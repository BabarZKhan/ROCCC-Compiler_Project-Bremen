
#include <cassert>

#include <basicnodes/basic.h>
#include <basicnodes/basic_factory.h>

#include <suifnodes/suif.h>
#include <suifnodes/suif_factory.h>

#include <cfenodes/cfe.h>
#include <cfenodes/cfe_factory.h>

#include "roccc_utils/roccc2.0_utils.h"
#include "roccc_utils/warning_utils.h"

#include "lutTransformationPass.h"

LUTTransformationPass::LUTTransformationPass(SuifEnv* pEnv)
    : PipelinablePass(pEnv, "LookupTableTransformation"),
      theEnv(pEnv),
      procDef(nullptr),
      LUTCounter(0) {}

LUTTransformationPass::~LUTTransformationPass() = default;

void LUTTransformationPass::do_procedure_definition(ProcedureDefinition* p)
{
    procDef = p;
    assert(procDef != nullptr);

    if (isLegacy(procDef)) {
        return;
    }

    OutputInformation("LUT Transformation pass begins");

    ReplaceLoads();
    ReplaceStores();

    OutputInformation("LUT Transformation pass ends");
}

void LUTTransformationPass::ReplaceLookup(LoadExpression* container, ArrayReferenceExpression* x)
{
    assert(procDef != nullptr);

    const LString procedureName = "ROCCCLUTLookup" + LString(LUTCounter);
    const LString procedureTypeName = "ROCCCLUTLookupType" + LString(LUTCounter);

    auto lookupType = create_c_procedure_type(
        theEnv,
        GetQualifiedTypeOfElement(x)->get_base_type(),
        false, true, 0, procedureTypeName);

    auto lookupSymbol = create_procedure_symbol(theEnv, lookupType, procedureName);

    procDef->get_symbol_table()->append_symbol_table_object(lookupType);
    procDef->get_symbol_table()->append_symbol_table_object(lookupSymbol);

    auto lookupSymAddr = create_symbol_address_expression(
        theEnv, GetQualifiedTypeOfElement(x)->get_base_type(), lookupSymbol);

    auto replacement = create_call_expression(
        theEnv, GetQualifiedTypeOfElement(x)->get_base_type(), lookupSymAddr);

    auto arraySym = GetArrayVariable(x);
    assert(arraySym != nullptr);

    auto loadArraySym = create_load_variable_expression(
        theEnv, arraySym->get_type()->get_base_type(), arraySym);

    lookupType->append_argument(arraySym->get_type());
    replacement->append_argument(loadArraySym);

    lookupType->append_argument(create_qualified_type(theEnv, x->get_index()->get_result_type()));
    replacement->append_argument(CreateIndex(x));

    lookupType->append_argument(GetQualifiedBaseInt(theEnv));
    replacement->append_argument(create_int_constant(theEnv, GetBaseInt(theEnv), IInteger(0)));

    container->get_parent()->replace(container, replacement);
    ++LUTCounter;
}

Expression* LUTTransformationPass::CreateIndex(ArrayReferenceExpression* x)
{
    int dimensionality = GetDimensionality(x);
    auto arraySym = GetArrayVariable(x);
    assert(arraySym != nullptr);

    const int elementSize = GetQualifiedTypeOfElement(x)->get_base_type()->get_bit_size().c_int();

    auto currentType = arraySym->get_type()->get_base_type();

    std::list<Expression*> indices;
    std::list<int> sizes;

    auto currentRef = x;
    for (int i = 0; i < dimensionality; ++i) {
        indices.push_front(currentRef->get_index());
        assert(currentRef != nullptr);

        currentRef = dynamic_cast<ArrayReferenceExpression*>(currentRef->get_base_array_address());
        assert(dynamic_cast<ArrayType*>(currentType) != nullptr);

        currentType = dynamic_cast<ArrayType*>(currentType)->get_element_type()->get_base_type();
        sizes.push_back(currentType->get_bit_size().c_int() / elementSize);
    }

    assert(!indices.empty() && !sizes.empty());

    auto indexIter = indices.begin();
    auto sizeIter = sizes.begin();

    auto finalExp = *indexIter;
    finalExp->set_parent(nullptr);
    ++indexIter;

    while (indexIter != indices.end()) {
        (*indexIter)->set_parent(nullptr);

        auto sizeExpr = create_int_constant(theEnv, GetBaseInt(theEnv), IInteger(*sizeIter));
        finalExp = create_binary_expression(theEnv, finalExp->get_result_type(), LString("multiply"), finalExp, sizeExpr);
        finalExp = create_binary_expression(theEnv, finalExp->get_result_type(), LString("add"), finalExp, *indexIter);

        ++indexIter;
        ++sizeIter;
    }

    return finalExp;
}

void LUTTransformationPass::ReplaceStore(StoreStatement* container, ArrayReferenceExpression* x)
{
    const LString procedureName = "ROCCCLUTStore" + LString(LUTCounter);
    const LString procedureTypeName = "ROCCCLUTStoreType" + LString(LUTCounter);

    auto storeType = create_c_procedure_type(
        theEnv,
        GetQualifiedTypeOfElement(x)->get_base_type(),
        false, true, 0, procedureTypeName);

    auto storeSymbol = create_procedure_symbol(theEnv, storeType, procedureName);

    procDef->get_symbol_table()->append_symbol_table_object(storeType);
    procDef->get_symbol_table()->append_symbol_table_object(storeSymbol);

    auto functionAddress = create_symbol_address_expression(
        theEnv, GetQualifiedTypeOfElement(x)->get_base_type(), storeSymbol);

    auto replacement = create_call_statement(theEnv, nullptr, functionAddress);

    auto arraySym = GetArrayVariable(x);
    assert(arraySym != nullptr);

    auto storeArraySym = create_load_variable_expression(
        theEnv, arraySym->get_type()->get_base_type(), arraySym);

    storeType->append_argument(arraySym->get_type());
    replacement->append_argument(storeArraySym);

    storeType->append_argument(create_qualified_type(theEnv, x->get_index()->get_result_type()));
    replacement->append_argument(CreateIndex(x));

    auto value = container->get_value();
    value->set_parent(nullptr);

    storeType->append_argument(create_qualified_type(theEnv, value->get_result_type()));
    replacement->append_argument(value);

    storeType->append_argument(GetQualifiedBaseInt(theEnv));
    replacement->append_argument(create_int_constant(theEnv, GetBaseInt(theEnv), IInteger(0)));

    container->get_parent()->replace(container, replacement);
    ++LUTCounter;
}

void LUTTransformationPass::ReplaceLoads()
{
    assert(procDef != nullptr);

    auto allLoads = collect_objects<LoadExpression>(procDef->get_body());
    for (auto* load : *allLoads) {
        auto currentRef = dynamic_cast<ArrayReferenceExpression*>(load->get_source_address());
        assert(currentRef != nullptr && "Generic pointers not supported!");

        if (IsLookupTable(GetArrayVariable(currentRef))) {
            ReplaceLookup(load, currentRef);
        }
    }
}

void LUTTransformationPass::ReplaceStores()
{
    assert(procDef != nullptr);

    auto allStores = collect_objects<StoreStatement>(procDef->get_body());
    for (auto* store : *allStores) {
        auto currentRef = dynamic_cast<ArrayReferenceExpression*>(store->get_destination_address());
        assert(currentRef != nullptr && "Generic pointers not supported!");

        if (IsLookupTable(GetArrayVariable(currentRef))) {
            ReplaceStore(store, currentRef);
        }
    }
}
