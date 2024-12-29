#include <cassert>

#include "constantArrayPropagationPass.h"

#include "roccc_utils/roccc2.0_utils.h"
#include "roccc_utils/warning_utils.h"

#include <suifkernel/utilities.h>
#include <basicnodes/basic_factory.h>

// Constructor
ConstantArrayPropagationPass::ConstantArrayPropagationPass(SuifEnv *env)
    : PipelinablePass(env, "ConstantArrayPropagationPass"), theEnv(env), procDef(nullptr) {}

// Entry point for the pass
void ConstantArrayPropagationPass::do_procedure_definition(ProcedureDefinition *proc_def) {
    procDef = proc_def;
    assert(procDef != nullptr);

    OutputInformation("Constant Array Propagation Pass begins");

    CollectInitializations();  // Step 1: Collect constant array initializations
    ReplaceLoads();           // Step 2: Replace load expressions with initializations

    OutputInformation("Constant Array Propagation Pass ends");
}

// Collect constant array initializations
void ConstantArrayPropagationPass::CollectInitializations() {
    initializations.clear();

    DefinitionBlock *procDefBlock = procDef->get_definition_block();
    assert(procDefBlock != nullptr);

    for (auto *varDef : procDefBlock->get_variable_definitions()) {
        assert(varDef != nullptr);

        VariableSymbol *varSym = varDef->get_variable_symbol();
        ValueBlock *valBlock = varDef->get_initialization();
        assert(varSym != nullptr && valBlock != nullptr);

        if (ValidSymbol(varSym)) {
            initializations[varSym] = valBlock;
            varSym->append_annote(create_brick_annote(theEnv, "ConstPropArray"));
        }
    }
}

// Validate if the variable symbol corresponds to a constant array
bool ConstantArrayPropagationPass::ValidSymbol(VariableSymbol *var) {
    assert(var != nullptr);

    auto *qualType = var->get_type();
    while (auto *arrayType = dynamic_cast<ArrayType *>(qualType->get_base_type())) {
        qualType = arrayType->get_element_type();
    }
    assert(qualType != nullptr);

    return std::any_of(qualType->get_qualifications().begin(),
                       qualType->get_qualifications().end(),
                       [](const LString &qual) { return qual == "const"; });
}

// Replace load expressions with constant initializations
void ConstantArrayPropagationPass::ReplaceLoads() {
    assert(procDef != nullptr);

    auto allLoads = collect_objects<LoadExpression>(procDef->get_body());
    for (auto *load : *allLoads) {
        auto *source = load->get_source_address();
        auto *topRef = dynamic_cast<ArrayReferenceExpression *>(source);

        if (topRef) {
            VariableSymbol *var = GetArrayVariable(topRef);
            assert(var != nullptr);

            if (ValueBlock *topBlock = initializations[var]; topBlock) {
                ReplaceLoad(load, topRef, var, topBlock);
            }
        }
    }
    delete allLoads;
}

// Replace a single load expression with a constant value
void ConstantArrayPropagationPass::ReplaceLoad(LoadExpression *load,
                                               ArrayReferenceExpression *ref,
                                               VariableSymbol *var,
                                               ValueBlock *topBlock) {
    std::list<IntConstant *> dimensions;
    while (ref) {
        auto *index = dynamic_cast<IntConstant *>(ref->get_index());
        if (!index) {
            OutputWarning("Trying to access a constant array with a nonconstant index!");
            var->remove_annote_by_name("ConstPropArray");
            return;
        }
        dimensions.push_front(index);
        ref = dynamic_cast<ArrayReferenceExpression *>(ref->get_base_array_address());
    }

    auto *currentBlock = topBlock;
    for (auto *dim : dimensions) {
        auto *multiBlock = dynamic_cast<MultiValueBlock *>(currentBlock);
        assert(multiBlock != nullptr);

        currentBlock = multiBlock->lookup_sub_block(dim->get_value());
    }

    auto *finalBlock = dynamic_cast<ExpressionValueBlock *>(currentBlock);
    assert(finalBlock != nullptr && "Attempted to use an uninitialized constant value!");

    Expression *replacementValue = finalBlock->get_expression();
    ReplaceExpression(load, replacementValue);
}

// Replace an expression with the given constant value
void ConstantArrayPropagationPass::ReplaceExpression(LoadExpression *load, Expression *replacementValue) {
    if (auto *constInt = dynamic_cast<IntConstant *>(replacementValue)) {
        auto *replacement = create_int_constant(theEnv, constInt->get_result_type(), constInt->get_value());
        load->get_parent()->replace(load, replacement);
        delete load;
    } else if (auto *constFloat = dynamic_cast<FloatConstant *>(replacementValue)) {
        auto *replacement = create_float_constant(theEnv, constFloat->get_result_type(), constFloat->get_value());
        load->get_parent()->replace(load, replacement);
        delete load;
    } else {
        assert(false && "Unknown constant type encountered");
    }
}
