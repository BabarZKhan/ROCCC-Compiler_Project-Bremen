// The ROCCC Compiler Infrastructure
//  This file is distributed under the University of California Open Source
//  License.  See ROCCCLICENSE.TXT for details.   

#include "common/system_specific.h"
#include <common/suif_copyright.h>
#include "common/suif_map.h"

#include <iostream>
#include <iokernel/cast.h>
#include <iokernel/clone_stream.h>
#include <common/i_integer.h>
#include <basicnodes/basic_factory.h>
#include <suifnodes/suif.h>
#include <suifnodes/suif_factory.h>
#include <basicnodes/basic.h>
#include <basicnodes/basic_constants.h>
#include <suifkernel/suifkernel_messages.h>
#include <suifkernel/utilities.h> 
#include <suifkernel/group_walker.h> 
#include "transforms/procedure_walker_utilities.h"
#include <utils/expression_utils.h>
#include <utils/symbol_utils.h>
#include <utils/type_utils.h>
#include <utils/cloning_utils.h>
#include <cfenodes/cfe.h>
#include "roccc_utils/list_utils.h"
#include "roccc_utils/IR_utils.h"
#include "roccc_utils/symbol_utils.h"
#include "roccc_utils/data_dependence_utils.h"
#include "roccc_utils/warning_utils.h"
#include "roccc_extra_types/array_info.h"
#include "renaming_pass.h"

/**************************** Declarations ************************************/

class RPStoreStatementWalker1 : public SelectiveWalker {
public:
    RPStoreStatementWalker1(SuifEnv *env)
        : SelectiveWalker(env, StoreStatement::get_class_name()) {}
    Walker::ApplyStatus operator()(SuifObject *x) override;
};

class RPStoreStatementWalker2 : public SelectiveWalker {
public:
    RPStoreStatementWalker2(SuifEnv *env)
        : SelectiveWalker(env, StoreStatement::get_class_name()) {}
    Walker::ApplyStatus operator()(SuifObject *x) override;
};

std::list<String> *arrayNames;
std::list<String> *nonRenamableArrays;
suif_map<String, VariableSymbol *> *renameMap;

/**************************** Helper Functions ********************************/

bool isDependent(ArrayInfo *storeInfo, ArrayInfo *useInfo, BrickAnnote *cForInfo) {
    // Implement the logic to check dependency
    // ...
}

bool shouldRenameArray(const String &arrayName) {
    return !is_in_list(arrayName, nonRenamableArrays) &&
           !is_in_list(arrayName, arrayNames);
}

void addArrayToRenameList(const String &arrayName) {
    if (shouldRenameArray(arrayName)) {
        arrayNames->push_back(arrayName);
    }
}

/**************************** Implementations *********************************/

RenamingPass::RenamingPass(SuifEnv *env)
    : PipelinablePass(env, "RenamingPass") {}

void RenamingPass::do_procedure_definition(ProcedureDefinition *procDef) {
    OutputInformation("Scalar renaming pass begins");
    if (procDef) {
        arrayNames = new std::list<String>();
        nonRenamableArrays = new std::list<String>();
        renameMap = new suif_map<String, VariableSymbol *>();

        RPStoreStatementWalker1 walker1(get_suif_env());
        procDef->walk(walker1);

        if (!is_items_in_list(arrayNames, nonRenamableArrays)) {
            RPStoreStatementWalker2 walker2(get_suif_env());
            procDef->walk(walker2);
        }
    }
    OutputInformation("Scalar renaming pass ends");
}

Walker::ApplyStatus RPStoreStatementWalker1::operator()(SuifObject *x) {
    auto *storeStmt = to<StoreStatement>(x);

    auto *destRefExpr = to<ArrayReferenceExpression>(storeStmt->get_destination_address());
    auto *arrayRefInfoAnnote = to<BrickAnnote>(destRefExpr->lookup_annote_by_name("array_ref_info"));
    auto *arrayInfo = to<ArrayInfo>(to<SuifObjectBrick>(arrayRefInfoAnnote->get_brick(0))->get_object());

    String destArrayName = arrayInfo->get_array_symbol_name();

    if (is_in_list(destArrayName, nonRenamableArrays)) {
        return Walker::Continue;
    }

    addArrayToRenameList(destArrayName);

    auto *enclosingLoop = get_enclosing_c_for_stmt(storeStmt);
    auto *cForInfo = to<BrickAnnote>(enclosingLoop->lookup_annote_by_name("c_for_info"));

    auto *reachedUses = to<BrickAnnote>(storeStmt->lookup_annote_by_name("reached_uses"));
    for (auto iter = reachedUses->get_brick_iterator(); iter.is_valid(); iter.next()) {
        auto *useExpr = to<LoadExpression>(to<SuifObjectBrick>(iter.current())->get_object());
        auto *useRefExpr = to<ArrayReferenceExpression>(useExpr->get_source_address());
        auto *useArrayRefInfo = to<ArrayInfo>(to<SuifObjectBrick>(
            to<BrickAnnote>(useRefExpr->lookup_annote_by_name("array_ref_info"))->get_brick(0))->get_object());

        if (isDependent(arrayInfo, useArrayRefInfo, cForInfo)) {
            nonRenamableArrays->push_back(destArrayName);
            return Walker::Continue;
        }
    }
    return Walker::Continue;
}

Walker::ApplyStatus RPStoreStatementWalker2::operator()(SuifObject *x) {
    auto *storeStmt = to<StoreStatement>(x);

    auto *destRefExpr = to<ArrayReferenceExpression>(storeStmt->get_destination_address());
    auto *arrayRefInfo = to<BrickAnnote>(destRefExpr->lookup_annote_by_name("array_ref_info"));
    String destArrayName = to<StringBrick>(arrayRefInfo->get_brick(1))->get_value();

    if (is_in_list(destArrayName, nonRenamableArrays)) {
        return Walker::Continue;
    }

    auto *baseArrayAddr = destRefExpr;
    while (is_a<ArrayReferenceExpression>(baseArrayAddr)) {
        baseArrayAddr = to<ArrayReferenceExpression>(baseArrayAddr)->get_base_array_address();
    }

    auto *arraySymExpr = to<SymbolAddressExpression>(baseArrayAddr);
    auto *arraySym = to<VariableSymbol>(arraySymExpr->get_addressed_symbol());

    if (renameMap->find(arraySym->get_name()) == renameMap->end()) {
        auto *replacement = to<VariableSymbol>(arraySym->deep_clone());
        rename_symbol(replacement, "");
        auto *symTable = get_procedure_definition(storeStmt)->get_symbol_table();
        symTable->add_symbol(replacement);
        name_variable(replacement, arraySym->get_name());
        arraySymExpr->set_addressed_symbol(replacement);
    } else {
        arraySymExpr->set_addressed_symbol(renameMap->lookup(arraySym));
    }

    return Walker::Continue;
}

