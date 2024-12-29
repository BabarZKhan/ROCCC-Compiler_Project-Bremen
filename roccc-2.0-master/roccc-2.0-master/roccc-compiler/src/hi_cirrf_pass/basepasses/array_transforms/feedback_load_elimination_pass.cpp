// The ROCCC Compiler Infrastructure
//  This file is distributed under the University of California Open Source
//  License.  See ROCCCLICENSE.TXT for details.

#include "common/system_specific.h"
#include <common/suif_copyright.h>

#include <iostream>
#include <iokernel/cast.h>
#include <iokernel/clone_stream.h>
#include <common/i_integer.h>
#include <basicnodes/basic_factory.h>
#include <suifnodes/suif.h>
#include <suifnodes/suif_factory.h>
#include <suifkernel/command_line_parsing.h>
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
#include <cfenodes/cfe_factory.h>
#include <typebuilder/type_builder.h>
#include "roccc_utils/loop_utils.h"
#include "roccc_utils/list_utils.h"
#include "roccc_utils/type_utils.h"
#include "roccc_utils/symbol_utils.h"
#include "roccc_utils/IR_utils.h"
#include "roccc_utils/data_dependence_utils.h"
#include "roccc_extra_types/array_info.h"
#include "feedback_load_elimination_pass.h"
#include "roccc_utils/warning_utils.h"

using namespace std;

// THIS PASS ONLY WORKS FOR THE INNERMOST LOOPS AND ELIMINATES THE FEEDBACK 
// LOAD/STORE PAIRS WITHIN THE LOOP BODY

// THIS PASS SHOULD ONLY BE EXECUTED RIGHT AFTER THE SCALAR_REPLACEMENT_PASS 
// THE PREPROCESSING_PASS and THE FLATTEN_STATEMENT_LIST_PASS

/**************************** Declarations ************************************/

class CForStatementWalker : public SelectiveWalker {
public:
    CForStatementWalker(SuifEnv *env)
        : SelectiveWalker(env, CForStatement::get_class_name()) {}
    Walker::ApplyStatus operator()(SuifObject *x) override;
};

class LoadVariableExpressionWalker : public SelectiveWalker {
public:
    LoadVariableExpressionWalker(SuifEnv *env, VariableSymbol *indexVar, Expression *lowerBoundExpr)
        : SelectiveWalker(env, LoadVariableExpression::get_class_name()),
          parentLoopIndexVar(indexVar),
          parentLoopLowerBoundExpr(lowerBoundExpr) {}

    Walker::ApplyStatus operator()(SuifObject *x) override;

private:
    VariableSymbol *parentLoopIndexVar;
    Expression *parentLoopLowerBoundExpr;
};

/**************************** Helper Functions ********************************/

static void handleFeedbackPair(
    SuifEnv *env,
    StoreStatement *storeStmt,
    ArrayInfo *destInfo,
    suif_map<LoadExpression *, ArrayInfo *> &loadExprArrayInfoMap,
    const String &loopCounterName,
    int loopStepSize,
    StatementList *beforeMemWrites,
    StatementList *afterMemReads,
    StatementList *loadInits,
    VariableSymbol *&feedbackVar,
    Type *varType,
    ProcedureDefinition *procDef) {

    for (auto iter = loadExprArrayInfoMap.begin(); iter != loadExprArrayInfoMap.end();) {
        ArrayInfo *sourceInfo = iter->second;
        if (destInfo->get_array_symbol_name() != sourceInfo->get_array_symbol_name()) {
            ++iter;
            continue;
        }

        if (is_a_feedback_pair(destInfo, sourceInfo, loopCounterName, loopStepSize)) {
            if (!feedbackVar) {
                feedbackVar = new_anonymous_variable(env, find_scope(procDef->get_body()),
                                                     retrieve_qualified_type(to<DataType>(varType)));
                name_variable(feedbackVar);

                auto feedbackVarSet = create_store_variable_statement(env, feedbackVar,
                    to<LoadVariableExpression>(deep_suif_clone(storeStmt->get_value())));
                beforeMemWrites->append_statement(feedbackVarSet);
            }

            LoadExpression *loadExpr = iter->first;
            StoreVariableStatement *loadParent = to<StoreVariableStatement>(get_expression_owner(loadExpr));

            auto feedbackVarGet = create_store_variable_statement(env, loadParent->get_destination(),
                create_load_variable_expression(env, to<DataType>(varType), feedbackVar));

            afterMemReads->append_statement(feedbackVarGet);

            iter = loadExprArrayInfoMap.erase(iter);
        } else {
            ++iter;
        }
    }
}

static void cleanUpStatements(StatementList *statementList, const list<Statement *> &statementsToRemove) {
    for (int i = 0; i < statementList->get_statement_count(); ) {
        if (is_in_list(statementList->get_statement(i), &statementsToRemove)) {
            statementList->remove_statement(i);
        } else {
            ++i;
        }
    }
}

/**************************** Implementations ********************************/

FeedbackLoadEliminationPass::FeedbackLoadEliminationPass(SuifEnv *env)
    : PipelinablePass(env, "FeedbackLoadEliminationPass") {}

void FeedbackLoadEliminationPass::do_procedure_definition(ProcedureDefinition *procDef) {
    OutputInformation("Feedback Load Elimination Pass begins");

    if (procDef) {
        CForStatementWalker walker(get_suif_env());
        procDef->walk(walker);
    }

    OutputInformation("Feedback Load Elimination Pass ends");
}

Walker::ApplyStatus CForStatementWalker::operator()(SuifObject *x) {
    SuifEnv *env = get_env();
    CForStatement *cForStmt = to<CForStatement>(x);

    Statement *body = cForStmt->get_body();
    if (!body || object_iterator<CForStatement>(body).is_valid()) {
        return Walker::Continue;
    }

    BrickAnnote *cForInfo = to<BrickAnnote>(cForStmt->lookup_annote_by_name("c_for_info"));
    String loopCounterName = (to<StringBrick>(cForInfo->get_brick(1)))->get_value();
    int loopStepSize = (to<IntegerBrick>(cForInfo->get_brick(4)))->get_value().c_int();

    ProcedureDefinition *procDef = get_procedure_definition(cForStmt);
    VariableSymbol *indexVar = get_c_for_basic_induction_variable(cForStmt);
    Expression *lowerBoundExpr = get_c_for_lower_bound_expr(cForStmt);

    BrickAnnote *ba;
    SuifObjectBrick *sob;

    ba = to<BrickAnnote>(cForStmt->lookup_annote_by_name("end_of_mem_reads"));
    sob = to<SuifObjectBrick>(ba->get_brick(0));
    MarkStatement *endOfMemReads = to<MarkStatement>(sob->get_object());

    ba = to<BrickAnnote>(cForStmt->lookup_annote_by_name("beg_of_mem_writes"));
    sob = to<SuifObjectBrick>(ba->get_brick(0));
    MarkStatement *begOfMemWrites = to<MarkStatement>(sob->get_object());

    auto storesList = collect_objects<StoreStatement>(body);
    if (storesList->empty()) {
        delete storesList;
        return Walker::Continue;
    }

    auto loadExprArrayInfoMap = new suif_map<LoadExpression *, ArrayInfo *>();
    for (auto *loadExpr : *collect_objects<LoadExpression>(body)) {
        if (is_a<ArrayReferenceExpression>(loadExpr->get_source_address())) {
            auto sourceAddrExpr = to<ArrayReferenceExpression>(loadExpr->get_source_address());
            auto sourceAddrInfoAnnote = to<BrickAnnote>(sourceAddrExpr->lookup_annote_by_name("array_ref_info"));
            auto sourceAddrInfo = to<ArrayInfo>(to<SuifObjectBrick>(sourceAddrInfoAnnote->get_brick(0))->get_object());
            loadExprArrayInfoMap->enter_value(loadExpr, sourceAddrInfo);
        }
    }

    auto beforeMemWrites = create_statement_list(env);
    auto afterMemReads = create_statement_list(env);
    auto loadInits = create_statement_list(env);
    auto statementsToRemove = new list<Statement *>();

    for (auto *storeStmt : *storesList) {
        if (is_a<ArrayReferenceExpression>(storeStmt->get_destination_address())) {
            auto destAddrExpr = to<ArrayReferenceExpression>(storeStmt->get_destination_address());
            auto destAddrInfoAnnote = to<BrickAnnote>(destAddrExpr->lookup_annote_by_name("array_ref_info"));
            auto destAddrInfo = to<ArrayInfo>(to<SuifObjectBrick>(destAddrInfoAnnote->get_brick(0))->get_object());
            auto varType = get_base_type(destAddrExpr->get_result_type());

            handleFeedbackPair(env, storeStmt, destAddrInfo, *loadExprArrayInfoMap, loopCounterName, loopStepSize,
                               beforeMemWrites, afterMemReads, loadInits, nullptr, varType, procDef);
        }
    }

    cleanUpStatements(to<StatementList>(body), *statementsToRemove);

    LoadVariableExpressionWalker walker(env, indexVar, lowerBoundExpr);
    loadInits->walk(walker);

    insert_statement_before(begOfMemWrites, beforeMemWrites);
    insert_statement_after(endOfMemReads, afterMemReads);
    insert_statement_before(cForStmt, loadInits);

    delete storesList;
    delete loadExprArrayInfoMap;
    delete statementsToRemove;

    return Walker::Continue;
}

Walker::ApplyStatus LoadVariableExpressionWalker::operator()(SuifObject *x) {
    LoadVariableExpression *loadVarExpr = to<LoadVariableExpression>(x);

    if (loadVarExpr->get_source() == parentLoopIndexVar) {
        loadVarExpr->get_parent()->replace(loadVarExpr,
                                           to<Expression>(deep_suif_clone(parentLoopLowerBoundExpr)));
    }
    return Walker::Continue;
}

