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
#include "roccc_utils/annote_utils.h"
#include "roccc_utils/IR_utils.h"
#include "roccc_utils/symbol_utils.h"
#include "roccc_utils/type_utils.h"
#include "roccc_utils/warning_utils.h"
#include "scalar_replacement_pass.h"

using namespace std;

// Scalar replacement pass for loops with minimal data dependencies in the innermost loops.

class ScalarReplacementPass : public PipelinablePass {
public:
    ScalarReplacementPass(SuifEnv *pEnv) : PipelinablePass(pEnv, "ScalarReplacementPass") {}

    void do_procedure_definition(ProcedureDefinition* proc_def) override {
        OutputInformation("Scalar replacement pass begins");

        if (proc_def) {
            SuifEnv *the_env = proc_def->get_suif_env();

            auto load_scalar_temporaries = make_unique<suif_map<Expression*, VariableSymbol*>>();
            auto store_scalar_temporaries = make_unique<suif_map<Expression*, VariableSymbol*>>();

            process_load_expressions(proc_def, the_env, load_scalar_temporaries.get());
            process_store_statements(proc_def, the_env, store_scalar_temporaries.get());

            c_for_statement_walker walker(the_env, load_scalar_temporaries.get(), store_scalar_temporaries.get());
            proc_def->walk(walker);
        }

        OutputInformation("Scalar replacement pass ends");
    }

private:
    void process_load_expressions(ProcedureDefinition* proc_def, SuifEnv* the_env, suif_map<Expression*, VariableSymbol*>* load_scalars) {
        for (Iter<LoadExpression> iter = object_iterator<LoadExpression>(proc_def); iter.is_valid(); iter.next()) {
            LoadExpression* load_expr = &iter.current();
            if (is_a<ArrayReferenceExpression>(load_expr->get_source_address())) {
                auto ref = to<ArrayReferenceExpression>(load_expr->get_source_address());
                auto var = find_or_create_temp_var(the_env, proc_def, ref, load_scalars);
                load_scalars->enter_value(ref, var);
            }
        }
    }

    void process_store_statements(ProcedureDefinition* proc_def, SuifEnv* the_env, suif_map<Expression*, VariableSymbol*>* store_scalars) {
        for (Iter<StoreStatement> iter = object_iterator<StoreStatement>(proc_def); iter.is_valid(); iter.next()) {
            StoreStatement* store_stmt = &iter.current();
            if (is_a<ArrayReferenceExpression>(store_stmt->get_destination_address())) {
                auto ref = to<ArrayReferenceExpression>(store_stmt->get_destination_address());
                auto var = find_or_create_temp_var(the_env, proc_def, ref, store_scalars);
                store_scalars->enter_value(ref, var);
            }
        }
    }

    VariableSymbol* find_or_create_temp_var(SuifEnv* the_env, ProcedureDefinition* proc_def, ArrayReferenceExpression* ref, suif_map<Expression*, VariableSymbol*>* scalar_temporaries) {
        VariableSymbol* var = nullptr;
        auto iter = scalar_temporaries->find(ref);
        if (iter == scalar_temporaries->end()) {
            Type* t = get_base_type(ref->get_result_type());
            var = new_anonymous_variable(the_env, find_scope(proc_def->get_body()), retrieve_qualified_type(to<DataType>(t)));
            name_variable(var);
        } else {
            var = iter->second;
        }
        return var;
    }
};

class c_for_statement_walker : public SelectiveWalker {
public:
    c_for_statement_walker(SuifEnv *the_env, suif_map<Expression*, VariableSymbol*>* load_scalars,
                            suif_map<Expression*, VariableSymbol*>* store_scalars)
        : SelectiveWalker(the_env, CForStatement::get_class_name()),
          load_scalar_temporaries(load_scalars), store_scalar_temporaries(store_scalars) {}

    Walker::ApplyStatus operator () (SuifObject *x) override {
        SuifEnv *env = get_env();
        CForStatement *the_c_for = to<CForStatement>(x);
        Statement *body = the_c_for->get_body();

        if (body) {
            StatementList *stmt_list_body = nullptr;
            if (!is_a<StatementList>(body)) {
                the_c_for->set_body(nullptr);
                stmt_list_body = create_statement_list(env);
                stmt_list_body->append_statement(body);
                the_c_for->set_body(stmt_list_body);
            } else {
                stmt_list_body = to<StatementList>(body);
            }

            process_statements(env, stmt_list_body);

            add_replacement_statements(the_c_for, stmt_list_body);
        }

        return Walker::Continue;
    }

private:
    suif_map<Expression*, VariableSymbol*>* load_scalar_temporaries;
    suif_map<Expression*, VariableSymbol*>* store_scalar_temporaries;

    void process_statements(SuifEnv* env, StatementList* stmt_list_body) {
        load_expression_walker load_walker(env, stmt_list_body, load_scalar_temporaries);
        stmt_list_body->walk(load_walker);

        store_statement_walker store_walker(env, stmt_list_body, store_scalar_temporaries);
        stmt_list_body->walk(store_walker);
    }

    void add_replacement_statements(CForStatement* the_c_for, StatementList* stmt_list_body) {
        BrickAnnote *dp_input_vars = create_brick_annote(get_env(), "dp_input_vars");
        the_c_for->append_annote(dp_input_vars);
        BrickAnnote *dp_output_vars = create_brick_annote(get_env(), "dp_output_vars");
        the_c_for->append_annote(dp_output_vars);
        BrickAnnote *stores = create_brick_annote(get_env(), "stores");
        the_c_for->append_annote(stores);

        for (auto& store_brick : stores->get_brick_iterator()) {
            SuifObjectBrick* sob = to<SuifObjectBrick>(store_brick);
            StoreStatement* store_stmt = to<StoreStatement>(sob->get_object());
            stmt_list_body->append_statement(store_stmt);
        }

        remove_annotations(the_c_for);
    }

    void remove_annotations(CForStatement* the_c_for) {
        delete (the_c_for->remove_annote_by_name("dp_input_vars"));
        delete (the_c_for->remove_annote_by_name("dp_output_vars"));
        delete (the_c_for->remove_annote_by_name("stores"));
    }
};

class load_expression_walker : public SelectiveWalker {
public:
    load_expression_walker(SuifEnv* the_env, StatementList* loop_body, suif_map<Expression*, VariableSymbol*>* the_scalars)
        : SelectiveWalker(the_env, LoadExpression::get_class_name()), parent(loop_body), scalar_temporaries(the_scalars) {}

    Walker::ApplyStatus operator () (SuifObject *x) override {
        SuifEnv *the_env = get_env();
        LoadExpression *the_load_expr = to<LoadExpression>(x);
        
        if (is_a<ArrayReferenceExpression>(the_load_expr->get_source_address())) {
            auto ref = the_load_expr->get_source_address();
            auto var = find_scalar_variable(ref);
            if (var) {
                Expression* replacement = create_load_variable_expression(the_env, the_load_expr->get_result_type(), var);
                the_load_expr->get_parent()->replace(the_load_expr, replacement);

                CForStatement* enclosing_loop = get_enclosing_c_for_stmt(parent);
                BrickAnnote* dp_in = to<BrickAnnote>(enclosing_loop->lookup_annote_by_name("dp_input_vars"));
                if (!search(dp_in, var)) {
                    Statement* store_var_stmt = create_store_variable_statement(the_env, var, the_load_expr);
                    parent->insert_statement(0, store_var_stmt);
                    dp_in->append_brick(create_suif_object_brick(the_env, var));
                }
            }
        }

        return Walker::Continue;
    }

private:
    StatementList* parent;
    suif_map<Expression*, VariableSymbol*>* scalar_temporaries;

    VariableSymbol* find_scalar_variable(Expression* ref) {
        auto iter = scalar_temporaries->find(ref);
        if (iter == scalar_temporaries->end()) {
            cout << "Load error: Scalar variable not found." << endl;
            return nullptr;
        }
        return iter->second;
    }
};

class store_statement_walker : public SelectiveWalker {
public:
    store_statement_walker(SuifEnv* the_env, StatementList* loop_body, suif_map<Expression*, VariableSymbol*>* the_scalars)
        : SelectiveWalker(the_env, StoreStatement::get_class_name()), parent(loop_body), scalar_temporaries(the_scalars) {}

    Walker::ApplyStatus operator () (SuifObject *x) override {
        SuifEnv* the_env = get_env();
        StoreStatement* store_stmt = to<StoreStatement>(x);

        if (is_a<ArrayReferenceExpression>(store_stmt->get_destination_address())) {
            auto ref = store_stmt->get_destination_address();
            auto var = find_scalar_variable(ref);
            if (var) {
                Expression* expr = store_stmt->get_value();
                store_stmt->set_value(nullptr);
                LoadVariableExpression* symbol_expr = create_load_variable_expression(the_env, ref->get_result_type(), var);
                store_stmt->set_value(symbol_expr);

                StoreVariableStatement* store_var_stmt = create_store_variable_statement(the_env, var, expr);
                replace_statement(store_stmt, store_var_stmt);

                CForStatement* enclosing_loop = get_enclosing_c_for_stmt(parent);
                BrickAnnote* dp_out = to<BrickAnnote>(enclosing_loop->lookup_annote_by_name("dp_output_vars"));
                BrickAnnote* stores = to<BrickAnnote>(enclosing_loop->lookup_annote_by_name("stores"));

                if (!search(dp_out, var)) {
                    stores->append_brick(create_suif_object_brick(the_env, store_stmt));
                    dp_out->append_brick(create_suif_object_brick(the_env, var));
                }
            }
        }

        return Walker::Continue;
    }

private:
    StatementList* parent;
    suif_map<Expression*, VariableSymbol*>* scalar_temporaries;

    VariableSymbol* find_scalar_variable(Expression* ref) {
        auto iter = scalar_temporaries->find(ref);
        if (iter == scalar_temporaries->end()) {
            cout << "Store error: Scalar variable not found." << endl;
            return nullptr;
        }
        return iter->second;
    }
};

