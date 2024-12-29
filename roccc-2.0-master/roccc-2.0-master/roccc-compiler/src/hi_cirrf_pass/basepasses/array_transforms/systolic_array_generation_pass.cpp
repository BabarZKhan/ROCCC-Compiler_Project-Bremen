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
#include "roccc_utils/annote_utils.h"
#include "roccc_utils/loop_utils.h"
#include "roccc_utils/list_utils.h"
#include "roccc_utils/type_utils.h"
#include "roccc_utils/symbol_utils.h"
#include "roccc_utils/IR_utils.h"
#include "roccc_utils/data_dependence_utils.h"
#include "roccc_utils/warning_utils.h"
#include "roccc_extra_types/array_info.h"
#include "systolic_array_generation_pass.h"

using namespace std;

// THIS PASS ONLY WORKS FOR THE INNERMOST LOOPS AND ELIMINATES THE FEEDBACK 
// LOAD/STORE PAIRS WITHIN THE LOOP BODY

// THIS PASS SHOULD ONLY BE EXECUTED RIGHT AFTER THE SCALAR_REPLACEMENT_PASS 
// THE PREPROCESSING_PASS AND THE FLATTEN_STATEMENT_LIST_PASS

/**************************** Declarations ************************************/

class sa_c_for_statement_walker : public SelectiveWalker {
public:
    sa_c_for_statement_walker(SuifEnv *the_env)
        : SelectiveWalker(the_env, CForStatement::get_class_name()) {}
    Walker::ApplyStatus operator()(SuifObject *x);
};

class sa_load_variable_expression_walker : public SelectiveWalker {
public:
    sa_load_variable_expression_walker(SuifEnv *the_env, VariableSymbol *iv, Expression *lbe)
        : SelectiveWalker(the_env, LoadVariableExpression::get_class_name()), parent_loop_index_var(iv), 
        parent_loop_lower_bound_expr(lbe) {}
    Walker::ApplyStatus operator()(SuifObject *x);
private:
    VariableSymbol* parent_loop_index_var;
    Expression* parent_loop_lower_bound_expr;
};

class sa_store_statement_walker : public SelectiveWalker {
public:
    sa_store_statement_walker(SuifEnv *the_env)
        : SelectiveWalker(the_env, StoreStatement::get_class_name()) {}
    Walker::ApplyStatus operator()(SuifObject *x);
};

class sa_load_expression_walker : public SelectiveWalker {
public:
    sa_load_expression_walker(SuifEnv *the_env)
        : SelectiveWalker(the_env, LoadExpression::get_class_name()) {}
    Walker::ApplyStatus operator()(SuifObject *x);
};

suif_map<VariableSymbol*, VariableSymbol*>* sa_load_rename_map;
suif_map<VariableSymbol*, VariableSymbol*>* sa_store_rename_map;

void save_systolic_array_result(CForStatement *c_for_stmt);
void initialize_systolic_array_w_saved_results(CForStatement *c_for_stmt);
void move_begin_hw_end_hw_marks(CForStatement *c_for_stmt);

/**************************** Implementations ************************************/

SystolicArrayGenerationPass::SystolicArrayGenerationPass(SuifEnv *pEnv) 
    : PipelinablePass(pEnv, "SystolicArrayGenerationPass") {}

void SystolicArrayGenerationPass::initialize() {
    PipelinablePass::initialize();
    _command_line->set_description("Generates a systolic array");
    OptionInt *option_is_internal_array_values_saved = new OptionInt("Is Systolic Array Internal Values Saved", &is_internal_array_values_saved);
    OptionList *systolic_array_generation_pass_arguments = new OptionList();
    systolic_array_generation_pass_arguments->add(option_is_internal_array_values_saved);
    _command_line->add(systolic_array_generation_pass_arguments);
}

void SystolicArrayGenerationPass::do_procedure_definition(ProcedureDefinition* proc_def) {
    OutputInformation("Systolic array generation pass begins");
    if (proc_def) {
        sa_c_for_statement_walker walker(get_suif_env());
        proc_def->walk(walker);
    }
    OutputInformation("Systolic array generation pass ends");
}

int get_systolic_array_cell_id(ArrayInfo* store_ref_info, BrickAnnote *loop_nest_info) {
    String loop_counter_name = (to<StringBrick>(loop_nest_info->get_brick(5)))->get_value();
    int loop_step_size = (to<IntegerBrick>(loop_nest_info->get_brick(8)))->get_value().c_int();

    int bc = 0;
    while(bc < store_ref_info->get_dimension()) {
        String index_var_name = store_ref_info->get_index_var_name(bc);
        if(index_var_name == loop_counter_name)
            return store_ref_info->get_c(bc) % loop_step_size;
        bc++;
    }

    return 0;
}

Walker::ApplyStatus sa_c_for_statement_walker::operator()(SuifObject *x) {
    SuifEnv *env = get_env();
    CForStatement *c_for_stmt = to<CForStatement>(x);

    Statement *body = c_for_stmt->get_body();

    if (object_iterator<CForStatement>(body).is_valid())
        return Walker::Continue;

    BrickAnnote* c_for_info = to<BrickAnnote>(c_for_stmt->lookup_annote_by_name("c_for_info"));
    String c_for_loop_counter_name = (to<StringBrick>(c_for_info->get_brick(1)))->get_value();
    int c_for_loop_step_size = (to<IntegerBrick>(c_for_info->get_brick(4)))->get_value().c_int();

    sa_load_rename_map = new suif_map<VariableSymbol*, VariableSymbol*>;
    sa_store_rename_map = new suif_map<VariableSymbol*, VariableSymbol*>;

    if (body) {
        list<StoreStatement*>* stores_list = collect_objects<StoreStatement>(body);

        if (stores_list->empty()) {
            delete stores_list;
            return Walker::Continue;
        }

        ProcedureDefinition* proc_def = get_procedure_definition(c_for_stmt);
        VariableSymbol *c_for_stmt_index_var = get_c_for_basic_induction_variable(c_for_stmt);
        Expression *c_for_stmt_lower_bound_expr = get_c_for_lower_bound_expr(c_for_stmt);

        BrickAnnote *ba = to<BrickAnnote>(c_for_stmt->lookup_annote_by_name("end_of_mem_reads"));
        SuifObjectBrick *sob = to<SuifObjectBrick>(ba->get_brick(0));
        MarkStatement *end_of_mem_reads = to<MarkStatement>(sob->get_object());

        ba = to<BrickAnnote>(c_for_stmt->lookup_annote_by_name("beg_of_mem_writes"));
        sob = to<SuifObjectBrick>(ba->get_brick(0));
        MarkStatement *beg_of_mem_writes = to<MarkStatement>(sob->get_object());

        list<VariableSymbol*>* array_names_in_load_exprs = collect_array_name_symbols_used_in_loads(body);
        suif_map<LoadExpression*, ArrayInfo*>* load_expr_array_info_map = new suif_map<LoadExpression*, ArrayInfo*>;

        list<LoadExpression*>* loads_list = collect_objects<LoadExpression>(body);
        for (LoadExpression* load_expr : *loads_list) {
            if (!is_a<ArrayReferenceExpression>(load_expr->get_source_address())) 
                continue;

            ArrayReferenceExpression *source_address_expr = to<ArrayReferenceExpression>(load_expr->get_source_address());
            BrickAnnote *source_address_info_annote = to<BrickAnnote>(source_address_expr->lookup_annote_by_name("array_ref_info"));
            sob = to<SuifObjectBrick>(source_address_info_annote->get_brick(0));
            ArrayInfo *source_address_info = (ArrayInfo*)(sob->get_object());

            load_expr_array_info_map->enter_value(load_expr, source_address_info);
        }
        delete loads_list;

        StatementList* before_beg_of_mem_writes = create_statement_list(env);
        StatementList* after_end_of_mem_reads = create_statement_list(env);
        StatementList* load_inits = create_statement_list(env);
        list<Statement*>* to_be_removed = new list<Statement*>;

        for (auto iter = stores_list->begin(); iter != stores_list->end();) {
            StoreStatement *store_stmt = *iter;
            if (!is_a<ArrayReferenceExpression>(store_stmt->get_destination_address())) 
                continue;

            ArrayReferenceExpression *destination_address_expr = to<ArrayReferenceExpression>(store_stmt->get_destination_address());
            BrickAnnote *destination_address_info_annote = to<BrickAnnote>(destination_address_expr->lookup_annote_by_name("array_ref_info"));
            sob = to<SuifObjectBrick>(destination_address_info_annote->get_brick(0));
            ArrayInfo *destination_address_info = (ArrayInfo*)(sob->get_object());

            VariableSymbol *array_sym = get_array_name_symbol(destination_address_expr);
            Type *t = get_base_type(destination_address_expr->get_result_type());
            VariableSymbol *feedback_var = NULL;
            bool is_store_safe_to_remove = true;

            for (auto iter2 = load_expr_array_info_map->begin(); iter2 != load_expr_array_info_map->end();) {
                ArrayInfo *source_address_info = (*iter2).second;

                if (destination_address_info->get_array_symbol_name() != source_address_info->get_array_symbol_name()) {
                    ++iter2;
                    continue;
                }

                if (is_a_feedback_pair(destination_address_info, source_address_info, c_for_loop_counter_name, c_for_loop_step_size)) {
                    if (sa_load_rename_map->find(array_sym) == sa_load_rename_map->end())
                        sa_load_rename_map->enter_value(array_sym, NULL);

                    if (!feedback_var) {
                        feedback_var = new_anonymous_variable(env, find_scope(proc_def->get_body()), retrieve_qualified_type(to<DataType>(t)));
                        name_variable(feedback_var, String("feedback_" + array_sym->get_name()));
                    }

                    VariableSymbol *renamed_feedback_var = NULL;
                    if (sa_load_rename_map->find(feedback_var) == sa_load_rename_map->end()) 
                        sa_load_rename_map->enter_value(feedback_var, renamed_feedback_var);

                    iter = stores_list->erase(iter);
                    continue;
                }
            }

            ++iter;
        }
        delete stores_list;
    }

    OutputInformation("Systolic array generation pass ends");
    return Walker::Continue;
}

void initialize_systolic_array_w_saved_results(CForStatement *c_for_stmt){

        SuifEnv *env = c_for_stmt->get_suif_env();
        VariableSymbol *innermost_loop_counter = get_c_for_basic_induction_variable(c_for_stmt);
        StatementList *body = create_statement_list(env);

        for(suif_map<VariableSymbol*, VariableSymbol*>::iterator iter = sa_load_rename_map->begin();
            iter != sa_load_rename_map->end(); iter++){

	    if((*iter).second == NULL) continue;

            VariableSymbol *source_array_sym = (*iter).first;
            DataType *array_expr_type = source_array_sym->get_type()->get_base_type();
            Expression *source_address_expr = create_symbol_address_expression(env,
                                                                array_expr_type,
                                                                source_array_sym);

            array_expr_type = (to<ArrayType>(array_expr_type))->get_element_type()->get_base_type();
            source_address_expr = create_array_reference_expression(env,
                                        array_expr_type, source_address_expr,
                                        create_load_variable_expression(env,
                                                innermost_loop_counter->get_type()->get_base_type(),
                                                innermost_loop_counter));
	    
	    CForStatement *parent_c_for_stmt = get_enclosing_c_for_stmt(c_for_stmt);
	    VariableSymbol *outer_loop_counter = get_c_for_basic_induction_variable(parent_c_for_stmt);
            array_expr_type = (to<ArrayType>(array_expr_type))->get_element_type()->get_base_type();
            source_address_expr = create_array_reference_expression(env,
                                        array_expr_type, source_address_expr,
				  	create_binary_expression(env, outer_loop_counter->get_type()->get_base_type(),
						String("subtract"),
						create_load_variable_expression(env,
                                                		outer_loop_counter->get_type()->get_base_type(),
                                                		outer_loop_counter),
					create_int_constant(env, IInteger(1))));

            VariableSymbol *destination_array_sym = (*iter).second;
            array_expr_type = destination_array_sym->get_type()->get_base_type();
            Expression *destination_address_expr = create_symbol_address_expression(env,
                                                                array_expr_type,
                                                                destination_array_sym);

            array_expr_type = (to<ArrayType>(array_expr_type))->get_element_type()->get_base_type();
            destination_address_expr = create_array_reference_expression(env,
                                                                array_expr_type, destination_address_expr,
                                                                create_load_variable_expression(env,
                                                                        innermost_loop_counter->get_type()->get_base_type(),
                                                                        innermost_loop_counter));

            StoreStatement *store_stmt = create_store_statement(env, source_address_expr, destination_address_expr);
            body->append_statement(store_stmt);
        }

        CForStatement *new_c_for_stmt = create_c_for_statement(env,
                                                   to<Statement>(deep_suif_clone(c_for_stmt->get_before())),
                                                   to<Expression>(deep_suif_clone(c_for_stmt->get_test())),
                                                   to<Statement>(deep_suif_clone(c_for_stmt->get_step())),
                                                   body);
	set_c_for_lower_bound(new_c_for_stmt, 0);
	
        insert_statement_before(c_for_stmt, new_c_for_stmt);
}

void save_systolic_array_result(CForStatement *c_for_stmt){

        SuifEnv *env = c_for_stmt->get_suif_env();
        VariableSymbol *innermost_loop_counter = get_c_for_basic_induction_variable(c_for_stmt);
        StatementList *body = create_statement_list(env);

        for(suif_map<VariableSymbol*, VariableSymbol*>::iterator iter = sa_store_rename_map->begin();
            iter != sa_store_rename_map->end(); iter++){

	    if((*iter).second == NULL) continue;

            VariableSymbol *source_array_sym = (*iter).second;
            DataType *array_expr_type = source_array_sym->get_type()->get_base_type();
            Expression *source_address_expr = create_symbol_address_expression(env,
                                                                array_expr_type,
                                                                source_array_sym);

            array_expr_type = (to<ArrayType>(array_expr_type))->get_element_type()->get_base_type();
            source_address_expr = create_array_reference_expression(env,
                                                                array_expr_type, source_address_expr,
                                                                create_load_variable_expression(env,
                                                                        innermost_loop_counter->get_type()->get_base_type(),
                                                                        innermost_loop_counter));

            VariableSymbol *destination_array_sym = (*iter).first;
            array_expr_type = destination_array_sym->get_type()->get_base_type();
            Expression *destination_address_expr = create_symbol_address_expression(env,
                                                                array_expr_type,
                                                                destination_array_sym);

            array_expr_type = (to<ArrayType>(array_expr_type))->get_element_type()->get_base_type();
            destination_address_expr = create_array_reference_expression(env,
                                        array_expr_type, destination_address_expr,
                                        create_load_variable_expression(env,
                                                innermost_loop_counter->get_type()->get_base_type(),
                                                innermost_loop_counter));
	    
	    CForStatement *parent_c_for_stmt = get_enclosing_c_for_stmt(c_for_stmt);
	    VariableSymbol *outer_loop_counter = get_c_for_basic_induction_variable(parent_c_for_stmt);
	    int parent_c_for_stmt_step_count = get_c_for_step(parent_c_for_stmt) - 1;
            array_expr_type = (to<ArrayType>(array_expr_type))->get_element_type()->get_base_type();
            destination_address_expr = create_array_reference_expression(env,
                                        array_expr_type, destination_address_expr,
				  	create_binary_expression(env, outer_loop_counter->get_type()->get_base_type(),
						String("add"),
						create_load_variable_expression(env,
                                                		outer_loop_counter->get_type()->get_base_type(),
                                                		outer_loop_counter),
					create_int_constant(env, IInteger(parent_c_for_stmt_step_count))));

            StoreStatement *store_stmt = create_store_statement(env, source_address_expr, destination_address_expr);
            body->append_statement(store_stmt);
        }

        CForStatement *new_c_for_stmt = create_c_for_statement(env,
                                                   to<Statement>(deep_suif_clone(c_for_stmt->get_before())),
                                                   to<Expression>(deep_suif_clone(c_for_stmt->get_test())),
                                                   to<Statement>(deep_suif_clone(c_for_stmt->get_step())),
                                                   body);

        insert_statement_after(c_for_stmt, new_c_for_stmt);
}

void move_begin_hw_end_hw_marks(CForStatement *c_for_stmt){

        SuifEnv *env = c_for_stmt->get_suif_env();
        ProcedureDefinition *proc_def = get_procedure_definition(c_for_stmt);

        BrickAnnote *begin_hw_mark_annote = to<BrickAnnote>(proc_def->lookup_annote_by_name("begin_hw"));
        BrickAnnote *end_hw_mark_annote = to<BrickAnnote>(proc_def->lookup_annote_by_name("end_hw"));

        SuifObjectBrick *sob = to<SuifObjectBrick>(begin_hw_mark_annote->get_brick(0));
        MarkStatement *begin_hw_mark_stmt = to<MarkStatement>(sob->get_object());

        sob = to<SuifObjectBrick>(end_hw_mark_annote->get_brick(0));
        MarkStatement *end_hw_mark_stmt = to<MarkStatement>(sob->get_object());

        remove_statement(begin_hw_mark_stmt);
        remove_statement(end_hw_mark_stmt);

        insert_statement_before(c_for_stmt, begin_hw_mark_stmt);
        insert_statement_after(c_for_stmt, end_hw_mark_stmt);
}

