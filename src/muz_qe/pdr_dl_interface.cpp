/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_dl.cpp

Abstract:

    SMT2 interface for the datalog PDR

Author:

    Krystof Hoder (t-khoder) 2011-9-22.

Revision History:

--*/

#include "dl_cmds.h"
#include "dl_context.h"
#include "dl_mk_coi_filter.h"
#include "dl_mk_interp_tail_simplifier.h"
#include "dl_mk_subsumption_checker.h"
#include "dl_mk_rule_inliner.h"
#include "dl_rule.h"
#include "dl_rule_transformer.h"
#include "dl_mk_extract_quantifiers.h"
#include "smt2parser.h"
#include "pdr_context.h"
#include "pdr_dl_interface.h"
#include "dl_rule_set.h"
#include "dl_mk_slice.h"
#include "dl_mk_unfold.h"
#include "dl_mk_coalesce.h"
#include "pdr_quantifiers.h"

using namespace pdr;

dl_interface::dl_interface(datalog::context& ctx) : 
    m_ctx(ctx), 
    m_pdr_rules(ctx), 
    m_old_rules(ctx),
    m_context(0),
    m_refs(ctx.get_manager()) {
    m_context = alloc(pdr::context, ctx.get_fparams(), ctx.get_params(), ctx.get_manager());
}


dl_interface::~dl_interface() {
    dealloc(m_context);
}


//
// Check if the new rules are weaker so that we can 
// re-use existing context.
// 
void dl_interface::check_reset() {
    datalog::rule_ref_vector const& new_rules = m_ctx.get_rules().get_rules();
    datalog::rule_ref_vector const& old_rules = m_old_rules.get_rules();  
    bool is_subsumed = !old_rules.empty();
    for (unsigned i = 0; is_subsumed && i < new_rules.size(); ++i) {
        is_subsumed = false;
        for (unsigned j = 0; !is_subsumed && j < old_rules.size(); ++j) {
            if (m_ctx.check_subsumes(*old_rules[j], *new_rules[i])) {
                is_subsumed = true;
            }
        }
        if (!is_subsumed) {
            TRACE("pdr", new_rules[i]->display(m_ctx, tout << "Fresh rule "););
            m_context->reset();
        }
    }
    m_old_rules.reset();
    m_old_rules.add_rules(new_rules.size(), new_rules.c_ptr());
}


lbool dl_interface::query(expr * query) {
    //we restore the initial state in the datalog context
    m_ctx.ensure_opened();
    m_pdr_rules.reset();
    m_refs.reset();
    m_pred2slice.reset();
    ast_manager& m =                      m_ctx.get_manager();
    datalog::rule_manager& rule_manager = m_ctx.get_rule_manager();
    datalog::rule_set        old_rules(m_ctx.get_rules());
    func_decl_ref            query_pred(m);
    datalog::rule_ref_vector query_rules(rule_manager);
    datalog::rule_ref        query_rule(rule_manager);
    rule_manager.mk_query(query, query_pred, query_rules, query_rule);
    m_ctx.add_rules(query_rules);
    expr_ref bg_assertion = m_ctx.get_background_assertion();

    check_reset();
   
    TRACE("pdr",
          if (!m.is_true(bg_assertion)) {
              tout << "axioms:\n";
              tout << mk_pp(bg_assertion, m) << "\n";
          }
          tout << "query: " << mk_pp(query, m) << "\n";
          tout << "rules:\n";
          m_ctx.display_rules(tout);
          );

    model_converter_ref mc = datalog::mk_skip_model_converter();
    proof_converter_ref pc;
    if (m_ctx.get_params().generate_proof_trace()) {
        pc = datalog::mk_skip_proof_converter();
    }
    m_ctx.set_output_predicate(query_pred);
    m_ctx.apply_default_transformation(mc, pc);

    if (m_ctx.get_params().slice()) {
        datalog::rule_transformer transformer(m_ctx);
        datalog::mk_slice* slice = alloc(datalog::mk_slice, m_ctx);
        transformer.register_plugin(slice);
        m_ctx.transform_rules(transformer, mc, pc);        
        query_pred = slice->get_predicate(query_pred.get());
        m_ctx.set_output_predicate(query_pred);
        
        // track sliced predicates.
        obj_map<func_decl, func_decl*> const& preds = slice->get_predicates();
        obj_map<func_decl, func_decl*>::iterator it  = preds.begin();
        obj_map<func_decl, func_decl*>::iterator end = preds.end();
        for (; it != end; ++it) {
            m_pred2slice.insert(it->m_key, it->m_value);
            m_refs.push_back(it->m_key);
            m_refs.push_back(it->m_value);
        }
    }

    if (m_ctx.get_params().unfold_rules() > 0) {
        unsigned num_unfolds = m_ctx.get_params().unfold_rules();
        datalog::rule_transformer transformer1(m_ctx), transformer2(m_ctx);
        if (m_ctx.get_params().coalesce_rules()) {
            transformer1.register_plugin(alloc(datalog::mk_coalesce, m_ctx));
            m_ctx.transform_rules(transformer1, mc, pc);
        }
        transformer2.register_plugin(alloc(datalog::mk_unfold, m_ctx));
        while (num_unfolds > 0) {
            m_ctx.transform_rules(transformer2, mc, pc);        
            --num_unfolds;
        }
    }
    // remove universal quantifiers from body.
    datalog::mk_extract_quantifiers* extract_quantifiers = alloc(datalog::mk_extract_quantifiers, m_ctx);
    datalog::rule_transformer extract_q_tr(m_ctx);
    extract_q_tr.register_plugin(extract_quantifiers);
    m_ctx.transform_rules(extract_q_tr, mc, pc);
    

    IF_VERBOSE(2, m_ctx.display_rules(verbose_stream()););
    m_pdr_rules.add_rules(m_ctx.get_rules());
    m_pdr_rules.close();
    m_ctx.reopen();
    m_ctx.replace_rules(old_rules);

    quantifier_model_checker quantifier_mc(*m_context, m, extract_quantifiers->quantifiers(), m_pdr_rules);
    
    datalog::scoped_restore_proof _sc(m); // update_rules may overwrite the proof mode.

    m_context->set_proof_converter(pc);
    m_context->set_model_converter(mc);
    m_context->set_query(query_pred);
    m_context->set_axioms(bg_assertion);
    m_context->update_rules(m_pdr_rules);
    
    if (m_pdr_rules.get_rules().empty()) {
        m_context->set_unsat();
        return l_false;
    }
        
    lbool result;
    while (true) {
        result = m_context->solve();
        if (result == l_true && extract_quantifiers->has_quantifiers()) {
            result = quantifier_mc.check();
            if (result != l_false) {
                return result;
            }
            // else continue
        }
        else {
            return result;
        }
    }

}

expr_ref dl_interface::get_cover_delta(int level, func_decl* pred_orig) {
    func_decl* pred = pred_orig;
    m_pred2slice.find(pred_orig, pred);
    SASSERT(pred);
    return m_context->get_cover_delta(level, pred_orig, pred);
}

void dl_interface::add_cover(int level, func_decl* pred, expr* property) {
    if (m_ctx.get_params().slice()) {
        throw default_exception("Covers are incompatible with slicing. Disable slicing before using covers");
    }
    m_context->add_cover(level, pred, property);
}

unsigned dl_interface::get_num_levels(func_decl* pred) {
    m_pred2slice.find(pred, pred);
    SASSERT(pred);
    return m_context->get_num_levels(pred);
}

void dl_interface::collect_statistics(statistics& st) const {
    m_context->collect_statistics(st);
}

void dl_interface::reset_statistics() {
    m_context->reset_statistics();
}

void dl_interface::display_certificate(std::ostream& out) const {
    m_context->display_certificate(out);
}

expr_ref dl_interface::get_answer() {
    return m_context->get_answer();
}

void dl_interface::cancel() {
    m_context->cancel();
}

void dl_interface::cleanup() {
    m_context->cleanup();
}

void dl_interface::updt_params() {
    dealloc(m_context);
    m_context = alloc(pdr::context, m_ctx.get_fparams(), m_ctx.get_params(), m_ctx.get_manager());
}

model_ref dl_interface::get_model() {
    return m_context->get_model();
}

proof_ref dl_interface::get_proof() {
    return m_context->get_proof();
}
