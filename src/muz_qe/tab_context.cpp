/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    tab_context.cpp

Abstract:

    Tabulation/subsumption/cyclic proof context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-01-15

Revision History:

--*/

#include "tab_context.h"
#include "trail.h"
#include "dl_rule_set.h"
#include "dl_context.h"
#include "dl_mk_rule_inliner.h"

namespace datalog {

    template<typename Ctx>
    struct restore_rule : trail<Ctx> {
        rule_ref_vector& m_rules;
        rule_ref&        m_rule;
        
        restore_rule(rule_ref_vector& rules, rule_ref& rule): 
            m_rules(rules),
            m_rule(rule) {
            m_rules.push_back(m_rule);
        }
        
        virtual void undo(Ctx & ctx) {
            m_rule = m_rules.back();
            m_rules.pop_back();
        }
    };

    enum tab_instruction {
        SELECT_RULE,
        SELECT_PREDICATE,
        BACKTRACK,
        NEXT_RULE,
        SATISFIABLE,
        UNSATISFIABLE,
        CANCEL
    };

    std::ostream& operator<<(std::ostream& out, tab_instruction i) {
        switch(i) {
        case SELECT_RULE: return out << "select-rule";
        case SELECT_PREDICATE: return out << "select-predicate";
        case BACKTRACK: return out << "backtrack";
        case NEXT_RULE: return out << "next-rule";
        case SATISFIABLE: return out << "sat";
        case UNSATISFIABLE: return out << "unsat";
        case CANCEL: return out << "cancel";
        }
        return out << "unmatched instruction";
    }

    class tab::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            unsigned m_num_unfold;
            unsigned m_num_no_unfold;
            unsigned m_num_subsume;
        };

        context&           m_ctx;
        ast_manager&       m;
        rule_manager&      rm;
        rule_unifier       m_unifier;
        rule_set           m_rules;
        trail_stack<imp>   m_trail;
        tab_instruction    m_instruction;
        rule_ref           m_query;
        rule_ref_vector    m_query_trail;
        unsigned           m_predicate_index;
        unsigned           m_rule_index;
        volatile bool      m_cancel;
        stats              m_stats;
    public:
        imp(context& ctx):
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_unifier(ctx),
            m_rules(ctx),
            m_trail(*this),
            m_instruction(SELECT_PREDICATE),
            m_query(rm),
            m_query_trail(rm),
            m_predicate_index(0),
            m_rule_index(0),
            m_cancel(false)
        {}

        ~imp() {}        

        lbool query(expr* query) {
            m_ctx.ensure_opened();
            m_rules.reset();
            m_rules.add_rules(m_ctx.get_rules());
            rule_ref_vector query_rules(rm);
            func_decl_ref query_pred(m);
            rm.mk_query(query, query_pred, query_rules, m_query);            
            return run();
        }
    
        void cancel() {
            m_cancel = true;
        }
        void cleanup() {
            m_cancel = false;
            m_trail.reset();
            m_query_trail.reset();
        }
        void reset_statistics() {
            m_stats.reset();
        }
        void collect_statistics(statistics& st) const {
            st.update("tab.num_unfold", m_stats.m_num_unfold);
            st.update("tab.num_unfold_fail", m_stats.m_num_no_unfold);
            st.update("tab.num_subsume", m_stats.m_num_subsume);
        }
        void display_certificate(std::ostream& out) const {
            // TBD
        }
        expr_ref get_answer() {
            // TBD
            return expr_ref(0, m);
        }
    private:
    
        void select_predicate() {
            unsigned num_predicates = m_query->get_uninterpreted_tail_size();
            if (num_predicates == 0) {
                m_instruction = UNSATISFIABLE;
                IF_VERBOSE(1, m_query->display(m_ctx, verbose_stream()); );
            }
            else {
                m_instruction = SELECT_RULE;
                m_predicate_index = 0; // TBD replace by better selection function.
                m_rule_index = 0;
            }
        }
        
        void apply_rule(rule const& r) {
            m_rule_index++;
            bool can_unify = m_unifier.unify_rules(*m_query, m_predicate_index, r);
            if (can_unify) {
                m_stats.m_num_unfold++;
                m_trail.push_scope();
                m_trail.push(value_trail<imp,unsigned>(m_rule_index));
                m_trail.push(value_trail<imp,unsigned>(m_predicate_index));
                rule_ref new_query(rm);
                m_unifier.apply(*m_query, m_predicate_index, r, new_query);
                m_trail.push(restore_rule<imp>(m_query_trail, m_query));
                m_query = new_query;
                TRACE("dl", m_query->display(m_ctx, tout););
                if (l_false == query_is_sat()) {
                    m_instruction = BACKTRACK;
                }
                else if (l_true == query_is_subsumed()) {
                    NOT_IMPLEMENTED_YET();
                }
                else {
                    m_instruction = SELECT_PREDICATE;
                }
            }
            else {
                m_stats.m_num_no_unfold++;
                m_instruction = SELECT_RULE;
            }
        }

        void select_rule() {
            func_decl* p = m_query->get_decl(m_predicate_index);
            rule_vector const& rules = m_rules.get_predicate_rules(p);
            if (rules.size() <= m_rule_index) {
                m_instruction = BACKTRACK;
            }
            else {
                apply_rule(*rules[m_rule_index]);
            }
        }

        void backtrack() {
            if (m_trail.get_num_scopes() == 0) {
                m_instruction = SATISFIABLE;
            }
            else {
                m_trail.pop_scope(1);
                m_instruction = SELECT_RULE;
            }
        }

        void next_rule() {
            SASSERT(m_trail.get_num_scopes() > 0);
            m_trail.pop_scope(1);
            m_instruction = SELECT_RULE;
        }

        lbool run() {
            m_instruction = SELECT_PREDICATE;
            while (true) {
                IF_VERBOSE(1, verbose_stream() << "run " << m_instruction << "\n";);                
                if (m_cancel) {
                    cleanup();
                    return l_undef;
                }
                switch(m_instruction) {
                case SELECT_PREDICATE: 
                    select_predicate(); 
                    break;
                case SELECT_RULE: 
                    select_rule(); 
                    break;
                case BACKTRACK:
                    backtrack();
                    break;
                case NEXT_RULE: // just use BACTRACK?
                    next_rule();
                    break;
                case SATISFIABLE: 
                    return l_false;
                case UNSATISFIABLE:
                    return l_true;
                case CANCEL:
                    m_cancel = false;
                    return l_undef;
                }
            }
        }    

        lbool query_is_sat() {
            expr_ref_vector fmls(m);

            return l_undef;
        }

        lbool query_is_subsumed() {
            return l_undef;
        }

    };

    tab::tab(context& ctx):
        m_imp(alloc(imp, ctx)) {        
    }
    tab::~tab() {
        dealloc(m_imp);
    }    
    lbool tab::query(expr* query) {
        return m_imp->query(query);
    }
    void tab::cancel() {
        m_imp->cancel();
    }
    void tab::cleanup() {
        m_imp->cleanup();
    }
    void tab::reset_statistics() {
        m_imp->reset_statistics();
    }
    void tab::collect_statistics(statistics& st) const {
        m_imp->collect_statistics(st);
    }
    void tab::display_certificate(std::ostream& out) const {
        m_imp->display_certificate(out);
    }
    expr_ref tab::get_answer() {
        return m_imp->get_answer();
    }

};
