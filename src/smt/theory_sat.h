/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_sat.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-03.

Revision History:

--*/
#ifndef _theory_sat_H_
#define _theory_sat_H_

#include"smt_theory.h"
#include"trail.h"
#include"union_find.h"
#include"simplifier.h"
#include"bv_simplifier_plugin.h"
#include"arith_decl_plugin.h"
#include"arith_simplifier_plugin.h"
#include"numeral_factory.h"
#include "smt_context.h"
#include "smt_justification.h"
#include "smt_b_justification.h"
#include"ast.h"
//#include <map>
namespace smt {
    


    class theory_sat : public theory {
    	svector<literal> tmp_reason;
    public:


		    class sat_justification : public justification {
				theory_sat& outer;
				//Use this as a marker to identify justificaiton causes that come from the parent theory.
				 bool from_parent_theory;
		         literal   m_lit;
		         svector<literal> ants;
		    public:
		         sat_justification(svector<literal> & reason, theory_sat * theory):outer(*theory),from_parent_theory(false),m_lit(null_literal),ants(){

		         }
		         ~sat_justification(){

		         }
		         sat_justification(literal l, theory_sat * theory ):outer(*theory), m_lit(l),from_parent_theory(false),ants(){SASSERT(m_lit!=null_literal);}
		         sat_justification( theory_sat * theory ):outer(*theory), m_lit(null_literal),from_parent_theory(true),ants(){;}
		          proof* mk_proof(smt::conflict_resolution&){return NULL;};
		          bool fromParentTheory(){
		        	  return from_parent_theory;
		          }

		        virtual void get_antecedents(conflict_resolution & cr) {
		        	//ok, construct the clause for this implication now, and then use it to mark the antecedents
		        	if(from_parent_theory){
		        		return;//no causes at all
		        	}

		        	if(ants.size()){
						for(int i = 0;i< ants.size();i++){
							literal l = ants[i];

							if(l!=m_lit){
								SASSERT(outer.get_context().get_assignment(l)==l_false);
								cr.mark_literal(~l);
							}else{
								SASSERT(outer.get_context().get_assignment(l)==l_true);
							}
						}
						return;
		        	}
		    		outer.mk_reason_for(m_lit ,outer.tmp_reason);


		        	SASSERT(outer.tmp_reason[0].var()==m_lit.var());

		        	//Creating a clause here is optional, and its not clear how well it works in Z3. Also, should this be a learnt clause instead?
		        	outer.get_context().mk_clause(outer.tmp_reason.size(), outer.tmp_reason.c_ptr(),0,CLS_AUX_LEMMA);

					literal first = outer.tmp_reason[0];
					for(int i = 0;i<outer.tmp_reason.size();i++){
						literal l = outer.tmp_reason[i];
						//This is optional - we are storing the reason here in a vector, so that if it is analyzed again,we don't need to redo the analysis.
						//However, this is a sub-optimal solution. A better option would be to create a new learnt clause and make _that_ the reason for the assignment, replacing this justification altogether
						//However, Z3 doesn't changing reasons during conflict resolution.

						ants.push_back(l);

						if(l!=m_lit){
							SASSERT(outer.get_context().get_assignment(l)==l_false);
							cr.mark_literal(~l);
						}else{
							SASSERT(outer.get_context().get_assignment(l)==l_true);
						}
					}
		        }
		        virtual theory_id get_from_theory() const {
		                return outer.get_id();
		            }


		    };
public:

    	friend class sat_justification;

    	sat_justification * parent_just;
        ptr_addr_map<expr, expr*> exported_functions;

        //These two maps connect variable ids in the parent and child contexts

         svector<bool_var> parent_child_map;
         svector<bool_var> child_parent_map;

         enum saerchtype{FORCE_SUBSEARCH,SINGLE_SUBSEARCH, PARTIAL_SUBSEARCH,LONG_PARTIAL_SUBSEARCH};

         saerchtype m_subsearch;

         bool m_subsearch_abort_early;


         bool initial_propagation;
         int popto;
        context * child_ctx;
        vector<expr*> exported;

           protected:
               virtual bool internalize_atom(app * atom, bool gate_ctx);
               virtual bool internalize_term(app * term);
               virtual void new_eq_eh(theory_var v1, theory_var v2);
               virtual bool use_diseqs() const;
               virtual void new_diseq_eh(theory_var v1, theory_var v2);
               virtual void reset_eh();
               virtual void assign_eh(bool_var v, bool is_true);
               virtual final_check_status final_check_eh();
               virtual bool build_models() const {
                   return false;
               }
               virtual bool can_propagate() {
            	   //in principle, we should just return child_ctx->can_propagate();

            	   //But that will lead to a huge recursive call being made at every propagation step.
            	   //So instead, we ensure that there is propagation at the very first step (via initial_propagation), and afterward assume that if the current solver is up to date, so are the sub solvers

            	   if(!child_ctx)
            		   return false;

            	   bool canprop = !(!initial_propagation && !child_ctx->inconsistent() && popto<0 && child_ctx->get_scope_level() == get_context().get_scope_level() &&    child_ctx->parent_qhead==get_context().m_assigned_literals.size()   && child_ctx->m_qhead==child_ctx->m_assigned_literals.size());
            	   if(!canprop){
            		   dbg_sync();
            	   }
            	   return canprop;
               }
               void init_search_eh();
               virtual void propagate();
               virtual void push_scope_eh();
               virtual void pop_scope_eh(unsigned num_scopes);
               void mk_reason_for(literal l, svector<literal> & reason) ;
               bool sharedWithParent(bool_var child_var){
            	   return  child_parent_map.size()>child_var && child_parent_map[child_var] != null_bool_var;
               }

               bool sharedWithChild(bool_var parent_var){
            	   return  parent_child_map.size()>parent_var && parent_child_map[parent_var] != null_bool_var;
               }

               void dbg_reasons(){
#ifdef Z3_DEBUG_SMS
            	   for(int i = 0;i<get_context().m_assigned_literals.size();i++){
            		   literal l = get_context().m_assigned_literals[i];
            		   b_justification j = get_context().get_justification(l.var());
            		   if(j.get_kind()==b_justification::JUSTIFICATION){
            			   sat_justification * s = (sat_justification*) j.get_justification();
            			   if(!s->fromParentTheory()){
            				   if(l.var()<parent_child_map.size()){
            				   bool_var v = parent_child_map[l.var()];
            				   if(v!=null_bool_var){
								   literal cl = literal(v,l.sign());
								   SASSERT(child_ctx->get_assignment(cl)==l_true);
            				   }
            				   }
            			   }
            		   }
            	   }
#endif
               }

               //check that child context and its parent are properly syncronized
               void dbg_sync(bool exact=false){
#ifdef Z3_DEBUG_SMS
            	   dbg_reasons();
            	   if(get_context().inconsistent() || get_context().get_scope_level()==0 || child_ctx->get_scope_level()==0 || child_ctx->inconsistent())
            		   return;

            	   int clv = child_ctx->get_scope_level();
            	   int plv = get_context().get_scope_level();
            	   SASSERT(clv<=plv);
            	   if(exact){
            		   SASSERT(clv==plv);
            	   }
            	   for(int i = 0;i<get_context().m_assigned_literals.size() ;i++){
            		   literal plit = get_context().m_assigned_literals[i];
            		   int llv = get_context().get_assign_level(plit);
            		   if(llv>clv)
            			   break;

            		   bool_var v = plit.var();
            		   if(get_context().get_var_theory(v)==get_family_id()){
            			   literal child_lit = literal(parent_child_map[v],plit.sign());
            			   literal t = literal(child_parent_map[child_lit.var()],plit.sign());
            			   lbool cval = child_ctx->get_assignment(child_lit);
            			   SASSERT(t==plit);
            			   int clev = child_ctx->get_assign_level(child_lit);
            			   SASSERT(child_ctx->get_assignment(child_lit)==l_true);
            			   SASSERT(clev<=llv);
            		   }
            	   }

            	   for(int i = 0;i<child_ctx->m_assigned_literals.size() ;i++){
					   literal childlit = child_ctx->m_assigned_literals[i];

					   bool_var v = childlit.var();
					   if(child_parent_map.size()>v){
						   bool_var p = child_parent_map[v];
						   if(p!=null_bool_var){
							   literal plit = literal(p,childlit.sign());
							   int clev = child_ctx->get_assign_level(childlit);
							   int plev = get_context().get_assign_level(plit);
							   lbool val = get_context().get_assignment(plit);
							   SASSERT(clev<=plev);
							   if(exact){
								   SASSERT(clev==plev || plev==get_context().get_search_level());
							   }

							  //
							   if(exact){
								   SASSERT(get_context().get_assignment(plit)==l_true);
							   }
						   }


					   }

				   }
            	   dbg_reasons();
#endif
               }

                literal_vector  m_tmp_literal_vector;
           public:

                enum satmodsat_kind {
                    OP_EXPORT,
                };
                func_decl * m_sms;
               theory_sat(family_id id, context * p);
               theory_sat(context * p);

               int export_expr(expr* to_export, context* from){
            	   exported.push_back(to_export);
            	   return exported.size()-1;
               }

               bool isExported(expr* to_export, context* from){

            	   return exported_functions.contains(to_export);
               }

               void setExported(expr* exportedFunction, expr* to_export,context*from ){
            	   exported_functions.insert(to_export, exportedFunction);
               }

               expr* getExported(expr* to_export, context* from){
            	   return exported_functions.find(to_export);
               }

               virtual ~theory_sat() {}

               virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_sat,new_ctx); }

               virtual char const * get_name() const;

               void attach(context * child);
               void dettach(context * child);

           };
};

#endif /* _theory_sat_H_ */

