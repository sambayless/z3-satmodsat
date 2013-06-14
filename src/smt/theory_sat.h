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
#include"theory_sat_params.h"
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
		         clause * clsreason;
		         int antecedents_size;
		         literal * antecedents;

		    public:
		         sat_justification(svector<literal> & reason, theory_sat * theory):outer(*theory),from_parent_theory(false),m_lit(null_literal),clsreason(0){
		        	 antecedents = new literal[reason.size()];
		        	 antecedents_size = reason.size();
		        	 for(int i = 0;i<reason.size();i++)
		        		 antecedents[i]=reason[i];
		         }
		         ~sat_justification(){
		        	 if(antecedents){
		        		 delete []antecedents;
		        	 }
		         }
		         sat_justification(literal l, theory_sat * theory ):outer(*theory), m_lit(l),clsreason(0),from_parent_theory(false),antecedents_size(0),antecedents(0){SASSERT(m_lit!=null_literal);}
		         sat_justification( theory_sat * theory ):outer(*theory), m_lit(null_literal),clsreason(0),from_parent_theory(true),antecedents_size(0),antecedents(0){;}
		          proof* mk_proof(smt::conflict_resolution&){return NULL;};
		          bool fromParentTheory(){
		        	  return from_parent_theory;
		          }
		          bool hasAntecedents(){
		        	  return antecedents_size;
		          }
		        virtual void get_antecedents(conflict_resolution & cr) {
		        	//ok, construct the clause for this implication now, and then use it to mark the antecedents
		        	if(from_parent_theory){
		        		return;//no causes at all
		        	}

		        	/*if(!antecedents){

		        		outer.mk_reason_for(m_lit ,outer.tmp_reason);

						//Now, construct this clause so we don't need to do this again.
						 //ctx.assign(l, ctx.mk_justification(theory_propagation_justification(get_id(), ctx.get_region(), antecedents.size(), antecedents.c_ptr(), l)));
						SASSERT(outer.tmp_reason.size()>0);
						//if(outer.tmp_reason.size()>2){
							//I would like to create a clause at this point, but it seems Z3 doesn't support doing this.
							//So, what I will do instead is store the antecedents in a vector, and add that vector to a list to be processed at some point in the future when it is indeed safe to add clauses to Z3.
							//clsreason = outer.get_context().mk_clause(outer.tmp_reason.size(), outer.tmp_reason.c_ptr(),0,CLS_AUX_LEMMA);
						//}

						//clause * c = outer.child_ctx->mk_clause(outer.tmp_reason.size(), outer.tmp_reason.c_ptr(),b_justification::mk_axiom(), CLS_LEARNED);

						//update the reason for this assignment in the parent context
					//	outer.m_context->get_bdata(m_lit.var()).m_justification=outer.m_context->mk_justification(theory_propagation_justification(outer.get_id(), outer.m_context->get_region(), c->size(), c, m_lit)));
						SASSERT(outer.tmp_reason[0].var()==m_lit.var());
						literal first = outer.tmp_reason[0];
						for(int i =  outer.get_context().get_assignment(first)==l_true ? 1:0;i<outer.tmp_reason.size();i++){
							literal l = outer.tmp_reason[i];
							SASSERT(outer.get_context().get_assignment(l)==l_false);
							cr.mark_literal(~l);
						}

						antecedents = new literal[outer.tmp_reason.size()];
						for(int i = 0;i<outer.tmp_reason.size();i++)
							antecedents[i]=outer.tmp_reason[i];
						antecedents_size= outer.tmp_reason.size();

						outer.to_create.push_back(std::pair(antecedents_size, antecedents));

		        	}*/

		        	if(antecedents){
		        		literal first = antecedents[0];

						for(int i = outer.get_context().get_assignment(first)==l_true ? 1:0 ;i<antecedents_size;i++){
							literal l =antecedents[i];

							SASSERT(outer.get_context().get_assignment(l)==l_false);
							cr.mark_literal(~l);
						}
		        		return;
		        	}

		    		outer.mk_reason_for(m_lit ,outer.tmp_reason);

					//Now, construct this clause so we don't need to do this again.
					 //ctx.assign(l, ctx.mk_justification(theory_propagation_justification(get_id(), ctx.get_region(), antecedents.size(), antecedents.c_ptr(), l)));
					SASSERT(outer.tmp_reason.size()>0);
					if(outer.tmp_reason.size()>2){
						//I would like to create a clause at this point, but it seems Z3 doesn't support doing this.
						//So, what I will do instead is store the antecedents in a vector, and add that vector to a list to be processed at some point in the future when it is indeed safe to add clauses to Z3.
					//	clsreason = outer.get_context().mk_clause(outer.tmp_reason.size(), outer.tmp_reason.c_ptr(),0,CLS_LEARNED);
					}


		        	if(clsreason){
		        		SASSERT(!clsreason->deleted());
						for(int i = 0;i<clsreason->get_num_literals();i++){
							literal l = clsreason->get_literal(i);
							SASSERT(l!=null_literal);
							if(l.var()!=m_lit.var()){
								SASSERT(outer.get_context().get_assignment(l)==l_false);
								cr.mark_literal(~l);
							}
						}
		        	}
		        	SASSERT(outer.tmp_reason[0].var()==m_lit.var());
					literal first = outer.tmp_reason[0];
					for(int i = 0;i<outer.tmp_reason.size();i++){
						literal l = outer.tmp_reason[i];
						if(l!=m_lit){
							SASSERT(outer.get_context().get_assignment(l)==l_false);
							cr.mark_literal(~l);
						}else{
							SASSERT(outer.get_context().get_assignment(l)==l_true);
						}
					}

		        	//delete(this);

		        }
		        virtual theory_id get_from_theory() const {
		                return outer.get_id();
		            }


		    };
public:

       // typedef trail_stack<theory_sat> th_trail_stack;

    	friend class sat_justification;

    	sat_justification * parent_just;
        ptr_addr_map<expr, expr*> exported_functions;

        //typedef svector<theory_var> vars;
        int parent_qhead;
        int child_qhead;

        //These two maps connect variable ids in the parent and child contexts
         svector<bool_var> parent_child_map;
         svector<bool_var> child_parent_map;
         svector<std::pair<int,literal*> > to_create;

         char * m_name;
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
            	   int qh = child_ctx&& child_ctx->m_qhead ;
            	   int sz = child_ctx&& child_ctx->m_assigned_literals.size();
            	   bool conflict =child_ctx&&  child_ctx->inconsistent() ;
            	   //But that will lead to a huge recursive call being made at every propagation step.
            	   //So instead, we ensure that there is propagation at the very first step, and afterward assume that if the current solver is up to date, so are the sub solvers
            	   bool canprop = (child_ctx && (initial_propagation || child_qhead<  child_ctx->m_qhead  || child_ctx->m_qhead!=child_ctx->m_assigned_literals.size()));
            	 //  bool can_prop= child_ctx && (initial_propagation || child_qhead<get_context().m_assigned_literals.size() || child_ctx->m_qhead < child_ctx->m_assigned_literals.size());
            	   return (child_ctx && (initial_propagation || child_ctx->inconsistent()   || child_ctx->m_qhead!=child_ctx->m_assigned_literals.size()));
                /*   return child_ctx && (initial_propagation ||
                		   child_ctx->m_qhead != child_ctx->m_assigned_literals.size() ||
                		   child_ctx->m_relevancy_propagator->can_propagate() ||
                		   !child_ctx->m_atom_propagation_queue.empty() ||
                		   child_ctx->m_qmanager->can_propagate() ||
                        !child_ctx->m_eq_propagation_queue.empty() ||
                        !child_ctx->m_th_eq_propagation_queue.empty() ||
                        !child_ctx->m_th_diseq_propagation_queue.empty());*/
            	   //   SASSERT(can_prop== (child_ctx && parent_child_map.size() && child_ctx->can_propagate()) );
            	  // return can_prop;
            	    //return child_ctx;// && ((child_qhead<get_context().) || (child_ctx->m_qhead < child_ctx->m_assigned_literals.size()));
					//return child_ctx && parent_child_map.size() && child_ctx->can_propagate();
               }
               void init_search_eh();
               virtual void propagate();
               virtual void push_scope_eh();
               virtual void pop_scope_eh(unsigned num_scopes);
               void mk_reason_for(literal l, svector<literal> & reason) ;
               bool sharedWithParent(bool_var child_var){
            	   //spped this up!

            	   return  child_parent_map.size()>child_var && child_parent_map[child_var] != null_bool_var;
               }

               void sync_levels(){
            	 /*  if(get_context().get_scope_level()<popto || popto<0){
            		   popto = get_context().get_scope_level();
            	   }*/
                 	if(child_ctx->get_scope_level()>popto && popto>=0)
                 		child_ctx->pop_scope(child_ctx->get_scope_level()-popto);
            		popto=-1;
                 		while(child_ctx->get_scope_level()<get_context().get_scope_level())
               	     		child_ctx->push_scope();


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

               void connect(bool_var parent, bool_var c, context* child);
               void attach(context * child);
               void dettach(context * child);
           };
};

#endif /* _theory_sat_H_ */

