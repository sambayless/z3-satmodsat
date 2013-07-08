/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_sat.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-30.

Revision History:

--*/

#include"smt_context.h"
#include"theory_sat.h"
#include"ast_pp.h"
namespace smt {



    theory_sat::theory_sat(family_id id, context * parent):

        theory(id),
          child_ctx(NULL),
         initial_propagation(true),
         popto(-1),
     	 m_subsearch(FORCE_SUBSEARCH),
     	 m_subsearch_abort_early(false)
    {
    	init(parent);
    	parent_just= new sat_justification(this);
    	m_sms = get_manager().mk_const_decl(symbol("@"),get_manager().mk_bool_sort());
    	m_subsearch = static_cast<saerchtype>( get_context().get_fparams().m_sms_subsearch);
    	m_subsearch_abort_early= get_context().get_fparams().m_sms_subsearch_abort;
    //	std::cout<<"Subsearch type = " << m_subsearch << " " << ", early abort = " << m_subsearch_abort_early << "\n";
    	get_manager().inc_ref(m_sms);
    }
    theory_sat::theory_sat( context * parent):

           theory(0),
           child_ctx(NULL),
           initial_propagation(true),
           popto(-1),
       	  m_subsearch(FORCE_SUBSEARCH),
       	  m_subsearch_abort_early(false)
       {
       	init(parent);
       	parent_just= new sat_justification(this);
       	m_sms = get_manager().mk_const_decl(symbol("@"),get_manager().mk_bool_sort());
                   get_manager().inc_ref(m_sms);
       }


    void theory_sat::attach(context * child){
    	child_ctx=child;
    }
	 void theory_sat::dettach(context * child){
		 child_ctx=NULL;
	 }

	 //This method is passed to conflict resolution.
	 //I'm using it just to check if a given literal should be included in the learnt clause or not,
	 //based on whether it was assigned by the parent solver.
	 //(This is a pretty ugly way to do this, though...)
	    bool check_j(literal l,b_justification & b, void * data) {
	    	if(l==null_literal)
	    		return false;
	    	theory_sat & outer = *(theory_sat*)data;
	    	if(outer.child_ctx->get_assign_level(l)<=outer.child_ctx->get_base_level()){
	    		if(outer.child_parent_map.size()> l.var()){
	    		bool_var v = outer.child_parent_map[ l.var()];
	    		if(v!=null_bool_var)
	    			return true;
	    		}
	    	}
	               	  if(b.get_kind()==b_justification::JUSTIFICATION ){
	       				 justification * j = b.get_justification();
	       				 if(j && j->get_from_theory()==outer.get_family_id()){
	       					 //then j must be a sat_justification
	       					theory_sat::sat_justification * sj = (theory_sat::sat_justification*) j;
	       					 return sj->fromParentTheory();
	       				 }
	       				 return false;
	       			 }else if (b.get_kind()==b_justification::AXIOM){
	       				theory_sat & outer = *(theory_sat*)data;
	       				if(outer.child_parent_map.size()> l.var()){
	       				bool_var v = outer.child_parent_map[ l.var()];
	       				return (v!=null_bool_var);
	       				}
	       				//return  outer.child_ctx->get_assign_level(l)<=outer.child_ctx->get_base_level() && outer.child_parent_map.contains(l.var());
	       			 } else{
	       				 return false;
	       			 }
	               	  return false;
	    }


	 //Propagate assignments to exported variables from the parent solver into the subsolver, and either generate a conflict in the parent solver, or propagate any assignments new to the exported variables back to the parent solver
    //This is by far the most complicated part of this code.
	void theory_sat::propagate(){
    	if(!child_ctx)
    		return;
    	//backtrack as needed
    	 if (popto >=0 &&child_ctx->get_scope_level()>popto){
    		child_ctx->pop_scope(child_ctx->get_scope_level()-popto);

    		if(popto<get_context().get_search_level()  )
    			child_ctx->parent_qhead= std::min(child_ctx->parent_qhead,(int)get_context().m_scopes[get_context().get_search_level()-1].m_assigned_literals_lim);//we can do much better than this, but this is at least safe

    	 }
    	 popto=-1;

    		SASSERT(get_context().get_scope_level() >= child_ctx->get_scope_level());

#ifdef Z3_DEBUG_SMS
    	 if(!child_ctx->inconsistent() ){
    	    for(int i = 0;i<child_ctx->parent_qhead;i++){
    	    	literal parent = get_context().m_assigned_literals[ i];
				if(get_context().get_var_theory(parent.var())!=get_family_id())
					continue;
				bool_var childvar = parent_child_map[parent.var()];
				SASSERT(child_ctx->get_assignment(literal(childvar,parent.sign()))!=l_undef);
    	    }
    	 }
    	#endif

    	 //Quick check to avoid entering the propagate function.
    	 if(!can_propagate()){
    		 while(child_ctx->get_scope_level()<get_context().get_scope_level())
    						 	child_ctx->push_scope();
#ifdef Z3_DEBUG_SMS
 	    	dbg_sync();
 	    	dbg_reasons();
 #endif
 	    		return;
 	    	}


    		initial_propagation=false;
    		SASSERT(get_context().get_scope_level() >= child_ctx->get_scope_level());
    	 int initial_level=child_ctx->get_scope_level();
    	 child_ctx->track_min_level=initial_level;
    	 child_ctx->propagate();
    		SASSERT(get_context().get_scope_level() >= child_ctx->get_scope_level());

    		//Ok: Check through the parent solvers assignments and propagate any assignments to exported varaibles.
    		//child_ctx->parent_qhead records the last position in the _parents_ assignment queue that we previously propagated.
    		while(!child_ctx->inconsistent() && child_ctx->parent_qhead<get_context().m_assigned_literals.size()){
    			literal parent = get_context().m_assigned_literals[ child_ctx->parent_qhead++];
    			if(get_context().get_var_theory(parent.var())!=get_family_id())
    				continue;
    			bool_var childvar = parent_child_map[parent.var()];
    			if(childvar==null_bool_var)
    				continue;//not a theory var


    			int lev = get_context().get_assign_level(parent.var());
    			SASSERT(child_ctx->get_scope_level()<=lev);

    			//Now increase the child solver's scope until it matches the parent solvers for this assignment.
    			//Also, make sure to propagate in the child here and check if this leads to any conflicts.
    			while(child_ctx->get_scope_level()<lev){
    				//We are going to start a new decision level; make sure the current one is fully propagated first
    				initial_level=child_ctx->get_scope_level();
    				//
    				child_ctx->track_min_level=initial_level;
    				child_ctx->propagate();
    				if(child_ctx->inconsistent()  || child_ctx->get_scope_level()<initial_level){
    					goto conflict;
    				}
    				child_ctx->push_scope();
    			}


    			SASSERT(child_ctx->get_scope_level()==get_context().get_scope_level());
    			literal child  = literal(childvar, parent.sign());
    			if(child_ctx->get_assignment(child)==l_false){
    				mk_reason_for(~parent, tmp_reason);
    				SASSERT(get_context().get_assignment(tmp_reason[0])==l_false);
    				if(tmp_reason.size()){
						SASSERT(get_context().get_assignment(tmp_reason[0])==l_false);
						get_context().mk_clause(tmp_reason.size(), tmp_reason.c_ptr(),0,CLS_AUX_LEMMA);
					}else{
						get_context().assign(~true_literal,b_justification::mk_axiom());
					}
    				SASSERT(get_context().inconsistent());
    				return;
    			}
    			SASSERT(child_ctx->get_scope_level()==get_context().get_assign_level(parent));
    			child_ctx->assign(child,b_justification(parent_just), false);
    		}


    		initial_level=child_ctx->get_scope_level();
    		child_ctx->track_min_level=initial_level;
    		child_ctx->propagate();

    		conflict:
    		if(child_ctx->inconsistent()  || child_ctx->get_scope_level()<initial_level){
				//ok, either we have a conflict, or something has to be propagated earlier than it previously was.
    			int lev = std::max((int)get_context().get_search_level(),child_ctx->track_min_level);
    			if(child_ctx->get_scope_level()>lev){
    				child_ctx->pop_scope(child_ctx->get_scope_level()-lev);
    			}
				if(lev<get_context().get_scope_level()){
					get_context().pop_scope(get_context().get_scope_level()-lev);
				}
			}

    		SASSERT(get_context().get_scope_level() >= child_ctx->get_scope_level());

    		//The subsolver is in conflict, so generate a learnt clause on the variables that were assigned by the parent solver, and then use it to create a conflict in the parent solver
    		if(child_ctx->inconsistent()){
    			if(!get_context().inconsistent()){
    			//then we have a conflict which we need to instantiate in S
    			child_ctx->m_conflict_resolution->mk_relative_lemma((child_ctx->m_not_l), child_ctx->m_conflict,false, &check_j,this);

				tmp_reason.reset();
				//Translate the clause into the parent's variable space
				int backtrack_level = 0;int conflict_level =0;
				int min_l = 0;

				for(literal_vector::const_iterator i = child_ctx->m_conflict_resolution->begin_relative();i!= child_ctx->m_conflict_resolution->end_relative();i++){
					literal c_lit = *i;
					if(c_lit==false_literal){
						continue;//this literal is trivially false.
					}
					if(child_ctx->get_assign_level(c_lit)<=child_ctx->get_base_level()){
						//this is a unit lit
						if(child_ctx->get_assignment(c_lit)==l_false){
							continue;//skip this literal
						}else{

						}
					}

					literal p_lit = literal(child_parent_map[ c_lit.var()],c_lit.sign());
					SASSERT(p_lit.var()!=null_bool_var);

					SASSERT(get_context().get_assignment(p_lit)==l_false);
					int l = get_context().get_assign_level(p_lit.var());
					if(l>conflict_level){
						backtrack_level=conflict_level;
						conflict_level=l;
						min_l=tmp_reason.size();
					}else if(l>backtrack_level){
						backtrack_level=l;
					}
					tmp_reason.push_back(p_lit);

				}
				if(min_l>0){
					literal t = tmp_reason[0];
					tmp_reason[0]=tmp_reason[min_l];
					tmp_reason[min_l]=t;
				}

#ifdef Z3_DEBUG_SMS
			get_context().dbg_check(tmp_reason);
			for(int i = 0;i<tmp_reason.size();i++){
				literal l = tmp_reason[i];
				SASSERT(get_context().get_assignment(l)==l_false);
			}
#endif
			//ok, generate a conflict in the super solver using this reason.
			if(tmp_reason.size()){
				SASSERT(get_context().get_assignment(tmp_reason[0])==l_false);
				get_context().mk_clause(tmp_reason.size(), tmp_reason.c_ptr(),0,CLS_AUX_LEMMA);
				//get_context().assign(tmp_reason[0],new sat_justification(tmp_reason,this));
			}else{
				get_context().assign(~true_literal,b_justification::mk_axiom());
			}
    			}
    			SASSERT(get_context().inconsistent());

    			return ;
    		}else{

    			//We successfully propagated from the parent solver to the subsolver without conflict; now check if the subsolver made any assignmnets to the interface variables, and propagate those back up to the parent solver.
    			//find lits to propagate back up to the parent solver

    			while(child_ctx->local_qhead < child_ctx->m_assigned_literals.size()){
    				literal childlit = child_ctx->m_assigned_literals[child_ctx->local_qhead++];
    				if(!sharedWithParent(childlit.var()))
    					continue;

    				bool_var parentvar = child_parent_map[childlit.var()];
    				SASSERT(parentvar != null_bool_var);

    				literal parentlit = literal(parentvar,childlit.sign());
    				lbool parentval = get_context().get_assignment(parentlit);
    				int cassign = child_ctx->get_assign_level(childlit);
    				int childlev =std::max(get_context().get_search_level(), child_ctx->get_assign_level(childlit));
    				if(parentval !=l_undef && get_context().get_assign_level(parentlit)>childlev){
    						get_context().pop_scope(get_context().get_scope_level()-childlev);
    						parentval = get_context().get_assignment(parentlit);
    				}else if (parentval==l_undef && get_context().get_scope_level()>childlev){
    					get_context().pop_scope(get_context().get_scope_level()-childlev);
    				}

    				if(parentval ==l_false){
    					//this is a conflict
    					mk_reason_for(~parentlit, tmp_reason);
						SASSERT(get_context().get_assignment(tmp_reason[0])==l_false);
#ifdef Z3_DEBUG_SMS
			get_context().dbg_check(tmp_reason);
			for(int i = 0;i<tmp_reason.size();i++){
				literal l = tmp_reason[i];
				SASSERT(get_context().get_assignment(l)==l_false);
			}
#endif
						if(tmp_reason.size()){
							SASSERT(get_context().get_assignment(tmp_reason[0])==l_false);
							get_context().mk_clause(tmp_reason.size(), tmp_reason.c_ptr(),0,CLS_AUX_LEMMA);
							//get_context().assign(tmp_reason[0],new sat_justification(tmp_reason,this));
						}else{
							get_context().assign(~true_literal,b_justification::mk_axiom());
						}
						SASSERT(get_context().inconsistent());
    				}else if (parentval==l_undef){
    					SASSERT(get_context().get_scope_level()==childlev);
#ifdef Z3_DEBUG_SMS
    					get_context().dbg_check_propagation(parentlit);
#endif
    					get_context().assign(parentlit,get_context().mk_justification( sat_justification(parentlit,this)));
    				}
    				if(child_ctx->get_scope_level()>get_context().get_scope_level())
						child_ctx->pop_scope(child_ctx->get_scope_level()-get_context().get_scope_level());
					 if (popto >=0 &&child_ctx->get_scope_level()>popto){
						child_ctx->pop_scope(child_ctx->get_scope_level()-popto);

						if(popto<get_context().get_search_level()  )
							child_ctx->parent_qhead= std::min(child_ctx->parent_qhead,(int)get_context().m_scopes[get_context().get_search_level()-1].m_assigned_literals_lim);//we can do much better than this, but this is at least safe

					 }
					 popto=-1;
    			}
    			dbg_reasons();

    			while(child_ctx->get_scope_level()<get_context().get_scope_level())
       				child_ctx->push_scope();


    			child_ctx->parent_qhead=get_context().m_assigned_literals.size();

#ifdef Z3_DEBUG_SMS
	    	dbg_sync();
	    	dbg_reasons();
	#endif

	    	SASSERT(!can_propagate());
    			return;
    		}

    }
    void theory_sat::push_scope_eh(){
    	if(!child_ctx)
    	    		return;
    	//Instead of directly pushing the scope of the subsolver here, we wait until we need to propagate, and push at that time

    }
    void theory_sat::pop_scope_eh(unsigned num_scopes){
    	if(!child_ctx)
    	    		return;

    	//Instead of directly popping the scope of the subsolver here, we wait until we need to propagate, and propagate at that time (using 'popto')

    	SASSERT(child_ctx->track_min_level<=child_ctx->get_scope_level());
    	int newlev = get_context().get_scope_level()-num_scopes;
    	if(newlev < child_ctx->get_scope_level() && (popto<0 || newlev<popto))
    		popto = newlev;
    	if(child_ctx->parent_qhead>get_context().m_assigned_literals.size())
    		child_ctx->parent_qhead=get_context().m_assigned_literals.size();
    	if(child_ctx->track_min_level>=0 && child_ctx->track_min_level<get_context().get_scope_level()){
    		child_ctx->parent_qhead= std::min(child_ctx->parent_qhead,(int)get_context().m_scopes[child_ctx->track_min_level].m_assigned_literals_lim);//we can do much better than this, but this is at least safe

    	}

#ifdef Z3_DEBUG_SMS
    	 if(!child_ctx->inconsistent() ){
    	    for(int i = 0;i<child_ctx->parent_qhead;i++){
    	    	literal parent = get_context().m_assigned_literals[ i];
				if(get_context().get_var_theory(parent.var())!=get_family_id())
					continue;
				bool_var childvar = parent_child_map[parent.var()];
				SASSERT(child_ctx->get_assignment(literal(childvar,parent.sign()))!=l_undef);
    	    }
    	 }
    	#endif
    }


    //Construct the reason for this assignment, in terms of interface varaibles.
    void theory_sat::mk_reason_for(literal parent_lit, svector<literal> & reason_out) {
    	SASSERT(parent_lit!=null_literal);

    	dbg_reasons();

    	literal child_lit = literal(parent_child_map[ parent_lit.var()],parent_lit.sign());
    	SASSERT(child_ctx->get_assignment(child_lit)==l_true);

    	child_ctx->m_conflict_resolution->mk_relative_lemma(child_lit,b_justification::mk_axiom(),true,&check_j,this);
    	reason_out.reset();

    	reason_out.push_back(parent_lit);
    	for(literal_vector::const_iterator i = child_ctx->m_conflict_resolution->begin_relative();i!= child_ctx->m_conflict_resolution->end_relative();i++){
    		literal c_lit = *i;
    		SASSERT(c_lit.var()<child_parent_map.size());
    		literal p_lit = literal(child_parent_map[ c_lit.var()],c_lit.sign());
    		SASSERT(p_lit.var()!=null_bool_var);
    		reason_out.push_back(p_lit);
    	}
#ifdef Z3_DEBUG_SMS
    	get_context().dbg_check(reason_out);
#endif
    }

     void theory_sat::assign_eh(bool_var v, bool is_true){
    	 return;
    }

     //Here, we are mapping the variables for the parent expression to the equivalent variable for the child expression in the child solver.
	    bool theory_sat::internalize_atom(app * n, bool gate_ctx) {
	        TRACE("sat_internalize", tout << "internalising atom:\n" << mk_pp(n, get_context().get_manager()) << "\n";);

	        context & ctx = get_context();

	        SASSERT(!ctx.b_internalized(n));

	        if (ctx.b_internalized(n)) {
	            TRACE("sat_internalize", tout << "term was re-internalized: #" << n->get_id() << "\n";);
	            return true;
	        }
	  	        bool_var v  = ctx.mk_bool_var(n);

	        int index = n->get_decl_kind() ;
			expr * childExp= exported[index];
			if(child_ctx->get_manager().is_true(childExp) ||child_ctx->get_manager().is_false(childExp)  )
			{
				//then this atom is a known constant, and we can just assert it in the main solver.
				 if(child_ctx->get_manager().is_true(childExp)){
					 get_context().assert_expr(n);
					 literal ls[1] = { literal(v,false) };
					 get_context().mk_clause(1,ls, 0);
				 }else{
					 get_context().assert_expr(get_context().get_manager().mk_not(n));
					 literal ls[1] = { literal(v,true) };
					 get_context().mk_clause(1,ls, 0);
				 }

				return true;
			}

			ctx.set_var_theory(v, get_id());

	        if(!child_ctx->b_internalized(childExp))
	        	child_ctx->internalize(childExp,false);

	        bool_var subvar =child_ctx->get_bool_var(childExp);

	        SASSERT(subvar!=null_bool_var);

	        if(subvar==null_bool_var)
	        	subvar = child_ctx->mk_bool_var(childExp);

			while(parent_child_map.size()<=v){
				parent_child_map.push_back(null_bool_var);
			}
			while(child_parent_map.size()<=subvar){
				child_parent_map.push_back(null_bool_var);
				}
			SASSERT(parent_child_map[v]==null_bool_var);
			SASSERT(child_parent_map[subvar]==null_bool_var);
			parent_child_map[v]=subvar;
			child_parent_map[subvar]=v;


	        TRACE("sat_internalize", tout << "succeeded... v: " << v << "\n";);

	        return true;
	    }

    bool theory_sat::internalize_term(app * term) {
        return false;
    }

    void theory_sat::new_eq_eh(theory_var v1, theory_var v2) {

    }

    bool theory_sat::use_diseqs() const {
        return false;
    }

    void theory_sat::new_diseq_eh(theory_var v1, theory_var v2) {
        UNREACHABLE();
    }

    void theory_sat::reset_eh() {
    	initial_propagation=true;

        theory::reset_eh();

    }
    void theory_sat::init_search_eh(){
    if(!child_ctx)
    	return;

    	child_ctx->check_preamble(false);
    	child_ctx->pop_to_base_lvl();
    	child_ctx->setup_context(false);
    	child_ctx->internalize_assertions();



    }


    final_check_status theory_sat::final_check_eh() {
    	if(!child_ctx)
				return FC_DONE;

    	//Ok: Now that we have successfully solved the parent solver, try solving the child solver.
    	//Either the child solver can be solved under its current interface assignment, or it cant.

    	//We are looping here to allow the child solver to backtrack past the interface assignments when it learns clauses,
    	//while still forcing it to solve under those assignments.

    	//There is actually some magic here: controlling exactly how the subsolver backtracks here, and deciding when it gives up and returns to the parent solver,
    	//can have a huge influence on the runtime.


    		int initial_parent_level = get_context().get_scope_level();
    		int initial_level= child_ctx->get_scope_level();

    		propagate();
    		int minlev = child_ctx->get_scope_level();
    		if(get_context().track_min_level < get_context().min_subsearch_level)
    		{
    			//don't attempt to solve the sub context here, because the parent solver has already been backtracked passed, just return...
    			return FC_DONE;
    		}

    		if(m_subsearch==PARTIAL_SUBSEARCH)
				child_ctx->min_subsearch_level = child_ctx->get_scope_level();
			else
				child_ctx->min_subsearch_level = 0;

    		SASSERT(minlev<=initial_parent_level);
    		lbool res=l_undef;
    		while(!child_ctx->inconsistent() && res==l_undef){
    			propagate();
    			if(child_ctx->inconsistent())
    				break;

    			if(m_subsearch==LONG_PARTIAL_SUBSEARCH)
					child_ctx->min_subsearch_level = child_ctx->get_scope_level();
				else
					child_ctx->min_subsearch_level = 0;

    			child_ctx->track_min_level=child_ctx->get_scope_level();
    			 dbg_sync();
    			//SASSERT(child_ctx->get_scope_level()==get_context().get_scope_level());
    			 res =(child_ctx->limited_search());

    			 minlev = std::min(minlev, child_ctx->track_min_level);
    			 pop_scope_eh(get_context().get_scope_level()-minlev);
    			 int tminlev =  std::max((int)get_context().get_search_level(),minlev);
    			 if(get_context().get_scope_level()>tminlev){
					get_context().pop_scope(get_context().get_scope_level()-tminlev);
    				 if (m_subsearch_abort_early){
    					 res= l_false;
    					 break;//give up search
    				 }
    			 }
    			 //give up after a single solve attempt.
    			 if(m_subsearch == SINGLE_SUBSEARCH){
    				 if(res!=l_true)
    					 res = l_false;
    				 break;
    			 }
    		}

    		propagate();
    		dbg_reasons();

    		if(res==l_true && get_context().get_scope_level()==initial_parent_level){
    			SASSERT(get_context().get_scope_level()==child_ctx->get_scope_level());
    			return FC_DONE;
    		}

    		return FC_CONTINUE;

    }

    char const * theory_sat::get_name() const {
        return "SAT_mod_SAT";
    }

};
