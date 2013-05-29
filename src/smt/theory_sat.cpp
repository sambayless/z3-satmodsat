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
        m_name("SubSolver"),
        parent_qhead(0),
        child_qhead(0),
        child_ctx(NULL)
        //,
        //th_trail_stack(*this)
    {
    	init(parent);
    	parent_just= new sat_justification(this);

    	 m_sms = get_manager().mk_const_decl(symbol("@"),get_manager().mk_bool_sort());
    	// m_sms = get_manager().mk_func_decl(symbol("@"),0,get_manager().mk_bool_sort(), get_manager().mk_bool_sort());
    	// m_sms = get_manager().mk_func_decl(symbol("@"),0,get_manager().mk_bool_sort(), get_manager().mk_bool_sort(),false,false,false);


    	               get_manager().inc_ref(m_sms);

    	            //   func_decl * mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range) {
    }
    theory_sat::theory_sat( context * parent):

           theory(0),
           m_name("SubSolver"),
           parent_qhead(0),
           child_qhead(0),
           child_ctx(NULL)
           //,
           //th_trail_stack(*this)
       {
       	init(parent);
       	parent_just= new sat_justification(this);
     //   func_decl_info info(id, OP_SMS);
         //      info.set_associative();
          //     info.set_flat_associative();
          //     info.set_commutative();
   	 m_sms = get_manager().mk_const_decl(symbol("@"),get_manager().mk_bool_sort());
             //  m_sms = get_manager().mk_func_decl(symbol("@"),get_manager().mk_bool_sort(), get_manager().mk_bool_sort());
               get_manager().inc_ref(m_sms);
       }

    void theory_sat::connect(bool_var parent, bool_var c, context* child){
    	//not supporting multiple children yet...
    	while(parent_child_map.size()<=parent){
    		parent_child_map.push_back(null_bool_var);
    	}
     	while(child_parent_map.size()<=c){
     		child_parent_map.push_back(null_bool_var);
        	}
    	parent_child_map[parent]=c;
    	child_parent_map[c]=parent;
    }
    void theory_sat::attach(context * child){
    	child_ctx=child;
    }
	 void theory_sat::dettach(context * child){
		 child_ctx=NULL;
	 }
	    bool check_j(literal l,b_justification & b, void * data) {

	    	theory_sat & outer = *(theory_sat*)data;
	               	  if(b.get_kind()==b_justification::JUSTIFICATION ){
	       				 justification * j = b.get_justification();
	       				 if(j && j->get_from_theory()==outer.get_family_id()){
	       					 //then j must be a sat_justification
	       					theory_sat::sat_justification * sj = (theory_sat::sat_justification*) j;
	       					 return sj->fromParentTheory();
	       				 }
	       				 return false;
	       			 }else{
	       				 return false;
	       			 }
	    }

    void theory_sat::propagate(){
    	if(!child_ctx )
    		return;
    	child_qhead=child_ctx->m_qhead;
    	child_ctx->propagate();
    	if(child_ctx->inconsistent() ){

#ifdef REPORT
    		std::cout<<"Construct reason for " << child_ctx->m_not_l << ": ";
    	            	for(int i = 0;i<child_ctx->m_assigned_literals.size();i++){
    	            		literal l = child_ctx->m_assigned_literals[i];
    	            		int lev = child_ctx->get_assign_level(l);
    	            		std::cout<<  l << "(L" << lev << ") ";
    	            	}
    	            	std::cout<<"\n";
#endif
    		//ok, we need to resolve this conflict down to the assignments from the parent solver
    		child_ctx->m_conflict_resolution->mk_relative_lemma((child_ctx->m_not_l), child_ctx->m_conflict, &check_j,this);

    		tmp_reason.reset();
    		//Translate the clause into the parent's variable space
    		int backtrack_level = 0;int conflict_level =0;
    		int min_l = 0;

			for(literal_vector::const_iterator i = child_ctx->m_conflict_resolution->begin_relative();i!= child_ctx->m_conflict_resolution->end_relative();i++){
				literal c_lit = *i;
				if(c_lit==false_literal){
					continue;//this literal is trivially false.
				}
				literal p_lit = literal(child_parent_map[ c_lit.var()],c_lit.sign());

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
#ifdef REPORT
			std::cout<<"Interface conflict (" << child_ctx->solver_num << ","<< get_context().solver_num << ") at level " << get_context().get_scope_level() << ", backtrack to " <<backtrack_level << " :";// <<  <<"\n";
			for(int i = 0;i<tmp_reason.size();i++)
				std::cout << tmp_reason[i] << " ";
			std::cout<<"\n";
#endif
#ifdef Z3_DEBUG_SMS
			get_context().dbg_check(tmp_reason);
#endif
			//add a new clause into the parent solver using this reason


			//generate a conflict in the super solver using this reason.
			if(tmp_reason.size()){
				//get_context().mk_clause(tmp_reason.size(), tmp_reason.c_ptr(),0,CLS_AUX_LEMMA);

				get_context().assign(tmp_reason[0],new sat_justification(tmp_reason,this));
			}else{
				get_context().assign(~true_literal,b_justification::mk_axiom());
			}
			//this may still leave the context in conflict after we add the clause.
		/*	if(backtrack_level<get_context().get_base_level())
				backtrack_level=get_context().get_base_level();//don't backtrack past base level
			if(backtrack_level<get_context().get_scope_level())
				get_context().pop_scope(get_context().get_scope_level()-backtrack_level);
			//
			//if(tmp_reason.size()){
				//make this clause in the parent solver
				clause * c =  get_context().mk_clause(tmp_reason.size(),tmp_reason.c_ptr(), NULL, CLS_AUX_LEMMA);//not supporting traces right now*/

		//	}else{
				//ie, add the empty clause.
			//	get_context().assign(false_literal,b_justification::mk_axiom());
				//get_context().assign( ,b_justification::mk_axiom());
		//	}
			bool b = get_context().inconsistent();
			SASSERT(get_context().inconsistent());
			//ok, the parent solver is now inconsistent and will backtrack as needed
    	}else{
    		//propagation succeeded, enqueue any propagated interface variables to the parent

    		//find lits to prop
			while(!get_context().inconsistent() && child_qhead<child_ctx->m_qhead){
				literal local_l =child_ctx->m_assigned_literals [child_qhead++];
				if(sharedWithParent(local_l.var())){
					literal parent_l = literal(child_parent_map[local_l.var()],local_l.sign());
#ifdef REPORT
					std::cout<< child_ctx->solver_num << "(" << local_l << ")" << " to " << get_context().solver_num << "(" << parent_l << ")\n";
#endif
#ifdef Z3_DEBUG_SUB
					get_context().dbg_check_propagation(parent_l);
#endif
					if(get_context().get_assignment(parent_l) != l_true)
						get_context().assign(parent_l,get_context().mk_justification( sat_justification(parent_l,this)));
				}


			}
    	}
    }
    void theory_sat::push_scope_eh(){
    	if(!child_ctx)
    	    		return;
    	while(child_ctx->get_scope_level()<get_context().get_scope_level())
    		child_ctx->push_scope();
    }
    void theory_sat::pop_scope_eh(unsigned num_scopes){
    	if(!child_ctx)
    	    		return;

    	int newlev = get_context().get_scope_level()-num_scopes;
    	if(child_ctx->get_scope_level()>newlev)
    		child_ctx->pop_scope(child_ctx->get_scope_level()-newlev);
    }


    void theory_sat::mk_reason_for(literal parent_lit, svector<literal> & reason_out) {
    	SASSERT(parent_lit!=null_literal);
    	SASSERT(get_context().get_assignment(parent_lit)==l_true);




    	literal child_lit = literal(parent_child_map[ parent_lit.var()],parent_lit.sign());
#ifdef REPORT
    	std::cout<<"Construct reason for " << child_lit << ": ";
            	for(int i = 0;i<child_ctx->m_assigned_literals.size();i++){
            		literal l = child_ctx->m_assigned_literals[i];
            		int lev = child_ctx->get_assign_level(l);
            		std::cout<<  l << "(L" << lev << ") ";
            	}
            	std::cout<<"\n";
#endif
    	child_ctx->m_conflict_resolution->mk_relative_lemma(child_lit,b_justification::mk_axiom(),&check_j,this);
    	reason_out.reset();
    	for(literal_vector::const_iterator i = child_ctx->m_conflict_resolution->begin_relative();i!= child_ctx->m_conflict_resolution->end_relative();i++){
    		literal c_lit = *i;
    		literal p_lit = literal(child_parent_map[ c_lit.var()],c_lit.sign());
    		reason_out.push_back(p_lit);
    	}
    	//reason_out[0]=~reason_out[0];
#ifdef Z3_DEBUG_SMS
    	get_context().dbg_check(reason_out);
#endif
    }

     void theory_sat::assign_eh(bool_var v, bool is_true){
    	 if(!child_ctx||  !parent_child_map.size())
    	     		return;

      	if(child_ctx->get_scope_level()>get_context().get_scope_level())
      		child_ctx->pop_scope(child_ctx->get_scope_level()-get_context().get_scope_level());

    	 while(child_ctx->get_scope_level()<get_context().get_scope_level())
    	     		child_ctx->push_scope();


    	literal child_lit = literal(parent_child_map[v],!is_true);
    	literal t = literal(child_parent_map[child_lit.var()],!is_true);
#ifdef REPORT
    	std::cout<< get_context().solver_num << "(" << t << ")" << " to " << child_ctx->solver_num << "(" << child_lit <<")\n";
#endif
    	SASSERT(t.var()==v);
    	SASSERT(t.var()!=null_bool_var);
    	//ok, need to switch this to creating a justification that can be distinguished from true axioms.
    	child_ctx->assign(child_lit ,b_justification(parent_just), false);
    }

	    bool theory_sat::internalize_atom(app * n, bool gate_ctx) {
	        TRACE("sat_internalize", tout << "internalising atom:\n" << mk_pp(n, get_context().get_manager()) << "\n";);

	        context & ctx = get_context();

	        SASSERT(!ctx.b_internalized(n));

	        if (ctx.b_internalized(n)) {
	            TRACE("sat_internalize", tout << "term was re-internalized: #" << n->get_id() << "\n";);
	            return true;
	        }


	        //To link theories, create a _new_ variable in the upper theory, and then associate it with the theory of SMT identifier so that context will call theory_sat.assign_eh

	        bool_var v  ; // = ctx.get_bool_var(n);

			//if(v==null_bool_var)
				v = ctx.mk_bool_var(n);
#ifdef REPORT
				std::cout << get_context().solver_num << " internalising atom:\n"<<mk_pp(n, get_context().get_manager()) << " is variable " << v  << "\n";
				if(get_context().get_assignment(v)!=l_undef){
					std::cout<<"ALREADY ASSIGNED!\n";

				}
#endif

	       //
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

	        //catch constants here


	        SASSERT(subvar!=null_bool_var);
#ifdef REPORT
	        std::cout << get_context().solver_num << " < " << child_ctx->solver_num << " exported from child atom:\n"<<mk_pp(childExp, child_ctx->get_manager()) << " is variable " << subvar  << "\n";

	    				if(child_ctx->get_assignment(subvar)!=l_undef){
	    					std::cout<<"ALREADY ASSIGNED SUBVAR!\n";

	    				}
#endif
	        if(subvar==null_bool_var)
	        	subvar = child_ctx->mk_bool_var(childExp);
	        connect(v,subvar,child_ctx);

	        TRACE("sat_internalize", tout << "succeeded... v: " << v << "\n";);
	       // std::cout<<  "succeeded... v: " << v << "\n";
	        return true;
	    }

    bool theory_sat::internalize_term(app * term) {
    	int a = 1;
        return false;
    }

    void theory_sat::new_eq_eh(theory_var v1, theory_var v2) {
        UNREACHABLE();
    }

    bool theory_sat::use_diseqs() const {
        return false;
    }

    void theory_sat::new_diseq_eh(theory_var v1, theory_var v2) {
        UNREACHABLE();
    }

    void theory_sat::reset_eh() {

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
    /*	child_ctx->reset_assumptions();
    	//ok, now we want to solve the sub solver, treating its current assignment as an assumption
    	for(int i = 0;i<child_ctx->m_assigned_literals.size();i++){
    		child_ctx->m_assumptions.push_back(l.var());
    	}*/

    	if(!child_ctx->propagate())
        		return FC_CONTINUE;

      	if(child_ctx->get_scope_level()>get_context().get_scope_level())
      		child_ctx->pop_scope(child_ctx->get_scope_level()-get_context().get_scope_level());

    	 while(child_ctx->get_scope_level()<get_context().get_scope_level())
    	     		child_ctx->push_scope();
    	int start_lev = child_ctx->get_scope_level();
    	int start_base =   child_ctx->m_base_lvl;
#ifdef REPORT
    	//child_ctx->push_scope();
    	std::cout<<"Begin search: ";
    	for(int i = 0;i<child_ctx->m_assigned_literals.size();i++){
    		literal l = child_ctx->m_assigned_literals[i];
    		int lev = child_ctx->get_assign_level(l);
    		std::cout<<  l << "(L" << lev << ") ";
    	}
    	std::cout<<"\n";
#endif
    	int start_search_lvl = child_ctx->m_search_lvl;
    	child_ctx->m_search_lvl=child_ctx->get_scope_level();
/*
    	while(child_ctx->m_base_lvl<child_ctx->get_scope_level()){
			child_ctx->m_base_scopes.push_back(context::base_scope());
			context::base_scope & bs              = child_ctx->m_base_scopes.back();
			bs.m_lemmas_lim              = child_ctx->m_lemmas.size();
			bs.m_inconsistent            = child_ctx->inconsistent();
			bs.m_simp_qhead_lim          = child_ctx->m_simp_qhead;
			child_ctx->m_base_lvl++;
			child_ctx->m_search_lvl++;
    	}*/

    	lbool res = (child_ctx->unbounded_search());
#ifdef REPORT
    	std::cout<<"Post Search: ";
    	for(int i = 0;i<child_ctx->m_assigned_literals.size();i++){
        		literal l = child_ctx->m_assigned_literals[i];
        		int lev = child_ctx->get_assign_level(l);
        		std::cout<<  l << "(L" << lev << ") ";
        	}
        	std::cout<<"\n";
#endif
    	//now put the base level back to what it used to be
    	int lev = child_ctx->get_scope_level();
#ifdef REPORT
    	std::cout<<"Conflict: " << child_ctx->m_not_l <<" ";
    	if(child_ctx->m_conflict.get_kind()==b_justification::JUSTIFICATION){
    		justification * j = child_ctx->m_conflict.get_justification();
    		std::cout<<j;
    	}
    	std::cout<<"\n";
#endif
    //	child_ctx->pop_to_base_lvl();
    /*	while(child_ctx->m_base_lvl>start_base){
        			child_ctx->m_base_scopes.pop_back();

        			child_ctx->m_base_lvl--;
        			child_ctx->m_search_lvl--;
            	}
*/
      	int end_lev = child_ctx->get_scope_level();
      	child_ctx->m_search_lvl=start_search_lvl;
#ifdef REPORT
    	std::cout<<"After backtrack: ";
    	for(int i = 0;i<child_ctx->m_assigned_literals.size();i++){
        		literal l = child_ctx->m_assigned_literals[i];
        		int lev = child_ctx->get_assign_level(l);
        		std::cout<<  l << "(L" << lev << ") ";
        	}
        	std::cout<<"\n";
#endif
/*    	if(child_ctx->get_scope_level()>start_lev)
    		child_ctx->pop_scope(child_ctx->get_scope_level()-start_lev);*/



    	if(res == l_undef){
    		//shouldn't happen
    		return FC_GIVEUP;
    	}else if (res==l_true){
    		return FC_DONE;
    	}else if (res==l_false){
    		//backtrack as needed and learn a clause
    		SASSERT(child_ctx->inconsistent());
    		//this is handled the same way as propagate() - if the child solver is inconsistent, then a new clause will be created that makes the parent solver inconsistent.
    		propagate();
    		return FC_CONTINUE;
    	}
    	UNREACHABLE();
    }

    char const * theory_sat::get_name() const {
        return m_name;
    }

};
