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

        child_ctx(NULL),
        initial_propagation(true),popto(-1)
        //,
        //th_trail_stack(*this)
    {
    	init(parent);
    	parent_just= new sat_justification(this);
    	m_flip_assign=false;
    	 m_sms = get_manager().mk_const_decl(symbol("@"),get_manager().mk_bool_sort());
    	// m_sms = get_manager().mk_func_decl(symbol("@"),0,get_manager().mk_bool_sort(), get_manager().mk_bool_sort());
    	// m_sms = get_manager().mk_func_decl(symbol("@"),0,get_manager().mk_bool_sort(), get_manager().mk_bool_sort(),false,false,false);


    	               get_manager().inc_ref(m_sms);

    	            //   func_decl * mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range) {
    }
    theory_sat::theory_sat( context * parent):

           theory(0),
           m_name("SubSolver"),

           child_ctx(NULL),
           initial_propagation(true),popto(-1)

       {
       	init(parent);
       	parent_just= new sat_justification(this);
    	m_flip_assign=false;

   	 m_sms = get_manager().mk_const_decl(symbol("@"),get_manager().mk_bool_sort());
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
     	SASSERT(parent_child_map[parent]==null_bool_var);
     	SASSERT(child_parent_map[c]==null_bool_var);
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



    void theory_sat::propagate(){
    	if(!child_ctx)
    		return;
    	//backtrack as needed
    	static int it = 0;
    	    	int localit = ++it;
    	    	if(localit==8){
    	    		int a =1;
    	    	}


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
    	 if(!can_propagate()){
    		 while(child_ctx->get_scope_level()<get_context().get_scope_level())
    						 	child_ctx->push_scope();
#ifdef Z3_DEBUG_SMS
 	    	dbg_sync();
 	    	dbg_reasons();
 #endif
 	    		return;
 	    	}


    	//	if((!initial_propagation && !child_ctx->inconsistent() &&   parent_qhead==get_context().m_assigned_literals.size()   && child_ctx->m_qhead==child_ctx->m_assigned_literals.size())){

    		initial_propagation=false;
    		SASSERT(get_context().get_scope_level() >= child_ctx->get_scope_level());
    	 int initial_level=child_ctx->get_scope_level();
    	 child_ctx->track_min_level=initial_level;
    	 child_ctx->propagate();
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

    		while(!child_ctx->inconsistent() && child_ctx->parent_qhead<get_context().m_assigned_literals.size()){
    			literal parent = get_context().m_assigned_literals[ child_ctx->parent_qhead++];
    			if(get_context().get_var_theory(parent.var())!=get_family_id())
    				continue;
    			bool_var childvar = parent_child_map[parent.var()];
    			if(childvar==null_bool_var)
    				continue;//not a theory var


    			int lev = get_context().get_assign_level(parent.var());
    			SASSERT(child_ctx->get_scope_level()<=lev);
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
    				//goto conflict;
    				mk_reason_for(~parent, tmp_reason);
    				SASSERT(get_context().get_assignment(tmp_reason[0])==l_false);
    				if(tmp_reason.size()){
						SASSERT(get_context().get_assignment(tmp_reason[0])==l_false);
						get_context().mk_clause(tmp_reason.size(), tmp_reason.c_ptr(),0,CLS_AUX_LEMMA);
						//get_context().assign(tmp_reason[0],new sat_justification(tmp_reason,this));
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
    		if(localit==8){
    		    	    		int a =1;
    		    	    	}

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
						if(child_ctx->get_assign_level(c_lit)==l_false){
							continue;//skip this literal
						}else{

						}
					}

					literal p_lit = literal(child_parent_map[ c_lit.var()],c_lit.sign());
					if(p_lit.var()==null_bool_var){
						exit(3);
					}

					SASSERT(p_lit.var()!=null_bool_var);
					//SASSERT(child_ctx->get_assignment(c_lit)==l_false);
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

#ifdef REPORT
			std::cout<<"Interface conflict (" << child_ctx->solver_num << ","<< get_context().solver_num << ") at level " << get_context().get_scope_level() << ", backtrack to " <<backtrack_level << " :";// <<  <<"\n";
			for(int i = 0;i<tmp_reason.size();i++)
				std::cout << tmp_reason[i] << " ";
			std::cout<<"\n";
#endif
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
	    	if(can_propagate()){
	    		int a =1;
	    	}
	    	SASSERT(!can_propagate());
    			return;
    		}

    }
    void theory_sat::push_scope_eh(){
    	if(!child_ctx)
    	    		return;
    	//don't do anything here - instead, sync_levels will lazily syncronize the levels between the child and parent solvers when assignments or propagations occur.
    /*	while(child_ctx->get_scope_level()<get_context().get_scope_level())
    		child_ctx->push_scope();*/
    }
    void theory_sat::pop_scope_eh(unsigned num_scopes){
    	if(!child_ctx)
    	    		return;
    	SASSERT(child_ctx->track_min_level<=child_ctx->get_scope_level());
    	int newlev = get_context().get_scope_level()-num_scopes;
    	if(newlev < child_ctx->get_scope_level() && (popto<0 || newlev<popto))
    		popto = newlev;
    	if(child_ctx->parent_qhead>get_context().m_assigned_literals.size())
    		child_ctx->parent_qhead=get_context().m_assigned_literals.size();
    	if(child_ctx->track_min_level>=0 && child_ctx->track_min_level<get_context().get_scope_level()){
    		child_ctx->parent_qhead= std::min(child_ctx->parent_qhead,(int)get_context().m_scopes[child_ctx->track_min_level].m_assigned_literals_lim);//we can do much better than this, but this is at least safe

    	}
    	//if(newlev==get_context().get_search_level() && get_context().get_search_level()>0 )
    	//	parent_qhead= std::min(parent_qhead,(int)get_context().m_scopes[get_context().get_search_level()-1].m_assigned_literals_lim);//we can do much better than this, but this is at least safe
    	//if(child_ctx->get_scope_level()>newlev)
    	//	child_ctx->pop_scope(child_ctx->get_scope_level()-newlev);
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



    void theory_sat::mk_reason_for(literal parent_lit, svector<literal> & reason_out) {
    	SASSERT(parent_lit!=null_literal);
    	if(parent_lit.var()==5){
    		int  a=1;
    	}

    	dbg_reasons();

    	literal child_lit = literal(parent_child_map[ parent_lit.var()],parent_lit.sign());
    	SASSERT(child_ctx->get_assignment(child_lit)==l_true);
#ifdef REPORT
    	std::cout<<"Construct reason for " << child_lit << ": ";
            	for(int i = 0;i<child_ctx->m_assigned_literals.size();i++){
            		literal l = child_ctx->m_assigned_literals[i];
            		int lev = child_ctx->get_assign_level(l);
            		std::cout<<  l << "(L" << lev << ") ";
            	}
            	std::cout<<"\n";
#endif
    	child_ctx->m_conflict_resolution->mk_relative_lemma(child_lit,b_justification::mk_axiom(),true,&check_j,this);
    	reason_out.reset();



    	reason_out.push_back(parent_lit);
    	for(literal_vector::const_iterator i = child_ctx->m_conflict_resolution->begin_relative();i!= child_ctx->m_conflict_resolution->end_relative();i++){
    		literal c_lit = *i;
    		SASSERT(c_lit.var()<child_parent_map.size());
    		literal p_lit = literal(child_parent_map[ c_lit.var()],c_lit.sign());
    		if(p_lit.var()==null_bool_var){
    							exit(3);
    						}
    		reason_out.push_back(p_lit);
    	}


    	//reason_out[0]=~reason_out[0];
#ifdef Z3_DEBUG_SMS
    	get_context().dbg_check(reason_out);
#endif
    }

     void theory_sat::assign_eh(bool_var v, bool is_true){
    	 return;
    	/* if(!child_ctx||  !parent_child_map.size())
    	     		return;




    	literal child_lit = literal(parent_child_map[v],!is_true);
    	literal t = literal(child_parent_map[child_lit.var()],!is_true);
#ifdef REPORT
    	std::cout<< get_context().solver_num << "(" << t << ")" << " to " << child_ctx->solver_num << "(" << child_lit <<")\n";
#endif
    	SASSERT(t.var()==v);
    	SASSERT(t.var()!=null_bool_var);
    	int plev = get_context().get_assign_level(v);
    	sync_levels(get_context().get_assign_level(v));// get_context().get_assign_level(v));
    	SASSERT(get_context().get_assign_level(v)==child_ctx->m_scope_lvl);
    	//ok, need to switch this to creating a justification that can be distinguished from true axioms.
    	child_ctx->assign(child_lit ,b_justification(parent_just), false);
    	if(child_lit.var()==22){
    		int a=1;
    	}*/
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
				//std::cout << get_context().solver_num << " internalising atom:\n"<<mk_pp(n, get_context().get_manager()) << " is variable " << v  << "\n";


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
	      //  std::cout << get_context().solver_num << " < " << child_ctx->solver_num << " exported from child atom:\n"<<mk_pp(childExp, child_ctx->get_manager()) << " is variable " << subvar  << "\n";
	        std::cout<< get_context().solver_num << " var " << v << " < " << child_ctx->solver_num << " var " << subvar << "\n";
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



    		int initial_parent_level = get_context().get_scope_level();
    		int initial_level= child_ctx->get_scope_level();

    		propagate();
    		int minlev = child_ctx->get_scope_level();
    		SASSERT(minlev<=initial_parent_level);
    		lbool res=l_undef;
    		while(!child_ctx->inconsistent() && res==l_undef){
    			propagate();
    			if(child_ctx->inconsistent())
    				break;
    			child_ctx->track_min_level=child_ctx->get_scope_level();
    			 dbg_sync();
    			//SASSERT(child_ctx->get_scope_level()==get_context().get_scope_level());
    			 res =(child_ctx->unbounded_search());

    			 minlev = std::min(minlev, child_ctx->track_min_level);
    			 pop_scope_eh(get_context().get_scope_level()-minlev);
    			 int tminlev =  std::max((int)get_context().get_search_level(),minlev);
    			 if(get_context().get_scope_level()>tminlev)
						get_context().pop_scope(get_context().get_scope_level()-tminlev);

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
        return m_name;
    }

};
