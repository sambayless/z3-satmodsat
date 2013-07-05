
#include<iostream>
#include<time.h>
#include<signal.h>

#include"timeout.h"
#include"aig/aig_parser.h"

#include"smt_strategic_solver.h"

#include"tactic2solver.h"
#include "smt_context.h"
#include "reg_decl_plugins.h"
#include "ast_pp.h"
#include "smt_types.h"
#include "aig_frontend.h"
extern bool g_display_statistics;
extern void display_config();
static clock_t             g_start_time;


static void display_statistics() {
    display_config();
    clock_t end_time = clock();

}

static void on_timeout() {
    display_statistics();
    exit(0);
}

static void on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    display_statistics();
    raise(SIGINT);
}


unsigned read_aig(char const* file_name, front_end_params& front_end_params) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);

    ast_manager m;
    front_end_params.m_minimize_lemmas=false;//disabled for now.
   /* front_end_params.m_relevancy_lvl=0;
    front_end_params.m_pre_simplifier=false;
    front_end_params.m_pre_simplify_expr=false;*/
    reg_decl_plugins(m);
    smt::context *ctx = new smt::context(m,front_end_params);

    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    vector<expr*> gates;
    vector<expr*> inputs;
    vector<expr*> outputs;
    vector<expr*> in_latches;
    vector<expr*> out_latches;
    vector<expr*> out_latches_prev;
    bool result = true;
    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
         parse_aig (in,inputs,outputs,in_latches,out_latches,gates,ctx->get_manager());
    }
    else {
         parse_aig (std::cin,inputs,outputs,in_latches,out_latches,gates,ctx->get_manager());
    }
    for(int i =  0;i<out_latches.size();i++){
    	expr * e =  ctx->get_manager().mk_fresh_const("OutLatch",ctx->get_manager().mk_bool_sort());
	     ctx->assert_expr(ctx->get_manager().mk_eq(out_latches[i],e));
	     out_latches[i]=e;
    }
    //AIG format assumes all in latches start assigned to 0
    for(int i = 0;i<in_latches.size();i++){
    	ctx->assert_expr(m.mk_not(in_latches[i]));
    }
    if(outputs.size()==0)
    	exit(20);
    expr* any_out = outputs[0];//ctx->get_manager().mk_or(outputs.size(),outputs.c_ptr());
   // ctx->push();
   // ctx->assert_expr(any_out);
    expr * property = ctx->get_manager().mk_fresh_const("Property",ctx->get_manager().mk_bool_sort());
    ctx->assert_expr(ctx->get_manager().mk_eq(property,any_out));
#ifdef Z3_DEBUG_SMS
    for(int i = 0;i<gates.size();i++){
    	ctx->dbg_gate_map.insert(gates[i],i);
    }
    ctx->dbg_gate_map.insert(any_out, gates.size());
    ctx->dbg_gate_map.insert(property, gates.size());
#endif
        lbool res = ctx->check_fast(1,&property);

    ctx->pop_to_base_lvl();
   // ctx->pop(1);
    result = (res==l_true);
    std::cout<<"k=" << 0 <<"\n";
    int i = 0;

    if(out_latches.size()){
     	//do a really simple BMC pass
    	for(i = 1;!result;i++){
    		std::cout<<"k=" << i <<"\n";
    		out_latches_prev.reset();
    		out_latches_prev.append(out_latches.size(), out_latches.c_ptr());

    	    ast_manager * m = new ast_manager();
    	    reg_decl_plugins(*m);
    	    smt::context *ctx2 = new smt::context(*m,front_end_params);
    	    ctx2->check();//get rid of this later
    	    ctx2->pop_to_base_lvl();

    	    if (file_name) {
    	        std::ifstream in(file_name);
    	        if (in.bad() || in.fail()) {
    	            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
    	            exit(ERR_OPEN_FILE);
    	        }
    	         parse_aig (in,inputs,outputs,in_latches,out_latches,gates,ctx2->get_manager());
    	    }
    	    else {
    	         parse_aig (std::cin,inputs,outputs,in_latches,out_latches,gates,ctx2->get_manager());
    	    }
    	    for(int i =  0;i<out_latches.size();i++){
    	       	expr * e =  ctx2->get_manager().mk_fresh_const("OutLatch",ctx2->get_manager().mk_bool_sort());
    	         ctx2->assert_expr(ctx2->get_manager().mk_eq(out_latches[i],e));
    	   	     out_latches[i]=e;
    	       }
#ifdef Z3_DEBUG_SMS
       	    //debug solver
    	    ast_manager * mdbg = new ast_manager();
			reg_decl_plugins(*mdbg);
			smt::context *dbg_ctx = new smt::context(*mdbg,front_end_params);
			vector<expr*> dbg_out_latches_prev;
			expr* dbg_any_out = 0;
			 expr * dbg_property=0;
			 expr * dbgeq=0;
			{


			    vector<expr*> dbg_inputs;
			    vector<expr*> dbg_outputs;
			    vector<expr*> dbg_in_latches;
			    vector<expr*> dbg_out_latches;

			    vector<expr*> dbg_gates;

				std::ifstream in(file_name);
				parse_aig (in,dbg_inputs,dbg_outputs,dbg_in_latches,dbg_out_latches,dbg_gates,dbg_ctx->get_manager());
				//AIG format assumes all in latches start assigned to 0

				for(int j = 0;j<dbg_in_latches.size();j++){
					expr*e=dbg_ctx->get_manager().mk_not(dbg_in_latches[j]);
					dbg_ctx->assert_expr(e);
				}

				for(int j = 1;j<=i;j++){
					 dbg_out_latches_prev.reset();
					 dbg_out_latches_prev.append(dbg_out_latches.size(), dbg_out_latches.c_ptr());
					 std::ifstream in(file_name);
					 parse_aig (in,dbg_inputs,dbg_outputs,dbg_in_latches,dbg_out_latches,dbg_gates,dbg_ctx->get_manager());

					 for(int k = 0;k<dbg_in_latches.size();k++){
						dbg_ctx->assert_expr(dbg_ctx->get_manager().mk_eq(dbg_out_latches_prev[k],dbg_in_latches[k]));
					}
				}
				for(int j = 0;j<in_latches.size();j++){
					expr* e = in_latches[j];
					ctx2->dbg_map.insert(e,dbg_in_latches[j]);
				}
				for(int j = 0;j<out_latches.size();j++){
					expr* e = out_latches[j];
					ctx2->dbg_map.insert(e,dbg_out_latches[j]);
				}
				for(int j = 0;j<out_latches_prev.size();j++){
					expr* e = out_latches_prev[j];
					ctx2->dbg_map.insert(e,dbg_out_latches_prev[j]);
				}
				for(int j = 0;j<gates.size();j++){
					expr* e = gates[j];
					ctx2->dbg_map.insert(e,dbg_gates[j]);
				}
				ctx2->dbg_solver= dbg_ctx;
				 dbg_any_out = dbg_ctx->get_manager().mk_or(dbg_outputs.size(),dbg_outputs.c_ptr());



				dbg_property = dbg_ctx->get_manager().mk_fresh_const("Property",dbg_ctx->get_manager().mk_bool_sort());
				dbgeq = dbg_ctx->get_manager().mk_eq(dbg_property,dbg_any_out);
				dbg_ctx->assert_expr(dbgeq);


			}
#endif


    	    ctx2->attach(ctx);
    	    expr* any_out = outputs[0];//m->mk_and(outputs.size(),outputs.c_ptr());
    	    for(int i = 0;i<in_latches.size();i++){
    	    	expr* e= ctx2->export_expr(out_latches_prev[i],ctx);
    	    	expr * eq = m->mk_eq(e,in_latches[i]);
    	 	    ctx2->assert_expr(eq);
#ifdef Z3_DEBUG_SMS
    	 	    ctx2->dbg_map.insert(e, dbg_out_latches_prev[i]);
    	 	    ctx2->dbg_map.insert(eq,dbg_ctx->get_manager().mk_true() );
#endif
    	    }

    	    expr * property = ctx2->get_manager().mk_fresh_const("Property",ctx2->get_manager().mk_bool_sort());

    	    expr * eq = ctx2->get_manager().mk_eq(property,any_out);
    	    ctx2->assert_expr(eq);

#ifdef Z3_DEBUG_SMS
    for(int i = 0;i<gates.size();i++){
    	ctx2->dbg_gate_map.insert(gates[i],i);
    }
    ctx2->dbg_gate_map.insert(any_out, gates.size());
    ctx2->dbg_gate_map.insert(property, gates.size());
#endif
#ifdef Z3_DEBUG_SMS
    	 	   ctx2->dbg_map.insert(any_out, dbg_any_out );
    	 	  ctx2->dbg_map.insert(property, dbg_property );
    	 	   ctx2->dbg_map.insert(eq,dbgeq );
#endif

    	      lbool res = ctx2->check_fast(1,&property);

		    result = (res==l_true);
		    ctx = ctx2;
#ifdef Z3_DEBUG_SMS

#endif

    	}


     }else{
     	//this is combinatorial, so we are done
     }

    display_statistics();
    std::cout<<"Result: " << (result? "10":"20")<< " after " << i << " steps" <<"\n";
    exit(result? 10:20);
    return result? 0 : 1;
}

