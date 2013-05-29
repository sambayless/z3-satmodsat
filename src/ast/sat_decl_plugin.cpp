/*
 * sat_decl_plugin.cpp
 *
 *  Created on: May 30, 2013
 *      Author: sam
 */




/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dl_decl_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#include "sat_decl_plugin.h"
#include <sstream>



sat_decl_plugin::sat_decl_plugin(){
	m_sms=NULL;
}


sort * sat_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {

    ast_manager& m = *m_manager;

    return m.mk_sort(symbol("satmodsat"), sort_info(m_family_id, k, num_parameters, parameters));


}
     func_decl * sat_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
    	// if(!m_sms){
    		    func_decl_info info(m_family_id, k);
    		    std::stringstream ss;
    		    ss<<"@" << k;
    		    return m_manager->mk_const_decl(symbol(ss.str().c_str()),m_manager->mk_bool_sort(),info);
    		 //   m_sms = m_manager->mk_func_decl(symbol("@"),m_manager->mk_bool_sort(),m_manager->mk_bool_sort(),info);
    		   // m_manager->inc_ref(m_sms);
    //	 }
    	// ast_manager& m = *m_manager;
    	// return m_sms;
    	 //return m.mk_func_decl(m_family_id,  domain,  func_decl_info(m_family_id, k));
    }

