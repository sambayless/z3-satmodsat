/*
 * sat_decl_plugin.h
 *
 *  Created on: May 30, 2013
 *      Author: sam
 */

#ifndef SAT_DECL_PLUGIN_H_
#define SAT_DECL_PLUGIN_H_



#include"ast.h"



class sat_decl_plugin : public decl_plugin {


public:
	sat_decl_plugin();

    virtual ~sat_decl_plugin() {}
    virtual void finalize(){

    }

    func_decl* m_sms;
    virtual decl_plugin * mk_fresh() { return alloc(sat_decl_plugin); }


    family_id get_family_id() const { return m_family_id; }

    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) ;

    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) ;

};

#endif /* SAT_DECL_PLUGIN_H_ */
