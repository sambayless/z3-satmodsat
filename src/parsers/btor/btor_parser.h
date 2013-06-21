/*
 * aig_parser.h
 *
 *  Created on: Jun 4, 2013
 *      Author: Sam Bayless
 */

#ifndef BTOR_PARSER_H_
#define BTOR_PARSER_H_
#include "vector.h"
#include "ast.h"
void parse_btor(std::istream & in,vector<expr*>& inputs,vector<expr*> & outputs,vector<expr*> & in_latches, vector<expr*> & out_latches, vector<expr*> & out_gates,vector<expr*> & asserted,   ast_manager & m);


#endif /* BTOR_PARSER_H_ */
