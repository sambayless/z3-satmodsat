/*
 * aig_parser.h
 *
 *  Created on: Jun 4, 2013
 *      Author: sam
 */

#ifndef AIG_PARSER_H_
#define AIG_PARSER_H_
#include "vector.h"
#include "ast.h"
void parse_aig(std::istream & in,vector<expr*>& inputs,vector<expr*> & outputs,vector<expr*> & in_latches, vector<expr*> & out_latches, vector<expr*> & out_gates,  ast_manager & m);


#endif /* AIG_PARSER_H_ */
