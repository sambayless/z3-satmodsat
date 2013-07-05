#include "btor_parser.h"
#undef max
#undef min
#include "ast.h"
#include "vector.h"
#include "bv_decl_plugin.h"
#include <string>
#include <sstream>
#include <vector>
#include <queue>
#include <map>
#include"well_sorted.h"
class buffered_stream_buffer {
    std::istream & m_stream;
    int            m_val;
    std::deque<int> buf;

public:

    buffered_stream_buffer(std::istream & s):
        m_stream(s),buf() {
        m_val = m_stream.get();

    }

    int  operator *() const {
        return m_val;
    }

    void operator ++() {
    	if(!buf.empty()){
    		m_val=buf.front();
    		buf.pop_front();
    	}else{
    		m_val = m_stream.get();
    	}
    }

    int operator[](int i){
    	if(i==0){
    		return m_val;
    	}else{
    		i--;
    		while(i>=buf.size()){
    			buf.push_back(m_stream.get());
    		}
    		return buf[i];
    	}
    }

};

template<typename Buffer>
void skip_whitespace(Buffer & in) {
    while ((*in >= 9 && *in <= 13) || *in == 32) {
        ++in;
    }
}

template<typename Buffer>
void skip_line(Buffer & in) {
    while(true) {
        if (*in == EOF) {
            return;
        }
        if (*in == '\n') {
            ++in;
            return;
        }
        ++in;
    }
}

template<typename Buffer>
int parse_int(Buffer & in) {
    int     val = 0;
    bool    neg = false;
    skip_whitespace(in);

    if (*in == '-') {
        neg = true;
        ++in;
    }
    else if (*in == '+') {
        ++in;
    }

    if (*in < '0' || *in > '9') {
        std::cerr << "(error, \"unexpected char: " << *in << "\")\n";
        exit(3);
        exit(ERR_PARSER);
    }

    while (*in >= '0' && *in <= '9') {
        val = val*10 + (*in - '0');
        ++in;
    }

    return neg ? -val : val;
}

template<typename Buffer>
int parse_hex(Buffer & in) {
    int     val = 0;
    bool    neg = false;
    skip_whitespace(in);

    if (*in == '-') {
        neg = true;
        ++in;
    }
    else if (*in == '+') {
        ++in;
    }

    if ((*in >= 'a' && *in <= 'f')|| (*in >= 'A' && *in <= 'F')) {

    }else if (*in >= '0' && *in <= '9'){

    }else{
    	 std::cerr << "(error, \"unexpected char: " << *in << "\")\n";
		exit(3);
		exit(ERR_PARSER);
    }

    while ( ((*in >= 'a' && *in <= 'f')|| (*in >= 'A' && *in <= 'F')) || (*in >= '0' && *in <= '9')) {
    	if (*in >= 'a' && *in <= 'f') {
    		  val = val*16 + (10+(*in - 'a'));
    	}else if (*in >= 'A' && *in <= 'F'){
    		  val = val*16 + (10+(*in - 'A'));
		}else if (*in >= '0' && *in <= '9'){
			  val = val*16 + (*in - '0');
		}

        ++in;
    }

    return neg ? -val : val;
}
template<typename Buffer>
int parse_bin(Buffer & in) {
    int     val = 0;
    bool    neg = false;
    skip_whitespace(in);

    if (*in == '-') {
        neg = true;
        ++in;
    }
    else if (*in == '+') {
        ++in;
    }

    if (*in < '0' || *in > '1') {
        std::cerr << "(error, \"unexpected char: " << *in << "\")\n";
        exit(3);
        exit(ERR_PARSER);
    }

    while (*in >= '0' && *in <= '1') {
        val = val*2 + (*in - '0');
        ++in;
    }

    return neg ? -val : val;
}

template<typename Buffer>
static unsigned char readChar( Buffer & in) {
        int i = *in;++in;
        if(i==EOF)
        {
			  std::cerr << "(error, \"unexpected EOF\""<< ")\n";
			  exit(3);
			  exit(ERR_PARSER);
        }
        return i;
}


template<typename Buffer>
static std::string peek_word( Buffer & in) {
       std::stringstream ss;
       skip_whitespace (in);
       int i = 0;
       while (!((in[i] >= 9 && in[i] <= 13) || in[i] == 32)){
    	   if(in[i]==EOF)
    		   break;

    	   //while the character is not whitespace...
    	    ss<<(char)in[i++];

       }

       return ss.str();
}

template<typename Buffer>
static std::string read_word( Buffer & in) {
       std::stringstream ss;
       skip_whitespace (in);

       while (!((*in >= 9 && *in <= 13) || *in == 32)){
    	   if(*in==EOF)
    		   break;
    	   //while the character is not whitespace...
    	    ss<<(char)readChar(in);

       }

       return ss.str();
}

template<typename Buffer>
static bool match(Buffer& in, const char* str) {
	//Adapted from Minisat 2
    int i;
    for (i = 0; str[i] != '\0'; i++)
        if (in[i] != str[i])
            return false;

    for (i = 0; str[i] != '\0'; i++)
    	++in;
    SASSERT(*in==32);
    return true;
}

/*
   OP_BV_NUM,
    OP_BIT1,
    OP_BIT0,
    OP_BNEG,
    OP_BADD,
    OP_BSUB,
    OP_BMUL,

    OP_BSDIV,
    OP_BUDIV,
    OP_BSREM,
    OP_BUREM,
    OP_BSMOD,

    // special functions to record the division by 0 cases
    // these are internal functions
    OP_BSDIV0,
    OP_BUDIV0,
    OP_BSREM0,
    OP_BUREM0,
    OP_BSMOD0,

    // special functions where division by 0 has a fixed interpretation.
    OP_BSDIV_I,
    OP_BUDIV_I,
    OP_BSREM_I,
    OP_BUREM_I,
    OP_BSMOD_I,

    OP_ULEQ,
    OP_SLEQ,
    OP_UGEQ,
    OP_SGEQ,
    OP_ULT,
    OP_SLT,
    OP_UGT,
    OP_SGT,

    OP_BAND,
    OP_BOR,
    OP_BNOT,
    OP_BXOR,
    OP_BNAND,
    OP_BNOR,
    OP_BXNOR,

    OP_CONCAT,
    OP_SIGN_EXT,
    OP_ZERO_EXT,
    OP_EXTRACT,
    OP_REPEAT,

    OP_BREDOR,
    OP_BREDAND,
    OP_BCOMP,

    OP_BSHL,
    OP_BLSHR,
    OP_BASHR,
    OP_ROTATE_LEFT,
    OP_ROTATE_RIGHT,
    OP_EXT_ROTATE_LEFT,
    OP_EXT_ROTATE_RIGHT,

    OP_BUMUL_NO_OVFL, // no unsigned multiplication overflow predicate
    OP_BSMUL_NO_OVFL, // no signed multiplication overflow predicate
    OP_BSMUL_NO_UDFL, // no signed multiplication underflow predicate

    OP_BIT2BOOL, // predicate
    OP_MKBV,     // bools to bv
    OP_INT2BV,
    OP_BV2INT,

    OP_CARRY,
    OP_XOR3,

    LAST_BV_OP
 */
struct bvector{
	expr * bv;
	svector<expr*> bools;
	bvector():bv(NULL){

	}
};
static expr* build_line(int var, expr* e,bvector & b,vector<bvector> & lines,bv_util & bv ){
	if( var<0){
		std::cerr<<"Bad variable " << var << "\n";
		exit(1);
	}
	while(lines.size()<=var){
		lines.push_back(bvector());
	}
	if(lines[var].bv){
		std::cerr<<"Redefined Varaible " << var << "\n";
		exit(1);
	}
	if(!bv.is_bv_sort(bv.get_manager().get_sort(e))){
		SASSERT(bv.get_manager().is_bool(e));//wrap this bool in a 1 bit bitvector
		e = bv.mk_bv(1,&e);
	}
	if(!is_well_sorted(bv.get_manager(), e)){
		std::cerr<<"Incompatible bitvector operations.\n";
		exit(1);
	}

	b.bv = e;
	lines[var]=b;
	return lines[var].bv;
}

static expr* get_line(int var,vector<bvector> & lines,  ast_manager& m ){
	bool negate = false;
	if(var<0){
		var=-var;
		negate=true;
	}

	if(var>=lines.size() || var==0){
		std::cerr<<"Undefined variable " << var << "\n";
		exit(1);
	}
	if(negate){
		 return m.mk_app(m.get_family_id("bv"), OP_BNOT, lines[var].bv);
		//return m.mk_not( lines[var]);
	}else
		return lines[var].bv;
}


template<typename Buffer>
static void inline read_line(Buffer & in,vector<bvector> & inputs,vector<bvector> &outputs,vector<bvector> &in_latches,vector<bvector> &out_latches, vector<bvector> & gates, vector<expr*> & asserted, ast_manager& m) {
	int var = parse_int(in);
	if(var<0){
		std::cerr<<"Bad variable ID " << var <<"\n";
		exit(1);
	}
	//this could be done more efficiently with a proper parser, of course...

	 family_id fid = m.get_family_id("bv");
	 bv_decl_plugin & bv_decl =*(bv_decl_plugin*) m.get_plugin(fid);
	 bv_util bv(m);

	 expr * e=NULL;
	 bvector b;b.bv=NULL;
	 skip_whitespace(in);

	//input variable
	 int bit_width=-1;
	if(match(in,"var")){
		bit_width =  parse_int(in);
		std::string s = read_word(in);
		const char * name = s.c_str();
		expr * vars [bit_width];
		for(int i = 0;i<bit_width;i++){
			vars[i]= m.mk_fresh_const(name,m.mk_bool_sort());
			m.inc_ref(vars[i]);
		}
		e= bv.mk_bv(bit_width,vars);

		b.bv= e;
		b.bools.append(bit_width,vars);
		inputs.push_back(b);
	}
	//latch
	else if (match(in,"next")){
		bit_width =  parse_int(in);
		int inputVar = parse_int(in);
		SASSERT(inputVar>0);
		int nextFunc = parse_int(in);
		expr* inExp = get_line(inputVar,gates,m);
		e = get_line(nextFunc,gates,m);
			int bit_width = bv.get_bv_size(e);
			expr * vars [bit_width];
			for(int i = 0;i<bit_width;i++){
				vars[i]= m.mk_fresh_const("output",m.mk_bool_sort());
				m.inc_ref(vars[i]);
			}
			expr * e_cpy = bv.mk_bv(bit_width,vars);
			asserted.push_back(m.mk_eq(e, e_cpy));

			in_latches.push_back(gates[inputVar]);


			b.bv= e_cpy;
			b.bools.append(bit_width,vars);
			out_latches.push_back(b);
	}
	//Circuit output
	else if(match(in,"root")){
		bit_width =  parse_int(in);
		int invar = parse_int(in);
		e = get_line(invar,gates,m);

		int bit_width = bv.get_bv_size(e);
		expr * vars [bit_width];
		for(int i = 0;i<bit_width;i++){
			vars[i]= m.mk_fresh_const("output",m.mk_bool_sort());
			m.inc_ref(vars[i]);
		}
		expr * e_cpy = bv.mk_bv(bit_width,vars);
		asserted.push_back(m.mk_eq(e, e_cpy));


		b.bv= e_cpy;
		b.bools.append(bit_width,vars);
		outputs.push_back(b);
	}else if(match(in,"one")){
		//1
		bit_width =  parse_int(in);
		int val =  1;

		e= bv.mk_numeral(val,bit_width);
	}else if(match(in,"ones")){
		//-1 (which in twos complement is 11111...)
		bit_width =  parse_int(in);
		int val =  -1;

		e= bv.mk_numeral(val,bit_width);
	}else if(match(in,"zero")){
		//0
		bit_width =  parse_int(in);
		int val =  0;

		e= bv.mk_numeral(val,bit_width);

	}else if(match(in,"constd")){
		//decimal constant
		bit_width =  parse_int(in);
		int val =  parse_int(in);//value in decimal

		e= bv.mk_numeral(val,bit_width);

	}else if(match(in,"consth")){
		//hex constant
		bit_width =  parse_int(in);
		int val =  parse_hex(in);//value in decimal

		e= bv.mk_numeral(val,bit_width);

	}else if(match(in,"const")){
		//binary constant
		bit_width = parse_int(in);
		int val =  parse_bin(in);//value in decimal
		e= bv.mk_numeral(val,bit_width);
	}
	//Unary Operators
	else if (match(in,"not")){
		bit_width =  parse_int(in);
		int invar = parse_int(in);
		e=bv.mk_bv_not(get_line(invar,gates,m));
	}else if (match(in,"neg")){
		bit_width =  parse_int(in);
		int invar = parse_int(in);
		e=bv.mk_bv_neg(get_line(invar,gates,m));
	}else if (match(in,"redand")){
		bit_width =  parse_int(in);
		int invar = parse_int(in);
		e= m.mk_app(fid, OP_BREDAND, get_line(invar,gates,m));
	}else if (match(in,"redor")){
		bit_width =  parse_int(in);
		int invar = parse_int(in);
		e= m.mk_app(fid, OP_BREDOR, get_line(invar,gates,m));
	}else if (match(in,"redxor")){
		//ie, parity
		bit_width =  parse_int(in);
		int invar = parse_int(in);
		expr * from = get_line(invar,gates,m);
		e = bv.mk_extract(0,1,from);
		for(int i = 1;i<bit_width-1;i++){
			expr * cur = bv.mk_extract(i,i+1,from);
			expr * next = m.mk_xor(e,cur);
			m.dec_ref(e);
			m.dec_ref(cur);
			e = next;
		}

	}else if (match(in,"inc")){
		bit_width =  parse_int(in);
		int invar = parse_int(in);
		expr * from = get_line(invar,gates,m);

		e= bv.mk_bv_add(from,bv.mk_numeral(bit_width,1) );

	}else if (match(in,"dec")){
		bit_width =  parse_int(in);
		int invar = parse_int(in);
		expr * from = get_line(invar,gates,m);
		e= bv.mk_bv_sub(from,bv.mk_numeral(bit_width,1) );
	}
	//Binary operators
	else if (match(in,"and")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_app(fid, OP_BAND, fromA, fromB);
		//e= m.mk_and(fromA,fromB);
	}else if (match(in,"or")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_app(fid, OP_BOR, fromA, fromB);
	}else if (match(in,"xor")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_app(fid, OP_BXOR, fromA, fromB);
	}else if (match(in,"nand")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		//e= m.mk_not( m.mk_and(fromA,fromB));
		e= m.mk_app(fid, OP_BNAND, fromA, fromB);
	}else if (match(in,"nor")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_app(fid, OP_BNOR, fromA, fromB);
	}else if (match(in,"xnor")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_app(fid, OP_BXNOR, fromA, fromB);
	}else if (match(in,"implies")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_implies(fromA,fromB);
	}else if (match(in,"iff")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_iff(fromA,fromB);
	}
	//arithmetic
	else if (match(in,"add")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= bv.mk_bv_add(fromA,fromB);
	}else if (match(in,"sub")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= bv.mk_bv_sub(fromA,fromB);
	}else if (match(in,"mul")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= bv.mk_bv_mul(fromA,fromB);
	}else if (match(in,"urem")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= bv.mk_bv_urem(fromA,fromB);
	}else if (match(in,"srem")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= bv.mk_bv_srem(fromA,fromB);
	}else if (match(in,"udiv")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_app(fid, OP_BUDIV, fromA, fromB);

	}else if (match(in,"sdiv")){
		bit_width =  parse_int(in);
			int invarA = parse_int(in);
			int invarB = parse_int(in);
			expr * fromA = get_line(invarA,gates,m);
			expr * fromB = get_line(invarB,gates,m);
			e= m.mk_app(fid, OP_BSDIV, fromA, fromB);
	}else if (match(in,"smod")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_app(fid, OP_BSMOD, fromA, fromB);
	}
	//relational
	else if (match(in,"eq")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);

		e= m.mk_eq(fromA,fromB);
	}else if (match(in,"ne")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_not( m.mk_eq(fromA,fromB));
	}else if (match(in,"ulte")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= bv.mk_ule(fromA,fromB);
		expr * cpy = m.mk_fresh_const("copy", m.mk_bool_sort());
		asserted.push_back(m.mk_eq(cpy,e));
		e =  bv.mk_bv(1, &cpy);
	}else if (match(in,"slte")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e=  m.mk_app(fid, OP_SLEQ, fromA, fromB);
		expr * cpy = m.mk_fresh_const("copy", m.mk_bool_sort());
		asserted.push_back(m.mk_eq(cpy,e));
		e =  bv.mk_bv(1, &cpy);
	}else if (match(in,"ugte")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e=  m.mk_app(fid, OP_UGEQ, fromA, fromB);
		expr * cpy = m.mk_fresh_const("copy", m.mk_bool_sort());
		asserted.push_back(m.mk_eq(cpy,e));
				e =  bv.mk_bv(1, &cpy);
	}else if (match(in,"sgte")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e=  m.mk_app(fid, OP_SGEQ, fromA, fromB);
		expr * cpy = m.mk_fresh_const("copy", m.mk_bool_sort());
				asserted.push_back(m.mk_eq(cpy,e));
				e =  bv.mk_bv(1, &cpy);
	}else if (match(in,"ult")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e=  m.mk_app(fid, OP_ULT, fromA, fromB);
		expr * cpy = m.mk_fresh_const("copy", m.mk_bool_sort());
				asserted.push_back(m.mk_eq(cpy,e));
				e =  bv.mk_bv(1, &cpy);
	}else if (match(in,"slt")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e=  m.mk_app(fid, OP_SLT, fromA, fromB);
		expr * cpy = m.mk_fresh_const("copy", m.mk_bool_sort());
				asserted.push_back(m.mk_eq(cpy,e));
				e =  bv.mk_bv(1, &cpy);
	}else if (match(in,"ugt")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= m.mk_app(fid, OP_UGT, fromA, fromB);
		expr * cpy = m.mk_fresh_const("copy", m.mk_bool_sort());
				asserted.push_back(m.mk_eq(cpy,e));
				e =  bv.mk_bv(1, &cpy);
	}else if (match(in,"sgt")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e=  m.mk_app(fid, OP_SGT, fromA, fromB);
		expr * cpy = m.mk_fresh_const("copy", m.mk_bool_sort());
				asserted.push_back(m.mk_eq(cpy,e));
				e =  bv.mk_bv(1, &cpy);
	}
	//shift
	else if (match(in,"sll")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);

		int aWidth = bv.get_bv_size(fromA);
			int bWidth = bv.get_bv_size(fromB);
			if(bWidth != aWidth){
				SASSERT(bWidth<aWidth);
				expr * b_ext = bv.mk_zero_extend(aWidth-bWidth, fromB);
				e= bv.mk_bv_shl(fromA,b_ext);
			}else{
				e= bv.mk_bv_shl(fromA,fromB);
			}
	}else if (match(in,"srl")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		int aWidth = bv.get_bv_size(fromA);
		int bWidth = bv.get_bv_size(fromB);
		if(bWidth != aWidth){
			SASSERT(bWidth<aWidth);
			expr * b_ext = bv.mk_zero_extend(aWidth-bWidth, fromB);
			e= bv.mk_bv_lshr(fromA,b_ext);
		}else{
			e= bv.mk_bv_lshr(fromA,fromB);
		}

	}else if (match(in,"sra")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		int aWidth = bv.get_bv_size(fromA);
		int bWidth = bv.get_bv_size(fromB);
		if(bWidth != aWidth){
			SASSERT(bWidth<aWidth);
			expr * b_ext = bv.mk_zero_extend(aWidth-bWidth, fromB);
			e= bv.mk_bv_ashr(fromA,b_ext);
		}else{
			e= bv.mk_bv_ashr(fromA,fromB);
		}
	}else if (match(in,"ror")){
		std::cerr<<"rol is not supported yet!\n";
				exit(1);
	}else if (match(in,"rol")){
		std::cerr<<"rol is not supported yet!\n";
		exit(1);
	}
	//overflow
	else if (match(in,"uadddo")){
		std::cerr<<"overflow detection is not supported yet!\n";
			exit(1);

	}else if (match(in,"sadddo")){
		std::cerr<<"overflow detection is not supported yet!\n";
					exit(1);
	}else if (match(in,"usubo")){
		std::cerr<<"overflow detection is not supported yet!\n";
					exit(1);
	}else if (match(in,"ssubo")){
		std::cerr<<"overflow detection is not supported yet!\n";
					exit(1);
	}else if (match(in,"umulo")){
		std::cerr<<"overflow detection is not supported yet!\n";
					exit(1);
	}else if (match(in,"smulo")){
		std::cerr<<"overflow detection is not supported yet!\n";
					exit(1);
	}else if (match(in,"sdivo")){
		std::cerr<<"overflow detection is not supported yet!\n";
					exit(1);
	}else if (match(in,"concat")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		e= bv.mk_concat(fromA,fromB);
	}
	//ternary
	else if (match(in,"cond")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int invarB = parse_int(in);
		int invarC = parse_int(in);
		expr * fromA = get_line(invarA,gates,m);
		expr * fromB = get_line(invarB,gates,m);
		expr * fromC = get_line(invarC,gates,m);
		expr * cond = m.mk_not( m.mk_eq(fromA, bv.mk_numeral(0, bv.get_bv_size(fromA))));
		e = m.mk_ite (cond,fromB, fromC);
	}
	//bitvector
	else if (match(in,"slice")){
		bit_width =  parse_int(in);
		int invarA = parse_int(in);
		int upper = parse_int(in);
		int lower = parse_int(in);
		expr * from = get_line(invarA,gates,m);
		e = bv.mk_extract (upper, lower,from);
	}
	//arrays
	else if (match(in,"array")){
		std::cerr<<"Arrays are not supported yet!\n";
							exit(1);
	}else if (match(in,"read")){
		std::cerr<<"Arrays are not supported yet!\n";
									exit(1);
	}else if (match(in,"write")){
		std::cerr<<"Arrays are not supported yet!\n";
									exit(1);
	}else if (match(in,"acond")){
		std::cerr<<"Arrays are not supported yet!\n";
									exit(1);
	}else{
		std::cerr<<"Unsupported boolector operation " << read_word(in) << "\n";
		exit(1);
	}

	SASSERT(asserted.empty() || m.is_bool(asserted.back()));

	if(e){
		if(!is_well_sorted(bv.get_manager(), e)){
			std::cerr<<"Incompatible bitvector operations.\n";
			exit(1);
		}

		int actual_width = 1;
		if(bv.is_bv_sort(m.get_sort(e)))
			actual_width =bv.get_bv_size(e);
		SASSERT(actual_width==bit_width || bit_width<0);
		build_line(var,e,b,gates,bv);
	}
}


template<typename Buffer>
void parse_btor_core(Buffer & in,vector<expr*>& inputs,vector<expr*> & outputs,vector<expr*> & in_latches, vector<expr*> & out_latches, vector<expr*>& gates, vector<expr*> & asserted, ast_manager & m) {


    outputs.reset();
    inputs.reset();
    in_latches.reset();
    out_latches.reset();
    gates.reset();
    asserted.reset();
    vector<int> output_lits;
    vector<int> nextstate_lits;

    vector<bvector> inputs_bv;
    vector<bvector> outputs_bv;
    vector<bvector> in_latches_bv;
    vector<bvector> out_latches_bv;
    vector<bvector> gates_bv;

    gates_bv.push_back(bvector());//gates start at index 1

    for (;;){
    	skip_whitespace(in);
        if (*in == EOF) break;
        else if (*in == ';'){
            skip_line(in);//this is a comment
	   }else{
		   read_line(in,inputs_bv,outputs_bv,in_latches_bv,out_latches_bv,gates_bv,asserted,m);
       }
    }


    for(int i = 0;i<inputs_bv.size();i++){
    	for(int j = 0;j<inputs_bv[i].bools.size();j++)
    		inputs.push_back(inputs_bv[i].bools[j]);
    }

    for(int i = 0;i<outputs_bv.size();i++){
       	for(int j = 0;j<outputs_bv[i].bools.size();j++)
       		outputs.push_back(outputs_bv[i].bools[j]);
       }


    for(int i = 0;i<in_latches_bv.size();i++){
       	for(int j = 0;j<in_latches_bv[i].bools.size();j++)
       		in_latches.push_back(in_latches_bv[i].bools[j]);
       }

    for(int i = 0;i<out_latches_bv.size();i++){
          	for(int j = 0;j<out_latches_bv[i].bools.size();j++)
          		out_latches.push_back(out_latches_bv[i].bools[j]);
          }

    for(int i = 0;i<gates_bv.size();i++){
		for(int j = 0;j<gates_bv[i].bools.size();j++)
			gates.push_back(gates_bv[i].bools[j]);
	   }

    SASSERT(out_latches.size()==in_latches.size());

    ptr_addr_map<expr, bool> latchset;

    for(int i = 0;i<in_latches.size();i++){
    	latchset.insert(in_latches[i],true);
    }
    int i, j=0;
    for(i =0;i< inputs.size();i++){
    	if(!latchset.contains(inputs[i])){
    		inputs[j++]=inputs[i];
    	}
    }
    inputs.shrink(inputs.size() -( i-j));
    return;
}


void parse_btor(std::istream & in,vector<expr*>& inputs,vector<expr*> & outputs,vector<expr*> & in_latches, vector<expr*> & out_latches,vector<expr*> & gates, vector<expr*> & asserted,   ast_manager & m) {
	buffered_stream_buffer _in(in);
    parse_btor_core(_in,inputs,outputs,in_latches,out_latches,gates, asserted,m);
}
