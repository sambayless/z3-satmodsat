#include "aig_parser.h"
#undef max
#undef min
#include "ast.h"
#include "vector.h"

class stream_buffer {
    std::istream & m_stream;
    int            m_val;
public:

    stream_buffer(std::istream & s):
        m_stream(s) {
        m_val = m_stream.get();
    }

    int  operator *() const {
        return m_val;
    }

    void operator ++() {
        m_val = m_stream.get();
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
static unsigned int parseDelta(unsigned int compare, Buffer& in) {
	//adapted from AIGER specification

    unsigned int x = 0, i = 0;

    unsigned char ch;
    while ((ch = readChar(in)) & 0x80){
      x |= (ch & 0x7f) << (7 * i++);
    }
    SASSERT(i<=4);
    x  |= (ch << (7 * i));

    SASSERT(x<=compare);
    return compare-x;
}






template<typename Buffer>
static void inline buildGate(Buffer & in,  vector<expr*> & gates,  ast_manager& m) {

	unsigned int gateVar = gates.size();

    unsigned int input1 = parseDelta(gateVar*2,in);
    unsigned  int input2 = parseDelta(input1,in);

    SASSERT(input1 < gateVar*2);
    SASSERT(input2 < gateVar*2);

	int in1 =( input1/2);
	bool invert1 = (input1%2);

	int in2 =( input2/2);
	bool invert2 = ( input2%2);

	expr* g1 = gates[in1];
	if(invert1)
		g1 = m.mk_not(g1);
	expr*g2 = gates[in2];
	if(invert2)
		g2 = m.mk_not(g2);

	gates.push_back(m.mk_and(g1,g2));

}

template<typename Buffer>
static bool readHeader(Buffer& in, int & vars, int & inputs, int & latches, int & outputs, int & gates) {

	if(readChar(in) != 'a' || readChar(in) != 'i' || readChar(in) != 'g')
		return false;



	 vars = parse_int(in);
	 inputs = parse_int(in);
	 latches = parse_int(in);
	 outputs = parse_int(in);
	 gates = parse_int(in);

	if(vars<0 || inputs <0 || latches < 0 || outputs<0 || gates <0)
		return false;


	return true;
}

template<typename Buffer>
void parse_aig_core(Buffer & in,vector<expr*>& inputs,vector<expr*> & outputs,vector<expr*> & in_latches, vector<expr*> & out_latches, vector<expr*>& gates, ast_manager & m) {

    int vars;
    int ninputs;
    int nlatches;
    int noutputs;
    int ngates;
    if(!readHeader(in,vars,ninputs, nlatches,noutputs,ngates))
	{
		  std::cerr << "(error, \"bad AIG header\""<< ")\n";
		  exit(3);
		  exit(ERR_PARSER);
    	return;
    }

    outputs.reset();
    inputs.reset();
    in_latches.reset();
    out_latches.reset();
    gates.reset();
    vector<int> output_lits;
    vector<int> nextstate_lits;

    gates.push_back(m.mk_false());//ground

    sort* b = m.mk_bool_sort();
	for(int i = 0;i<ninputs;i++)
	{
		expr* e= m.mk_fresh_const("Input",b);//allocate input vars
		inputs.push_back(e);
		gates.push_back(e);
		m.inc_ref(e);
	}
	for(int i = 0;i<nlatches;i++)
	{
		expr* e= m.mk_fresh_const("Latch_in",b);//allocate latch input vars
		in_latches.push_back(e);
		gates.push_back(e);
		m.inc_ref(e);

		int next_state = parse_int(in);
		nextstate_lits.push_back(next_state);
		SASSERT(*in=='\n');
		++in;//skip the newline
	}
	for(int i = 0;i<noutputs;i++)
	{
		int output = parse_int(in);
		output_lits.push_back(output);
		SASSERT(*in=='\n');
		++in;//skip the newline
	}

	for(int i = 0;i<ngates;i++)
	{
		buildGate(in,gates,m);
	}
	for(int i = 0;i<nextstate_lits.size();i++)
	{
		int next = nextstate_lits[i];
		int var = (next/2);
		bool invert =  (next%2);
		SASSERT(var<gates.size());
		expr * e = gates[var];
		if(invert)
			e= m.mk_not(e);

		out_latches.push_back(e);
		m.inc_ref(e);
	}

	for(int i = 0;i<output_lits.size();i++)
	{
		int out = output_lits[i];
		int var = (out/2);
		bool invert =  (out%2);
		SASSERT(var<gates.size());
		expr * e = gates[var];
		if(invert)
			e= m.mk_not(e);

		outputs.push_back(e);
		m.inc_ref(e);
	}
    return;
}


void parse_aig(std::istream & in,vector<expr*>& inputs,vector<expr*> & outputs,vector<expr*> & in_latches, vector<expr*> & out_latches,vector<expr*> & gates,   ast_manager & m) {
    stream_buffer _in(in);
    parse_aig_core(_in,inputs,outputs,in_latches,out_latches,gates, m);
}
