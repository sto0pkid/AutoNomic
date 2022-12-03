#include <cassert>
#include <iostream>
#include <locale>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <stdexcept>
#include <stdio.h>
#include <tuple>

#include "univar.h"

#include "jsonld_an.h"

#ifdef with_marpa
#include "marpa_an.h"
#endif

#include "pstreams-0.8.1/pstream.h"


#ifdef debug_cli
#define CLI_TRACE(x) TRACE(x)
#else
#define CLI_TRACE(x)
#endif


/*
 * Globals
 *
 */

// to hold a kb/query string
string qdb_text;


string format = "";
string base = "";

/*
 * Could be local to the input processor?
 */
bool irc = false;

int result_limit = 123;


std::set<string> silence;

bool in_silent_part = false;

std::ostream& dout = std::cout;
std::ostream& derr = std::cerr;
std::istream& din = std::cin;


bool nocolor = false;
bool fnamebase = true;//?

extern bool have_builtins;

std::map<string,bool*> _flags = {
		 {"nocolor",&nocolor}
		,{"deref",&deref}
		,{"irc",&irc}
		,{"shorten",&shorten}
		,{"base",&fnamebase}
		,{"builtins",&have_builtins}
};
typedef std::pair<int*, string> IOP;
std::map<string,IOP> int_flags = {
		  {"level",IOP(&level,"debug level")}
};

std::vector<string> extensions = {"jsonld", "natural3", "natq", "n3", "nq"};
std::vector<string> _formats = {
								#ifdef with_marpa
								"n3",
								#endif
								#ifndef NOPARSER
								"nq",
								#endif
								#ifdef JSON
								"jsonld"
								#endif
};


yprover *anProver = 0;

std::vector<qdb> kbs;

bool done_anything = false;

results_t cppout_results;

/*
 * The structure is essentially the interface for a stack with an undoable
 * "pop". 
 *
 */

class Input
;

enum Mode {COMMANDS, KB, QUERY, SHOULDBE, OLD, RUN};
std::stack<Input *> inputs;
#define INPUT (inputs.top())

class Input
{
public:
	bool interactive = false;
	bool do_reparse = true;
	bool do_cppout = false;
	bool do_query = true;
	bool do_test = false;
	std::string name;
	Mode mode = COMMANDS;
	int limit = 123;//this should be hierarchical tho
	

	virtual string pop() = 0;
	virtual string pop_long() = 0;
	virtual void take_back() = 0;
	virtual void readline()	{};
	virtual bool end() = 0;
	virtual bool done() = 0;

	Input()
	{
		if(inputs.size()) {
			//these should be inherited from parent input
			limit = INPUT->limit;
			do_cppout = INPUT->do_cppout;
			do_query = INPUT->do_query;
			do_test = INPUT->do_test;
		}
	}
};


class ArgsInput : public Input
{
public:
	int argc;
	char **argv;
	int counter = 1;


	ArgsInput(int argc_, char**argv_)
	{
		argc = argc_;
		argv = argv_;
		name = "args";
	}


	bool end()
	{
		return counter == argc;
	}
	bool done()
	{
		return end();
	}
	string pop()
	{
		assert(!end());
		return argv[counter++];
	}
	string pop_long()
	{
		return pop();
	}
	void take_back()
	{
		counter--;
		assert(counter);
	}
};



class StreamInput : public Input
{
public:
	std::istream& stream;
	string line;
	size_t pos;
	std::stack<size_t> starts;

	void figure_out_interactivity()
	{
		//if its a file
		std::ifstream* s = dynamic_cast<std::ifstream*>(&stream);
		interactive = !s;
		//else its stdin
		if (!s) {
			//assert(stream == std::cin);//sometimes doesnt compile
			//but its not attached to a tty
			if (!isatty(fileno(stdin)) && !irc)
				interactive = false;
		}
	}

	StreamInput(string fn_, std::istream& is_) : stream(is_)
	{
		name = fn_;
		figure_out_interactivity();
	}

	~StreamInput(){
		dout << "StreamInput destructor." << std::endl;
	}
	bool done()
	{
		return stream.eof();
	}
	bool end()
	{
		bool r = pop_long() == "";
		take_back();
		return r;
	}

	void readline()
	{
		std::getline(stream, line);
		while(!starts.empty()) starts.pop();
		pos = 0;

		auto m = stream.rdbuf()->in_avail();
		//TRACE(dout << m << endl);
		do_reparse = interactive && m <= 0;
		/* got_more_to_read()? this isnt guaranteed to work.
		 * i would just use select here, like http://stackoverflow.com/a/6171237
		 * got any crossplatform idea?
		 */
	}
	/*
	 * Return the next token from the Stream (starting from `pos`) and place its
	 * start position on the internal stack `starts`.
	 *
	 *
	 */
	string pop_x(char x)
	{

		while(line[pos] == ' ') pos++;
		size_t start = pos;
		while(line[pos] != x && line[pos] != '\n' && line[pos] != 0) pos++;
		size_t end = pos;
		string t = line.substr(start, end);
		starts.push(start);
		return t;
	}
	string pop()
	{
		return pop_x(' ');
	}
	string pop_long()
	{
		return pop_x(0);
	}
	void take_back()
	{
		assert(starts.size());
		pos = starts.top();
		starts.pop();
	}
};















void fresh_prover()
{
	if (anProver)
		delete anProver;
	anProver = new yprover(merge_qdbs(kbs));
}


void set_mode(Mode m)
{
	dout << "#mode = ";
	switch(m) {
		case COMMANDS:
			dout << "commands";
			break;
		case KB:
			dout << "kb";
			break;
		case QUERY:
			dout << "query";
			break;
		case SHOULDBE:
			dout << "shouldbe";
			break;
		case OLD:
			dout << "old";
			break;
		case RUN:
			dout << "run";
			break;
	}
	dout << endl;
	INPUT->mode = m;
}

void help(){
	done_anything = true;
	//FIXME : make this more robust by sticking these strings in vars and removing duplication
	//FIXME : then generalize this so it's just a couple lines
	//FIXME : make this a better help command heh
	if(INPUT->end()){
		dout << "Help -- commands: kb, query, help, quit; use \"help <topic>\" for more detail." << endl;
		dout << "command 'kb': load a knowledge-base." << endl;
		dout << "command 'query': load a query and run." << endl;
		dout << "command 'help': display command descriptions." << endl;
		dout << "command 'quit': exit back to terminal" << endl;
		dout << "\"fin.\" is part of the kb/query-loading, it denotes the end of your rule-base" << endl;
	}
	else{
		string help_arg = INPUT->pop();
		string help_str = "";
		if(help_arg == "kb"){
			help_str = "command 'kb': load a knowledge-base.";
		}
		else if(help_arg == "query"){
			help_str = "command 'query': load a query and run.";
		}
		else if(help_arg == "help"){
			help_str = "command 'help': display command descriptions.";
		}
		else if(help_arg == "quit") {
			help_str = "command 'quit': exit back to terminal";
		}
		else if(help_arg == "fin"){
			help_str = "\"fin.\" is part of the kb/query-loading, it denotes the end of your rule-base";
		}else{
			dout << "No command \"" << help_arg << "\"." << endl;
			return;
		}
		dout << "Help -- " << help_str << endl;
	}
}


void switch_color(){
	if(nocolor){
                KNRM = KRED = KGRN = KYEL = KBLU = KMAG = KCYN = KWHT = "";
	}else{
		KNRM = "\x1B[0m";
		KRED = "\x1B[31m";
		KGRN = "\x1B[32m";
		KYEL = "\x1B[33m";
		KBLU = "\x1B[34m";
		KMAG = "\x1B[35m";
		KCYN = "\x1B[36m";
		KWHT = "\x1B[37m";
	}
}

bool _shouldbe(results_t &results, qdb &sb) {
	if (sb.first.empty() && sb.second.empty()) {
		return results.empty();
	}
	if(!results.size())
		return false;
	auto r = results.front();
	results.pop_front();
	return qdbs_equal(r, sb);
}



void test_result(bool x) {
	dout << INPUT->name << ":test:";
	if (x)
		dout << KGRN << "PASS" << KNRM << endl;
	else
		dout << KRED << "FAIL" << KNRM << endl;
}


void shouldbe(qdb &sb) {
	if (INPUT->do_query) 
		test_result(_shouldbe(anProver->results, sb));
	if (INPUT->do_cppout) {
		bool r = _shouldbe(cppout_results, sb);
		dout << "cppout:";
		test_result(r);
	}
}

void thatsall()
{
	test_result(anProver->results.empty());
}

void clear_kb(){
	kbs.clear();
}


#ifndef NOPARSER
ParsingResult parse_nq(qdb &kb, qdb &query, std::istream &f)
{
	//We can maybe remove this class eventually and just
	//use functions? idk..
	nqparser parser;
        try {
                parser.parse(kb, f);
        } catch (std::exception& ex) {
                derr << "[nq]Error reading quads: " << ex.what() << endl;
                return FAIL;
        }
        try {
                parser.parse(query, f);
        } catch (std::exception& ex) {
                derr << "[nq]Error reading quads: " << ex.what() << endl;
                return FAIL;
        }
        return COMPLETE;
}
#endif



ParsingResult _parse(qdb &kb, qdb &query, std::istream &f, string fmt)
{
	CLI_TRACE(dout << "parse fmt: " << fmt << endl;)
#ifdef with_marpa
	if(fmt == "natural3" || fmt == "n3") {
		//dout << "Supported is a subset of n3 with our fin notation" << endl;
		return parse_natural3(kb, query, f, base);
	}
#endif
#ifndef NOPARSER
	if(fmt == "natq" || fmt == "nq" || fmt == "nquads")
		return parse_nq(kb, query, f);
#endif
#ifdef JSON
	if(fmt == "jsonld"){
		return parse_jsonld(kb, f);
	}
#endif
	return FAIL;
}

string fmt_from_ext(string fn){
	string fn_lc(fn);
        std::locale loc;
	string::size_type fn_len = fn_lc.length();
	for(string::size_type i=0; i<fn_len; ++i)
	 fn_lc[i] = std::tolower(fn_lc[i],loc);
	//boost::algorithm::to_lower(fn_lc);

	for (auto x:extensions){
	 bool is_match = true;
	 string::size_type x_len = x.length();
	 assert(x_len > 0);
	 for(string::size_type i=0;i<x_len; i++){
	  is_match = is_match && (fn_lc[fn_len-1-i] == x[x_len-1-i]);
	  if(!is_match) break;
         }
         if(is_match) return x;
        }
	return "";
}

ParsingResult parse(qdb &kb, qdb &query, std::istream &f, string fn) {
	string fmt = format;
	if (fmt == "")
		fmt = fmt_from_ext(fn);
	if (fmt != "")
		return _parse(kb, query, f, fmt);
	else
	{
		ParsingResult best = FAIL;
		for (auto x : _formats) {
			ParsingResult r = _parse(kb, query, f, x);
			if (r > best)
			{
				if (r==COMPLETE)
					return r;
				best = r;
			}
		}
		return best;
	}
	return FAIL;
}


ParsingResult get_qdb(qdb &kb, string fname){
	std::ifstream is(fname);

	if (!is.is_open()) {
		dout << "failed to open file." << std::endl;
		return FAIL;
	}

	qdb dummy_query;

	auto r = parse(kb, dummy_query, is, fname);
	dout << "qdb graphs count:"<< kb.first.size() << std::endl;

	/*
	int nrules = 0;
	for ( pquad quad :*kb.first["@default"])
		nrules++;
	dout << "rules:" << nrules << std::endl;
	*/

	return r;
}

/*
int count_fins()
{
	int fins = 0;
	std::stringstream ss(qdb_text);
	do {
		string l;
		getline(ss, l);
		if(!ss.good())break;
		std::trim(l);
		if (l == "fin.") fins++;
	}
	return fins;
}
*/
int count_fins()
{
	int fins = 0;
	string line;
	stringstream ss(qdb_text);
	while (!ss.eof()) {
		getline(ss, line);
		if (startsWith(line, "fin") && *wstrim(line.c_str() + 3) == ".")
			fins++;
	}
	return fins;
}

bool dash_arg(string token, string pattern){
	return (token == pattern) || (token == "-" + pattern) || (token == "--" + pattern);
}

/*
void get_int(int &i, const string &tok)
{
	try
	{
		i = std::stoi(tok);
	}
	catch (std::exception& ex)
	{
		dout << "bad int, " << endl;
	}
}
*/





bool read_option(string s){
	if(s.length() < 2 || s.at(0) != '-' || s == "--")
		return false;
	
	while(s.at(0) == '-'){
		s = s.substr(1, s.length()-1);
	}

	string _option = s;

	
	for(string x : _formats){
		if(x == _option){
			format = x;
			dout << "input format:"<<format<<std::endl;
			return true;
		}
	}

	if (!INPUT->end()) {
		string token = INPUT->pop();
	
		if(_option == "silence") {
			silence.emplace(token);
			CLI_TRACE(dout << "silence:";
			for(auto x: silence)
				dout << x << " ";
			dout << endl;)
			return true;
		}


		for( auto x : _flags){
			CLI_TRACE(dout << _option << _option.size() << x.first << x.first.size() << std::endl;)
			if(x.first == _option){
				*x.second = std::stoi(token);
				if(x.first == "nocolor") switch_color();
				return true;
			}
		}


		for( auto x : int_flags){
			if(x.first == _option){
				*x.second.first = std::stoi(token);
				dout << x.second.second << ":" << *x.second.first << std::endl;
				return true;
			}
		}


#define input_option(x, y, z) \
		\
		if(_option == x){ \
			INPUT->y = std::stoi(token); \
			dout << z << ":" << INPUT->y << std::endl; \
			return true; \
		} 

		input_option("cppout", do_cppout, "cppout");
		input_option("lambdas", do_query, "lambdas");
		input_option("test", do_test, "test");
		input_option("limit", limit, "results limit");

		INPUT->take_back();
	}

	return false;
}



void do_run(string fn)
{
	

	std::ifstream &is = *new std::ifstream(fn);
	if (!is.is_open()) {//weird behavior with directories somewhere around here
		dout << "[cli]failed to open \"" << fn << "\"." << std::endl;
	}
	else {
		dout << "[cli]loading \"" << fn << "\"." << std::endl;
		inputs.push(new StreamInput(fn, is));
	}
}



//err...
void run()
{
	set_mode(RUN);
}






void do_query(qdb &q_in)
{
	dout << "query size: " << q_in.first.size() << std::endl;
	result_limit = INPUT->limit;
	anProver->query(q_in);
	done_anything = true;
}


/*
 * Process a query input.
 *
 */
void cmd_query(){
	if(kbs.size() == 0){
		dout << "No kb; cannot query." << endl;
	}else{
		if(INPUT->end()){
			set_mode(QUERY);
		}else{
			if(!INPUT->end()){
				string fn = INPUT->pop_long();
				qdb q_in;
				ParsingResult r = get_qdb(q_in,fn);
				if (r != FAIL)
					do_query(q_in);
			}
		}
	}
}






void add_kb(string fn)
{
	qdb kb;
	ParsingResult r = get_qdb(kb,fn);
	if (r != FAIL)
		kbs.push_back(kb);
}




/*
 * Process a kb input.
 *
 */
void cmd_kb(){
	if(INPUT->end()){
		clear_kb();
		set_mode(KB);
	}else{
		string token = INPUT->pop();
		if(dash_arg(token,"clear")){
			clear_kb();
			return;
		}
		/*else if(dash_arg(token,"set")){
			clear_kb();
		}*/
		//FIXME: this option doesn't work if you have "kb --add" in a file
		else if(dash_arg(token,"add")){
			//dont clear,
			if (INPUT->end())
				throw std::runtime_error("add what?");
			else
				add_kb(INPUT->pop_long());
		}else{
			clear_kb();
			add_kb(token);
		}	
	}
}









//print the prompt string differently to
//specify current mode:
void displayPrompt(){
	if (INPUT->interactive) {
		string prompt;
		switch(INPUT->mode) {
			case OLD:
				prompt = "old";
				break;
			case COMMANDS:
				prompt = "autonomic";
				break;
			case KB:
				prompt = "kb";
				break;
			case RUN:
				prompt = "run";
				break;
			case QUERY:
				prompt = "query";
				break;
			case SHOULDBE:
				prompt = "shouldbe";
				break;
		}
		std::cout << prompt;
		if (format != "")
			std::cout << "["<<format<<"]";
		std::cout << "> ";

	}
}




bool try_to_parse_the_line__if_it_works__add_it_to_qdb_text() //:)
{
	string x = qdb_text + INPUT->pop_long() + "\n";

	if (!INPUT->do_reparse) {
		qdb_text = x;
	}
	else {
		qdb kb, query;
		std::stringstream ss(x);
		int pr = parse(kb, query, ss, "");
		dout << "parsing result:" << pr << std::endl;
		if (pr) {
			qdb_text = x;
		}
		else {
			dout << "[cli]that doesnt parse, try again" << std::endl;
			return false;
		}
	}
	return true;
}









/*
 * Gets run when:
 * 1) An Input is done()
 * 2) The COMMAND is "-"
 * 3) The RUN fn is "-"
 */
StreamInput* emplace_stdin()
{
	auto new_stdin = new StreamInput("stdin", std::cin);
	//inputs.push(new StreamInput("stdin", std::cin));
	inputs.push(new_stdin);
	return new_stdin;
}




void passthru(string s)
{
	std::string line;
	redi::ipstream m(s);
	while (getline(m.out(), line))
		dout << line << endl;
	m.close();
}

bool run_command(){
	string token = INPUT->pop();
	if (startsWith(token, "#") || token == ""){}
	else if (read_option(token)){}
	else if (token == "help" || token == "halp" || token == "hilfe"){
		help();
	}
	else if (token == "kb"){
		cmd_kb();
	}
	else if (token == "query"){
		cmd_query();
	}
	else if (token == "shouldbe")
		set_mode(SHOULDBE);
	else if (token == "thatsall")
		thatsall();
	else if (token == "run")
		run();
	else if (token == "shouldbesteps") {
		//test_result(std::stoi(read_arg()) == anProver->steps_);
	}
	else if (token == "shouldbeunifys") {
		//test_result(std::stoi(read_arg()) == anProver->unifys_);
	}
	else if (token == "quit")
		return false;
		//break;
	else if (token == "-")
		emplace_stdin();
	else {
		INPUT->take_back();
		//maybe its old-style input
		if (try_to_parse_the_line__if_it_works__add_it_to_qdb_text())
			set_mode(OLD);
		else
			dout << "[cli]that doesnt parse, try again" << std::endl;
	}
	return true;

}

void run_code(){
	try_to_parse_the_line__if_it_works__add_it_to_qdb_text();
	int fins = count_fins();
	if (fins > 0) {
		dout << "fin." << std::endl;
		qdb kb,kb2;

		std::stringstream ss(qdb_text);
		auto pr = parse(kb, kb2, ss, INPUT->name);

		if(pr == COMPLETE) {
			if (INPUT->mode == KB) {
				kbs.push_back(kb);
				fresh_prover();
			}
			else if (INPUT->mode == QUERY) {
				if (INPUT->do_query)
					do_query(kb);

				if (INPUT->do_cppout) {
					cppout_results.clear();	
				
					std::string line;

					passthru("sleep 1; rm cppout out.cpp out.o");
					//passthru("sleep 1; astyle out.cpp; rm cppout out.o");

					anProver->cppout(kb);
					stringstream omg;
					omg << "  || echo  \"test:cppout:make:" << KRED << "FAIL:" << KNRM;
					string fff=omg.str();

					dout << "Making cppout." << endl;
					stringstream errss;
					errss << "make -e -f Makefile2 cppout" << fff << INPUT->name << "\"";
					passthru(errss.str());

					dout << "Make done." << endl;
					if (INPUT->do_test)
					{

					stringstream cmdss;
			
					dout << "Running cppout." << endl;	
					cmdss << "./cppout" << fff << INPUT->name << "\"";
					redi::ipstream p(cmdss.str());

					while (getline(p.out(), line)) {
						dout << line << endl;
						if (startsWith(line, "RESULT ")) {
							string result = line.substr(line.find(":") + 1);
							qdb kb, kb2, cppout;
							std::stringstream ss(result);
							auto pr = parse(cppout, kb2, ss, "cppout output");
							cppout_results.push_back(cppout);
						}
					}
					p.close();
					}
				}
				done_anything = true;
			}
			else if (INPUT->mode == SHOULDBE) {
				shouldbe(kb);
			}
		}
		else
			dout << "error" << endl;
		qdb_text = "";
		set_mode(COMMANDS);
	}
}

void run_file(){
	string fn = INPUT->pop_long();
	if (fn == "-")
		emplace_stdin();
	else
		do_run(fn);

}

void run_old(){
	try_to_parse_the_line__if_it_works__add_it_to_qdb_text();

	int fins = count_fins();
	if (fins > 1) {
		kbs.clear();
		qdb kb,kb2;
		std::stringstream ss(qdb_text);
		auto pr = parse(kb, kb2, ss, INPUT->name);
		dout << "querying" << std::endl;
		kbs.push_back(kb);
		fresh_prover();
		do_query(kb2);
		qdb_text = "";
		set_mode(COMMANDS);
	}
}


int main ( int argc, char** argv)
{
	//Initialize the prover strings dictionary with built-in nodes.
	dict.init();


	auto args_input = new ArgsInput(argc, argv);
	std::unique_ptr<ArgsInput> args_input_ptr(args_input);
	std::unique_ptr<StreamInput> stream_input_ptr;

	if(argc > 1){
		inputs.emplace(args_input);
	}else{
		stream_input_ptr = std::unique_ptr<StreamInput>(emplace_stdin());
	}

	/* Looping over...
	 * "Input"s?
	 * "COMMAND"s?  
	 * lines?       in a StreamInput it's lines
	 * "token"s?    in the ArgsInput it's tokens
	 * 
	 * In the ArgsInput it's Tokens
	 * But in a StreamInput it's Lines
	 * But those lines can be "typecast" as Commands
	 *
	 */
	bool continue_processing = true;
	int iteration_index = 0;
	while(continue_processing) {
		iteration_index++;
		/* 
		 * On the first iteration, INPUT->interactive is false, so this won't
		 * display anything.
		 *
		 */
		displayPrompt();

		/* 
		 * On the first iteration, readline() = (){}, so this will have no
		 * effect.
		 *
		 */
		INPUT->readline();


		switch(INPUT->mode) {
			case OLD:
				run_old();
				break;
			case COMMANDS:
				continue_processing = run_command();
				break;
			case KB:
				run_code();
				break;
			case RUN:
				run_file();
				break;
			case QUERY:
				run_code();
				break;
			case SHOULDBE:
				run_code();
				break;
		}



		if(INPUT->done()){
			auto popped = inputs.top();
			inputs.pop();

			/*if there werent any args, drop into repl*/
			if (dynamic_cast<ArgsInput*>(popped))
				if (!done_anything)
					stream_input_ptr = std::unique_ptr<StreamInput>(emplace_stdin()); 

			//delete popped;

		}
		if(!inputs.size()){
			continue_processing = false;
		}
	}

	if (anProver)
		delete anProver;
}
