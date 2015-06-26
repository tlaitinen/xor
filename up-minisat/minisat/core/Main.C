/******************************************************************************************[Main.C]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <ctime>
#include <cstring>
#include <stdint.h>
#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "Solver.h"

/*************************************************************************************/
#ifdef _MSC_VER
#include <ctime>

static inline double cpuTime(void) {
    return (double)clock() / CLOCKS_PER_SEC; }
#else

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }
#endif


#if defined(__linux__)
static inline int memReadStat(int field)
{
    char    name[256];
    pid_t pid = getpid();
    sprintf(name, "/proc/%d/statm", pid);
    FILE*   in = fopen(name, "rb");
    if (in == NULL) return 0;
    int     value;
    for (; field >= 0; field--) {

        int ret __attribute__((unused)) = fscanf(in, "%d", &value);
    }
    fclose(in);
    return value;
}
static inline uint64_t memUsed() { return (uint64_t)memReadStat(0) * (uint64_t)getpagesize(); }


#elif defined(__FreeBSD__)
static inline uint64_t memUsed(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss*1024; }


#else
static inline uint64_t memUsed() { return 0; }
#endif

#if defined(__linux__)
#include <fpu_control.h>
#endif

//=================================================================================================
// DIMACS Parser:

#define CHUNK_LIMIT 1048576

class StreamBuffer {
    gzFile  in;
    char    buf[CHUNK_LIMIT];
    int     pos;
    int     size;

    void assureLookahead() {
        if (pos >= size) {
            pos  = 0;
            size = gzread(in, buf, sizeof(buf)); } }

public:
    StreamBuffer(gzFile i) : in(i), pos(0), size(0) {
        assureLookahead(); }

    int  operator *  () { return (pos >= size) ? EOF : buf[pos]; }
    void operator ++ () { pos++; assureLookahead(); }
};

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

template<class B>
static void skipWhitespace(B& in) {
    while ((*in >= 9 && *in <= 13) || *in == 32)
        ++in; }

template<class B>
static void skipLine(B& in) {
    for (;;){
        if (*in == EOF || *in == '\0') return;
        if (*in == '\n') { ++in; return; }
        ++in; } }

template<class B>
static int parseInt(B& in) {
    int     val = 0;
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    if (*in < '0' || *in > '9') reportf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    while (*in >= '0' && *in <= '9')
        val = val*10 + (*in - '0'),
        ++in;
    return neg ? -val : val; }

template<class B>
static void readClause(B& in, Solver& S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        while (var >= S.nVars()) S.newVar();
        lits.push( (parsed_lit > 0) ? Lit(var) : ~Lit(var) );
    }
}

template<class B>
static bool match(B& in, const char* str) {
    for (; *str != 0; ++str, ++in)
        if (*str != *in)
            return false;
    return true;
}


template<class B>
static void parse_DIMACS_main(B& in, Solver& S) {
    vec<Lit> lits;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF)
            break;
        else if (*in == 'p'){
            if (match(in, "p ") && *in == 'c' && match(in, "cnf")) {
                int vars    = parseInt(in);
                int clauses = parseInt(in);
                reportf("|  Number of variables:  %-12d                                         |\n", vars);
                reportf("|  Number of clauses:    %-12d                                         |\n", clauses);
            } else if (match(in, "xcnf")) {
                int vars    = parseInt(in);
                int clauses = parseInt(in);
                reportf("|  Number of variables:        %-12d                                   |\n", vars);
                reportf("|  Number of clauses (CNF):    %-12d                                   |\n", clauses);
                reportf("|  Input may contain XOR-clauses                                       |\n");
            } else{
                reportf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p') {
#ifdef VERIFY
            if (*in == 'c') {

                ++in;
                skipWhitespace(in);
                if (*in == '-' || isdigit(*in)) {
                    int lit = parseInt(in);
//                    reportf("got model lit %d\n", lit);
                }

            } 


#endif

               skipLine(in);
            }else {
            bool isXor = match(in, "x");

            readClause(in, S, lits);
            if (isXor)
                S.addXorClause(lits);
            else
                S.addClause(lits);
        }
    }
}

// Inserts problem into solver.
//
static void parse_DIMACS(gzFile input_stream, Solver& S) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, S); }


//=================================================================================================


void printStats(Solver& solver, StopWatch& totalTime)
{
    double   cpu_time = cpuTime();
    uint64_t mem_used = memUsed();
    reportf("restarts               : %llu\n", (long long unsigned) solver.starts);
    reportf("conflicts              : %-12llu   (%.0f /sec)\n", (long long unsigned) solver.conflicts   , solver.conflicts   /cpu_time);
    reportf("decisions              : %-12llu   (%4.2f %% random) (%.0f /sec)\n", (long long unsigned) solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    reportf("propagations           : %-12llu   (%.0f /sec)\n", (long long unsigned) solver.propagations, solver.propagations/cpu_time);
   up::XorModule& up = solver.upModule;

    reportf("UP-xor assumptions     : %-12lld\n", up.stats.assumptions);
    reportf("UP-xor implied         : %-12lld\n", up.stats.implied);
    reportf("UP-xor conflicts       : %-12lld\n", up.stats.conflicts);
    reportf("UP-xor learnts         : %-12lld\n", up.stats.learnts);
    if (up.stats.learnts)
        reportf("UP-xor learnt size     : %.2f\n", (float) up.stats.learntLits / (float) up.stats.learnts);
    reportf("UP-xor explained       : %-12lld\n", up.stats.explained);
    reportf("UP-xor deep cuts       : %-12lld\n", up.stats.deepCuts);
    reportf("UP-xor cached exp.     : %-12lld\n", up.stats.cachedExplained);
    reportf("total time             : %-12g\n", ((double) totalTime.total()) / ((double) 1000000000.0) );
    reportf("xor time               : %-12g\n", ((double) solver.xorTime.total()) / ((double) 1000000000.0));

    if (up.stats.explained) {
        reportf("UP-xor exp. length     : %.2f\n", (float) up.stats.explanationLits / up.stats.explained);
    } 
    if (up.stats.deepCuts) {
        reportf("UP-xor deep exp. length: %.2f\n", (float) up.stats.deepExpLits / up.stats.deepCuts);

    }
    if (up.stats.deepCuts) {

        reportf("UP-xor even eliminated : %.2f\n", (float) up.stats.evenElimLits / up.stats.deepCuts);
    }
    reportf("UP-xor auto-learned    : %-12lld\n", up.stats.autoLearned);







    reportf("conflict literals      : %-12llu   (%4.2f %% deleted)\n", (long long unsigned) solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    if (mem_used != 0) reportf("Memory used            : %.2f MB\n", mem_used / 1048576.0);
    reportf("CPU time               : %g s\n", cpu_time);
}

Solver* solver;
static void SIGINT_handler(int signum) {
    StopWatch stopWatch;
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    printStats(*solver, stopWatch);
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    exit(1); }


//=================================================================================================
// Main:

void printUsage(char** argv)
{
    Solver      S;
    reportf("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n\n", argv[0]);
    reportf("OPTIONS:\n\n");
    reportf("  -polarity-mode       = {true,false,rnd}      default: false\n");
    reportf("  -xor-propagation     = {eager,lazy}          default: %s\n", (S.xor_propagation == Solver::xor_propagation_eager) ? "eager" : "lazy");
    reportf("  -xor-lazy-factor     = <num> [ 1 - N ]       default: %d\n", S.xor_lazy_factor);
    reportf("  -xor-rule-priority   = {external,internal}   default: %s\n", (S.xor_rule_priority == Solver::xor_rule_priority_internal) ? "internal" : "external" );
    reportf("  -xor-store-clauses   = {true,false}          default: %s\n", (S.xor_store_clauses) ? "true" : "false");
    reportf("  -xor-exp-length      = <num> [ 3 - N ]       default: %d\n", S.xor_exp_length);
    reportf("  -xor-bump-activity   = {0,1,2}               default: %d\n", S.xor_bump_activity);
    reportf("  -xor-even-elim       = {true,false}          default: %s\n", S.xor_even_elim ? "true" : "false");
    reportf("  -xor-create-vars     = {true,false}          default: %s\n", S.xor_create_vars ? "true" : "false");
    reportf("  -xor-to-cnf          = {true,false}          default: %s\n", S.xor_to_cnf ? "true" : "false");
    reportf("  -xor-deep-cuts       = {true,false}]         default: %s\n", S.xor_deep_cuts ? "true" : "false");
    reportf("  -xor-1uip-cuts       = {true,false}          default: %s\n", S.xor_1uip_cuts ? "true" : "false");
    reportf("  -xor-store-exp       = <num> [ 3 - N ]       default: %d\n", S.xor_store_exp);
    reportf("  -xor-tree-exp        = {true,false}          default: %s\n", S.xor_tree_exp ? "true" : "false");
    reportf("  -xor-learn-all       = {true,false}          default: %s\n", S.xor_learn_all ? "true" : "false");
    reportf("  -log-conflicts       = <PATH>                default: off\n");
    reportf("  -decay               = <num> [ 0 - 1 ]\n");
    reportf("  -rnd-freq            = <num> [ 0 - 1 ]\n");
    reportf("  -verbosity           = {0,1,2}\n");
    reportf("  -learn-factor        = <float>             default: 0.3\n");
    reportf("\n");
}


const char* hasPrefix(const char* str, const char* prefix)
{
    int len = strlen(prefix);
    if (strncmp(str, prefix, len) == 0)
        return str + len;
    else
        return NULL;
}


int main(int argc, char** argv)
{
    StopWatch totalTime;
    totalTime.start();
    Solver      S;
    S.verbosity = 1;


    int         i, j;
    const char* value;
    for (i = j = 0; i < argc; i++){
        if ((value = hasPrefix(argv[i], "-polarity-mode="))){
            if (strcmp(value, "true") == 0)
                S.polarity_mode = Solver::polarity_true;
            else if (strcmp(value, "false") == 0)
                S.polarity_mode = Solver::polarity_false;
            else if (strcmp(value, "rnd") == 0)
                S.polarity_mode = Solver::polarity_rnd;
            else{
                reportf("ERROR! unknown polarity-mode %s\n", value);
                exit(0); }

        }else if ((value = hasPrefix(argv[i], "-xor-propagation="))) {
            if (strcmp(value, "eager") == 0)
                S.xor_propagation = Solver::xor_propagation_eager;
            else if (strcmp(value, "lazy") == 0)
                S.xor_propagation = Solver::xor_propagation_lazy;
            else{
                reportf("ERROR! unknown xor-propagation %s\n", value);
                exit(0); }
        }else if ((value = hasPrefix(argv[i], "-xor-lazy-factor="))) {
            S.xor_lazy_factor = atoi(value);
            if (S.xor_lazy_factor == 0) {
                reportf("ERROR! invalid xor-lazy-factor %s\n", value);
                exit(0); }
        }else if ((value = hasPrefix(argv[i], "-xor-rule-priority="))) {
            if (strcmp(value, "external") == 0) 
                S.xor_rule_priority = Solver::xor_rule_priority_external;
            else if (strcmp(value, "internal") == 0)
                S.xor_rule_priority = Solver::xor_rule_priority_internal;
            else {
                reportf("ERROR! unknown xor-rule-priority %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-xor-internal-vars="))) {
            if (strcmp(value, "on") == 0)
                S.xor_internal_vars = true;
            else if (strcmp(value, "off") == 0)
                S.xor_internal_vars = false;
            else {
                reportf("ERROR! unknown xor-internal-vars %s\n", value);
                exit(0);
            }
                        
        }else if ((value = hasPrefix(argv[i], "-xor-store-clauses="))) {
            if (strcmp(value, "true") == 0)
                S.xor_store_clauses = true;
            else if (strcmp(value, "false") == 0)
                S.xor_store_clauses = false;
            else {
                reportf("ERROR! unknown xor-store-clauses %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-xor-to-cnf="))) {
            if (strcmp(value, "true") == 0)
                S.xor_to_cnf = true;
            else if (strcmp(value, "false") == 0)
                S.xor_to_cnf = false;
            else {
                reportf("ERROR! unknown xor-to-cnf %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-xor-exp-length="))) {
            S.xor_exp_length = atoi(value);
            if (S.xor_exp_length < 2) {
                reportf("ERROR! invalid xor-exp-length %s\n", value);
                exit(0);
            }

        }else if ((value = hasPrefix(argv[i], "-xor-bump-activity="))) {
            if (strcmp(value, "1") == 0)
                S.xor_bump_activity = 1;
            else if (strcmp(value, "2") == 0)
                S.xor_bump_activity = 2;
            else if (strcmp(value, "0") == 0)
                S.xor_bump_activity = 0;
            else {
                reportf("ERROR! unknown xor-bump-activity %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-xor-even-elim="))) {
            if (strcmp(value, "true") == 0)
                S.xor_even_elim = true;
            else if (strcmp(value, "false") == 0)
                S.xor_even_elim = false;
            else {
                reportf("ERROR! unknown xor-even-elim %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-xor-create-vars="))) {
            if (strcmp(value, "true") == 0)
                S.xor_create_vars = true;
            else if (strcmp(value, "false") == 0)
                S.xor_create_vars = false;
            else {
                reportf("ERROR! unknown xor-create-vars %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-xor-deep-cuts="))) {
            if (strcmp(value, "true") == 0)
                S.xor_deep_cuts = true;
            else if (strcmp(value, "false") == 0)
                S.xor_deep_cuts = false;
            else {
                reportf("ERROR! unknown xor-deep-cuts %s\n", value);
                exit(0);
            }

        } else if ((value = hasPrefix(argv[i], "-xor-1uip-cuts="))) {
            if (strcmp(value, "true") == 0)
                S.xor_1uip_cuts = true;
            else if (strcmp(value, "false") == 0)
                S.xor_1uip_cuts = false;
            else {
                reportf("ERROR! unknown xor-1uip-cuts %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-xor-store-exp="))) {
            S.xor_store_exp = atoi(value);
            if (S.xor_store_exp < 2 && S.xor_store_exp != 0) {
                reportf("ERROR! invalid xor-store-exp %s\n", value);
                exit(0);
            }

        } else if ((value = hasPrefix(argv[i], "-xor-tree-exp="))) {
            if (strcmp(value, "true") == 0)
                S.xor_tree_exp = true;
            else if (strcmp(value, "false") == 0)
                S.xor_tree_exp = false;
            else {
                reportf("ERROR! unknown xor-deep-cuts %s\n", value);
                exit(0);
            }
        } 
 else if ((value = hasPrefix(argv[i], "-xor-learn-all="))) {
            if (strcmp(value, "true") == 0)
                S.xor_learn_all = true;
            else if (strcmp(value, "false") == 0)
                S.xor_learn_all = false;
            else {
                reportf("ERROR! unknown xor-learn-all %s\n", value);
                exit(0);
            }
        } 
        
        else if ((value = hasPrefix(argv[i], "-log-conflicts="))) {
           S.conflictLog = fopen(value, "w");
           if (!S.conflictLog) {
               reportf("ERROR! could not open file '%s'\n", value);
               exit(0);
           }
        }
        else if ((value = hasPrefix(argv[i], "-learn-factor="))) {
            S.learntsize_factor = atof(value);
            if (S.learntsize_factor == 0.0) {
                reportf("ERROR! Invalid learn-factor %s\n", 
                        value);
                exit(0);
            }

        }else if ((value = hasPrefix(argv[i], "-rnd-freq="))){
            double rnd;
            if (sscanf(value, "%lf", &rnd) <= 0 || rnd < 0 || rnd > 1){
                reportf("ERROR! illegal rnd-freq constant %s\n", value);
                exit(0); }
            S.random_var_freq = rnd;

        }else if ((value = hasPrefix(argv[i], "-decay="))){
            double decay;
            if (sscanf(value, "%lf", &decay) <= 0 || decay <= 0 || decay > 1){
                reportf("ERROR! illegal decay constant %s\n", value);
                exit(0); }
            S.var_decay = 1 / decay;

        }else if ((value = hasPrefix(argv[i], "-verbosity="))){
            int verbosity = (int)strtol(value, NULL, 10);
            if (verbosity == 0 && errno == EINVAL){
                reportf("ERROR! illegal verbosity level %s\n", value);
                exit(0); }
            S.verbosity = verbosity;

        }else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "-help") == 0 || strcmp(argv[i], "--help") == 0){
            printUsage(argv);
            exit(0);

        }else if (strncmp(argv[i], "-", 1) == 0){
            reportf("ERROR! unknown flag %s\n", argv[i]);
            exit(0);

        }else
            argv[j++] = argv[i];
    }
    argc = j;


    reportf("This is MiniSat 2.0 beta\n");
#if defined(__linux__)
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
    reportf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
    double cpu_time = cpuTime();

    solver = &S;
    signal(SIGINT,SIGINT_handler);
    signal(SIGHUP,SIGINT_handler);
//    FILE* sf = fopen("eqModule.tr", "w");
//    S.eqModule.set_record_stream(sf);
    if (argc == 1)
        reportf("Reading from standard input... Use '-h' or '--help' for help.\n");

    gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if (in == NULL)
        reportf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

    reportf("============================[ Problem Statistics ]=============================\n");
    reportf("|                                                                             |\n");

    parse_DIMACS(in, S);
    gzclose(in);
    FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

    double parse_time = cpuTime() - cpu_time;
    reportf("|  Parsing time:         %-12.2f s                                       |\n", parse_time);

    S.noMoreVars();
    if (!S.simplify()){
        reportf("Solved by unit propagation\n");
        if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
        printf("UNSATISFIABLE\n");
        exit(20);
    }

    bool ret = S.solve();
    totalTime.stop();
    printStats(S, totalTime);
    reportf("\n");
    printf(ret ? "SATISFIABLE\n" : "UNSATISFIABLE\n");
    if (res != NULL){
        if (ret){
            fprintf(res, "SAT\n");
            for (int i = 0; i < S.nVars(); i++)
                if (S.model[i] != l_Undef)
                    fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
            fprintf(res, " 0\n");
        }else
            fprintf(res, "UNSAT\n");
        fclose(res);
    }
    //fclose(sf);
#ifdef NDEBUG
    exit(ret ? 10 : 20);     // (faster than "return", which will invoke the destructor for 'Solver')
#endif
}
