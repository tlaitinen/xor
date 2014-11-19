#ifndef _xormodule_hpp_
#define _xormodule_hpp_

#include "bcg.hpp"
#include "fud.hpp"
#include "timestamp.hpp"
#include "stats.hpp"
#include "util.hpp"
#include "Settings.hpp"
#include "Simplex.h"

#include <map>
#include <set>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <queue>

//#define CHECK


namespace bx {
    // ternary xor-clause 
    struct Clause {
        // variable indices
        int v[3];

        // parity bit
        int p;

        // timestamp for propagation 
        int ts;


        Clause()  {}
        Clause(int v1, int v2, int v3, int p_) : p(p_), ts(0) {
            v[0] = v1;
            v[1] = v2;
            v[2] = v3;
        }
    };


//#define DEBUG
class XorModule {
public:
    class Interface {
        public:
            virtual ~Interface() {}

            /** returns an identifier of an unused variable */
            virtual int xorNewVar()=0;

            virtual void xorInsertToTrail(int lit, int dl)=0;
    };

    typedef Bcg::Lit Lit;


    // element in the unit propagation queue
    struct Assign {
        Lit lit;
        int r1, r2, ts, dl;
        Assign(const Lit& l, int r1_, int r2_, int ts_, int dl_)
            : lit(l), r1(r1_), r2(r2_), ts(ts_), dl(dl_) {}
    };
    Settings settings;

    Stats stats;

private:        
    // binary constraint graph used to derive explanations
    // for implied-literals and conflicts
    Bcg bcg;

    // find-union-deunion data structure used to
    // track equivalence classes of variables
    Fud fud;

    // backjump marker
    struct Backjump {
        // number of merged equivalence classes 
        // (union-operations)
        int unions;

        // number of edges in the binary constraint graph
        int edges;

        // number of implied literals
        int implied;

        // number of implied internal variable
        int internals;

        // number of assigned literals
        int assigned;

        // value of edge-timestamp
        int timestamp;

#ifdef ECAI
        int ecaiImplied;
        xorsat::BackjumpId ecaiBackjump;
#endif

        int assignOps;

        int eqvQueueOps;

        int clauseActivations;

        int dl;

        std::vector<int> aliasVars;
        std::vector<int> binXorActivations;



#ifdef DEBUG
        // stored state
        std::string state;
#endif
        Backjump() {}
        Backjump(int u, int e, int i, int int_, int a)
            : unions(u), edges(e), implied(i), internals(int_), assigned(a) {}
    };

    struct AssignOp {
        enum { Push=1, Pop=0 } op;
        Assign a;
        AssignOp() : op(Pop), a(Assign(Lit(0,0),0,0,0,0)) {}
        AssignOp(Assign& a_) : op(Push), a(a_) {}
    };
    struct EqvQueueOp {
        enum { Push, PopBack, PopFront } op;
        int v;
        EqvQueueOp() : op(PopBack), v(0) {}
        const EqvQueueOp& front() {
            op = PopFront;
            return *this;
        }
        EqvQueueOp(int v_) : op(Push), v(v_) {}
    };

//    std::vector<AssignOp> assignOps;
    std::vector<AssignOp> assignOps;
    std::vector<EqvQueueOp> eqvQueueOps;
    
    
    typedef  std::vector<size_t> Clauses;
    std::vector<size_t> clauseActivations;
    std::vector<bool> clauseActive;
    std::vector<int> clearExpParity;
    typedef std::map< std::pair<int, int>, int > AliasMap;
    AliasMap aliasMap;

    typedef std::set< std::pair< std::set<int>, bool> > PendingXors;
    PendingXors pendingXors;




    // container for variable-related information
    struct Var {
        // pointer to ternary xor-clauses where the variable
        // has occurrences
        Clauses clauses;

        // reason-variables if the variable is xor-implied
        // (or r1 is zero)
        int r1, r2;

        // timestamp when the xor-implied variable was deduced (or
        // xor-assumption assigned) (used to get the corresponding version of
        // binary constraint graph for xor-explanations)
        int ts;

        int dl;
        bool alias;
        bool internal;


           std::vector<Lit> exp;
        std::vector<int> path;
        int expParity;



        Var() : r1(0), r2(0), ts(0),  dl(0), alias(false), internal(false), expParity(0) {}
    };


    // stack of backjump markers
    std::vector<Backjump> backjumps;

    std::ofstream trailFile;



public:

    class DummyInterface : public Interface {
    public:
        int xorNewVar() {
            return 0;
        }
    };


private:

    Interface& owner;

    // stack of xor-implied literals
    std::vector<Lit> implied_lits;
    std::vector<int> implied_internals;

    std::vector<Lit> dl0Lits;


    // stack of xor-assumptions
    //std::vector<int> xorAssumptions;
    std::vector<int> xorAssumptions;


    // conflict clause (if non-empty, the solver is in conflicting state)
    std::vector<Lit> conflict;

    // variables whose activities need to be bumped
    std::vector<int> participated;

    // unit propagation queue
    std::deque<Assign> assigns;

    // eqv propagation queue
    std::deque<int> eqvQueue;

    // storage for ternary xor-clauses,
    // allocated separately because Clause-objects are not allowed
    // to move in the memory (they are pointer-referenced)
    std::vector<Clause> clauses;
    

    // storage for variables
    std::vector<Var> vars;
    std::vector<bool> inEqvQueue;
    std::vector<int> inParticipated, inExplanation;
//    std::deque<int> toExplain;
    struct ToExplain {
        int var;
        int ts;
        ToExplain(int v, int t) : var(v), ts(t) {}
        bool operator>(const ToExplain& t) const {
            return ts < t.ts;
        }
    };
    std::priority_queue< ToExplain, std::vector<ToExplain>, std::greater<ToExplain> > toExplain;

    
    typedef std::vector< std::pair<int, int> > Subgraph;
    Subgraph subgraph;

    // edge-timestamp
    int timestamp;

    int explainTimestamp;

    int clauseTimestamp;

    int conflictVar;

    int numGraphs;

    bool initialized;
#ifdef VERIFY
        Simplex simplex;
        std::vector<Lit> model_lits;

   
#endif


    void removeDuplicates(std::vector<Lit>& lits, bool evenElim);

    void addPendingImplied();


    // this method makes a conflict clause in case where a ternary xor-clause
    // 'c' has three assigned variables
    void ternaryConflict(Clause* c);

    // this method is called when a binary xor-clause is implied by the ternary
    // xor-clause 'c', it updates equivalence classes, adds edges to binary
    // constraint graph, detects and explain conflicts, and queues xor-implied
    // literals, returns false, if there is a conflict 
    bool implyBinXor(Clause* c, int e1, int e2, Lit reason);

    // this method computes the implied binary xor-clauses    
    bool ternaryBinRule(Lit reason);


    // this method increments the edge timestamp and handles
    // overflows
    void incTimestamp();

    void incEqvTimestamp();

    // checks the clauses of the variable 'varId' to find out whether there are
    // two variables in the same equivalence class in one clause.  if so, then
    // the third variable is implied, if it is unassigned.
    bool ternaryUnaryRule(int varId);

    // equivalence propagation
    bool eqvPropagate();


    // this method pops literals from the propagation queue
    // and infers implied binary xor-clauses and implied xor-literals
    // as long as possible or until a conflict is reached
    bool _propagate();


    int newBinXor(int r1, int r2, int dl, int ts);
    void _explain(Var& v, int var, int r1, int r2, int ts, 
            std::vector<Lit>& explanation, std::vector<int>& participated);



    // initializes data structures,
    // must be called before propagate()
    void setup();

    void add_ternary_xor(const std::vector<int>& lhs, const bool rhs);
    void getCommonAliasMapPairs(std::set<int>& lhs, std::set<std::pair<int,int> >& excluded,
                                std::vector<std::pair<int, int> >& pairs);

    void optimize_and_add_xor(const std::vector<int>& lhs, const bool rhs);

    void add_long_xor(const std::vector<int>& lhs, const bool rhs);

    public:
    XorModule(Interface& o);
    ~XorModule() {
    }
    /** Add a new variable in the system and return its index */
    int new_var();


    /** Add equation lhs = rhs to the system.
     * lhs is a list of variables (a variable can occur multiple times). */
    void add_equation(const std::vector<int>& lhs, const bool rhs);

    /** Is the system still satisfiable? */
    bool is_sat() const {
        return conflict.empty();
    }

    void toGraphviz(const std::string& path) {
         bcg.toGraphviz(path.c_str(), 0,0, timestamp, false);
    }

    bool propagate();


    /**
     * The number of implied literals may increase (never decrease).
     * Return false if system is in inconsistent state.
     */
    void assume(const int var, const bool value);

    /**
     * Get the conflict; "is_sat" must have returned false.
     * The returned vector is only valid until the next call to "backtrack".
     */
    const std::vector<Lit>* get_conflict() const {
        return &conflict; 
    }

    const std::vector<int>* get_participated() const {
        return &participated;
    }

    /**
     * Get the implied literals.
     * The returned vector may be grown by "assume", "add_equation" and
     * shrunk by "backtrack".
     */
    const std::vector<Lit>* get_implied_lits() const {
        return &implied_lits; 
    }
    
    /**
     * Get the explanation of the implied literal \a lit.
     */
    void explain(Lit lit, std::vector<Lit>& explanation);

    size_t numPendingXors() const {
        return pendingXors.size();

    }
    void simplify(std::vector<Lit>& dl0lits);
    int set_backtrack_point(int dl=0);

    void backtrack(int backtrack_point);
    void remove_clauses_of(int var);
#ifdef VERIFY
    void add_model_lit(int lit) {
        model_lits.push_back(Lit(abs(lit), lit < 0));
    }
#endif


#ifdef CHECK
    void checkConsistency();
    void checkNoActiveClauses(int v);
    void checkTimestamps();
#endif
#ifdef DEBUG
    std::string toString();
#endif
#ifdef VERIFY
        void verify(std::vector<Lit>& lits);
#endif

    void printLiterals(std::vector<Lit>& lits);
};
}
#endif
