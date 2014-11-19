/****************************************************************************************[Solver.C]
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
#include "Solver.h"
#include "Sort.h"
#include "Split.hpp"
#include "Common.hpp"
#include <cmath>
#include <vector>
#include <iostream>
#include <deque>
#define NO_XOR_MIN

#undef DBG
#ifndef DEBUG
#define checkConsistency()
#define printState()
#define DBG(x...)
#define DBG_(x)
#else
#define DBG(x...) reportf(x)
#define DBG_(x) x
#endif



using namespace std;
//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters: (formerly in 'SearchParams')
    var_decay(1 / 0.95), clause_decay(1 / 0.999), random_var_freq(0.02)
  , restart_first(100), restart_inc(1.5), 
   learntsize_factor((double)1/(double)3),   // original 1/3
   learntsize_inc(1.1) // original 1.1

    // More parameters:
    //
  , expensive_ccmin  (true)
  , polarity_mode    (polarity_false)
  , xor_propagation         (xor_propagation_eager)
  , xor_learn(0)
  , xor_rule_priority       (xor_rule_priority_internal)
  , xor_internal_vars       (false)
  , xor_store_clauses       (false)
  , xor_to_cnf              (false)
  , xor_even_elim           (false)
  , xor_minimize_reason     (false)
  , xor_deep_cuts           (true)
  , xor_cuts                (xor_cuts_first_cnf)
  , xor_bump_activity       (0)
  , verbosity        (0)

    // Statistics: (formerly in 'SolverStats')
    //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , xorPreAnalyzeJumps(0)
  , xorUnaryExp(0)
  , xorBinaryExp(0)
  , xorTernaryExp(0)
 
  
  

  , ok               (true)
  , cla_inc          (1)
  , var_inc          (1)
  , xorValidPrefix   (0)
  , xorUsefulness    (1)
  //, bumpTimestamp(0)
  , qhead            (0)
  , xorLevel         (0)
  , simpDB_assigns   (-1)
  , simpDB_props     (0)
  , order_heap       (VarOrderLt(activity))
  , random_seed      (91648253)
  , progress_estimate(0)
  , remove_satisfied (true)
  , numXorClauses(0)

{
    xorLits = 0;
    xorAlreadyLits = 0;
    xorImpliedLits = 0;
    xorJustify = xorExplain = 0;
    xorConflictLits = 0;
    xorLearnt = 0;
}


Solver::~Solver()
{
    for (int i = 0; i < learnts.size(); i++) free(learnts[i]);
    for (int i = 0; i < clauses.size(); i++) free(clauses[i]);
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches   .push();          // (list for positive literal)
    watches   .push();          // (list for negative literal)
    
    reason    .push(NULL);
    assigns   .push(toInt(l_Undef));
    xorAssigns   .push(toInt(l_Undef));
    xorJustifiable.push(0);

    level     .push(-1);
    //bumpTs    .push(0);
    activity  .push(0);
    seen      .push(0);
        

    polarity    .push((char)sign);
    decision_var.push((char)dvar);

    // variables are never removed so the variable indices in MiniSAT
    // and in libxorsat will match (with offset of 1)
    xorSolver.addVariable();

    insertVarOrder(v);
    return v;
}


bool Solver::addClause(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);

    if (!ok)
        return false;
    else{
        // Check if clause is satisfied and remove false/duplicate literals:
        sort(ps);
        Lit p; int i, j;
        for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
            if (value(ps[i]) == l_True || ps[i] == ~p)
                return true;
            else if (value(ps[i]) != l_False && ps[i] != p)
                ps[j++] = p = ps[i];
        ps.shrink(i - j);
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        assert(value(ps[0]) == l_Undef);
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == NULL);
    }else{
        Clause* c = Clause_new(ps, false);
        clauses.push(c);
        attachClause(*c);
    }



    return true;
}

bool Solver::addXorClause(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);

    if (!ok)
        return false;
    bool top = false;

    sort(ps);

    // remove assigned literals and flip the Top-symbol accordingly
    int i, j;
    for (i = j = 0; i < ps.size(); i++) {
        if (value(ps[i]) == l_False)
            continue;
        else if (value(ps[i]) == l_True) {
            top = !top;
            continue;
        }
        else {
            Lit p = ps[i];
            if (sign(p)) {
                top = !top;
                p = unsign(p);
            }
            ps[j++] = p;
        }
    }

    ps.shrink(i - j);

    if (ps.size() == 0) {

        if (top == false)
            return ok = false;
        else
            return true;
    } else if (ps.size() == 1){
        assert(value(ps[0]) == l_Undef);
        if (top)
            ps[0] = ~ps[0];

        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == NULL);
    } else{
        vector<xorsat::VariableId> xc;
        for (int j = 0; j < ps.size(); j++) {
            assert(sign(ps[j]) == false);
            xc.push_back(var(ps[j]) + 1); 
        }
        if (top)
            xc.push_back(0);

        numXorClauses ++;
        xorSolver.addClause(xc);
    }

    if(xor_to_cnf and ps.size() <= 5) {
        vec<Lit> cl;
        const unsigned int p = 1 << ps.size();
//        fprintf(stderr, "%u ", p);
        for(unsigned int i = 0; i < (1 << ps.size()); i++) {
            unsigned int nof_ones = 0;
            cl.clear();
            for (int j = 0; j < ps.size(); j++) {
                bool one = (i & (1 << j)) != 0;
                cl.push(one?~ps[j]:ps[j]);
                if(one) nof_ones++;
            }
            if(((nof_ones % 2) == 1) == top) {
                if(!addClause(cl))
                    return false;
            }
        }
    } 

    return true;
}


void Solver::attachClause(Clause& c) {
    assert(c.size() > 1);
    watches[toInt(~c[0])].push(&c);
    watches[toInt(~c[1])].push(&c);
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(Clause& c) {
    assert(c.size() > 1);
    assert(find(watches[toInt(~c[0])], &c));
    assert(find(watches[toInt(~c[1])], &c));
    if (reason[var(c[0])] == &c) {
        // reason-reference is cleared because reduceDB deletes
        // learned clauses that originated from xor-module.
        // TODO: needed?
        reason[var(c[0])] = NULL;
    }
    remove(watches[toInt(~c[0])], &c);
    remove(watches[toInt(~c[1])], &c);
    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(Clause& c) {
//    xorImplied.remove(&c);
    detachClause(c);
    free(&c); }


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int lvl) {
    if (decisionLevel() > lvl){
        for (int c = trail.size()-1; c >= trail_lim[lvl]; c--){
            Var     x  = var(trail[c]);
            assigns[x] = toInt(l_Undef);
            xorJustifiable[x] = 0;
            DBG("xorJustifiable[x%d] = 0\n", x+1);
            insertVarOrder(x); 
        }
        qhead = trail_lim[lvl];

        trail.shrink(trail.size() - trail_lim[lvl]);
        trail_lim.shrink(trail_lim.size() - lvl);
        xorValidPrefix = trail.size();
    } 
    xorCutTrail();
}

void Solver::exactCancelUntil(int qh) {
    DBG("exactCancelUntil(%d)\n", qh);

    int elems = 0;
    while (qhead > qh) {
        if (qhead < trail.size()) {
            Var x = var(trail[qhead]);
            if (level[x] == 0)
                break;
            assigns[x] = toInt(l_Undef);
            DBG("xorJustifiable[x%d] = 0\n", x+1);
            xorJustifiable[x] = 0;
            insertVarOrder(x);
            elems++;
        } 
        qhead--;
    }

    if (elems) {
        trail.shrink(elems);


        int lastLevel = level[var(trail[trail.size() - 1])];
        if (lastLevel < trail_lim.size())
            trail_lim.shrink(trail_lim.size() - lastLevel);
    }

    checkConsistency();
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit(int polarity_mode, double random_var_freq)
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (toLbool(assigns[next]) == l_Undef && decision_var[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || toLbool(assigns[next]) != l_Undef || !decision_var[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    bool sign = false;
    switch (polarity_mode){
    case polarity_true:  sign = false; break;
    case polarity_false: sign = true;  break;
    case polarity_user:  sign = polarity[next]; break;
    case polarity_rnd:   sign = irand(random_seed, 2); break;
    default: assert(false); }

    return next == var_Undef ? lit_Undef : Lit(next, sign);
}
void Solver::xorIncStats(xorsat::Disjunction& impl) {
    int v1=-1,v2=-1, s = 0;

    for (size_t i = 0; i < impl.literals.size(); i++) {
        if (level[impl.literals[i].variable - 1] > 0) {
            s ++;
            if (v1 == -1)
                v1 = impl.literals[i].variable * (impl.literals[i].negative ? -1 : 1);
            else if (v2 == -1)
                v2 = impl.literals[i].variable * (impl.literals[i].negative ? -1 : 1);
        }

    }
    switch(s) {
        case 1:
            xorUnaryExp++;
            break;
        case 2: {
                    xorBinaryExp++;
                    int tmp;
                    if (v1 > v2) {
                        tmp = v1;
                        v1 = v2;
                        v2 = tmp;
                    }


                    xorBinExps.insert(make_pair(v1,v2));
                }
                break;
        case 3:
                xorTernaryExp++;
                break;
    }



}

void Solver::xorJustifyLit(Lit p, vec<Lit>& learnt_clause)
{
    xorsat::Disjunction impl;

    xorSolver.justify(impl, xorsat::Literal(var(p)+1, sign(p)));
    int s = impl.literals.size();
    if (xorJustifyHist.size() <= s)
        xorJustifyHist.resize(s+1);
    xorJustifyHist[s]++;
    xorLits += s;
    xorIncStats(impl);

    s = 0;

    xorJustify++;
    if (xor_bump_activity) {
        const std::vector<xorsat::VariableId>& participated = 
            xorSolver.getParticipated();
        for (size_t i = 0; i < participated.size(); i++) {
            DBG("bumping activity of x%d\n", participated[i]);
            varBumpActivity(participated[i]-1);
            if (xor_bump_activity == 2)
                varBumpActivity(participated[i]-1);


        }
    }
    learnt_clause.clear();
    DBG(" got %s\n", impl.toString().c_str());
    for (vector<xorsat::Literal>::const_iterator l =
        impl.literals.begin(); l != impl.literals.end(); l++) {
        Var v = l->variable - 1;

        Lit p2 = Lit(v, l->negative);
        learnt_clause.push(p2);

    }
    if (learnt_clause.size() > 1) {
        // pick the literal with the highest decision level and swap it to
        // be the second in the clause
        int max_i = 1;
        for (int i = 2; i < learnt_clause.size(); i++)
            if (level[var(learnt_clause[i])] > level[var(learnt_clause[max_i])])
                max_i = i;
        Lit pp             = learnt_clause[max_i];
        learnt_clause[max_i] = learnt_clause[1];
        learnt_clause[1]     = pp;



        Clause* c = xorLearnClause(learnt_clause, true);
        reason[var(p)] = c;

    }
}

/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|  
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
void Solver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    //bumpTimestamp++;
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;
    checkConsistency();
    printState();

    xorsat::Disjunction impl;
    vec<Lit> learnt_clause;
    vec<Lit> xor_learnt;

    bool forgetClause = false;

    do{
        assert(confl != NULL);          // (otherwise should be UIP)
        Clause& c = *confl;

        if (c.learnt())
            claBumpActivity(c);
        

        // DEBUG
        DBG("Analyze clause : ");
        DBG_(printClause(c));
        DBG(" (dl=%d)\n", decisionLevel());


        // END DEBUG

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level[var(q)] > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level[var(q)] >= decisionLevel())
                    pathC++;
                else{
                    out_learnt.push(q);
                    if (level[var(q)] > out_btlevel)
                        out_btlevel = level[var(q)];
                }
                DBG("    seen x%d now. pathC=%d. out_btlevel=%d\n",
                    var(q)+1, pathC, out_btlevel);
            } else
                DBG("    already seen x%d\n", var(q)+1);

        }
        if (forgetClause) {
            forgetClause = false;
            DBG("forgetting xor-explanation\n");

            free(&c);
            reason[var(p)] = NULL;

            xorJustifiable[var(p)] = 1;

        }
        // Select next clause to look at:
        while (!seen[var(trail[index--])]) {
            DBG("    skipping ");
            DBG_(printLit(trail[index+1]));
            DBG("\n");
        }
        DBG(" index now : %d\n", index+1);
        p     = trail[index+1];
        if (xorJustifiable[var(p)]) {

            xorJustifiable[var(p)] = 0;
            DBG(" xor-justifying ");
            DBG_(printLit(p));
            DBG("\n");

            xorSolver.justify(impl, xorsat::Literal(var(p)+1, sign(p)));
            int s = impl.literals.size();
            if (xorJustifyHist.size() <= s)
                xorJustifyHist.resize(s+1);
            xorJustifyHist[s]++;
            xorLits += s;
            xorIncStats(impl);



            xorJustify++;
            if (xor_bump_activity) {
                const std::vector<xorsat::VariableId>& participated = 
                    xorSolver.getParticipated();
                for (size_t i = 0; i < participated.size(); i++) {
                    DBG("bumping activity of x%d\n", participated[i]);
                    varBumpActivity(participated[i]-1);
                    if (xor_bump_activity == 2)
                        varBumpActivity(participated[i]-1);


                }
            }
            learnt_clause.clear();
            DBG(" got %s\n", impl.toString().c_str());
            for (vector<xorsat::Literal>::const_iterator l =
                impl.literals.begin(); l != impl.literals.end(); l++) {
                Var v = l->variable - 1;
    
                Lit p2 = Lit(v, l->negative);
                learnt_clause.push(p2);

            }
            if (learnt_clause.size() > 1) {
                // pick the literal with the highest decision level and swap it to
                // be the second in the clause
                int max_i = 1;
                for (int i = 2; i < learnt_clause.size(); i++)
                    if (level[var(learnt_clause[i])] > level[var(learnt_clause[max_i])])
                        max_i = i;
                Lit pp             = learnt_clause[max_i];
                learnt_clause[max_i] = learnt_clause[1];
                learnt_clause[1]     = pp;



                Clause* c = xorLearnClause(learnt_clause, xor_store_clauses);
                reason[var(p)] = c;

                if (!xor_store_clauses)
                    forgetClause = true;

            } else {
                for (int i = 0; i < seen.size(); i++)
                    seen[i] = 0;
                out_learnt.clear();
                learnt_clause.copyTo(out_learnt);
                out_btlevel = 0;
                return;
            }

        }
        
        confl = reason[var(p)];
        
        seen[var(p)] = 0;
        pathC--;
        DBG("  extracting reason for ");
        DBG_(printLit(p));
        DBG(" pathC=%d\n\n",pathC);

    }while (pathC > 0);
    if (forgetClause) {
        forgetClause = false;
        DBG("forgetting xor-explanation\n");

        free(confl);
        reason[var(p)] = NULL;

        xorJustifiable[var(p)] = 1;

    }

    out_learnt[0] = ~p;
    DBG("out_learnt1: ");
    DBG_(printClause(out_learnt));
    DBG("\n");

    // Simplify conflict clause:
    //
    int i, j;
    if (expensive_ccmin){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++) {
#ifndef NO_XOR_MIN            
            if (xorJustifiable[var(out_learnt[i])]) {
                xorJustifiable[var(out_learnt[i])] = 0;
                xorJustifyLit(~out_learnt[i], xor_learnt);
                if (xor_learnt.size() == 1) {

                    out_learnt.clear();
                    xor_learnt.copyTo(out_learnt);
                    out_btlevel = 0;
                    DBG("UNIT XOR-REASON in expensive_ccmin\n");
                   for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

                    return;
                }

            }
#endif
            bool exit=false;
            Lit unit;
            if (reason[var(out_learnt[i])] == NULL || !litRedundant(out_learnt[i], abstract_level, exit, unit))
                out_learnt[j++] = out_learnt[i];
            if (exit) {
                for (int i = 0; i < seen.size(); i++)
                    seen[i] = 0;

                out_learnt.clear();
                out_learnt.push(unit);
                out_btlevel = 0;
                return;

            }

        }
    }else{
        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++){
            Clause& c = *reason[var(out_learnt[i])];
            for (int k = 1; k < c.size(); k++)
                if (!seen[var(c[k])] && level[var(c[k])] > 0){
                    out_learnt[j++] = out_learnt[i];
                    break; }
        }
    }
    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();
    
    DBG("out_learnt2: ");
    DBG_(printClause(out_learnt));
    DBG("\n");

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        for (int i = 2; i < out_learnt.size(); i++)
            if (level[var(out_learnt[i])] > level[var(out_learnt[max_i])])
                max_i = i;
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level[var(p)];
    }

    // DEBUG
    for (int i = 0; i < out_learnt.size(); i++) {
       DBG("learnt %d: %sx%d (lvl=%d)\n", i, 
           (sign(out_learnt[i]) 
              ? "~" : " "),  var(out_learnt[i])+1,
            level[var(out_learnt[i])]);
    }
    // END DEBUG


    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels, bool& exit, Lit& unit)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    vec<Lit> xor_learnt;

    while (analyze_stack.size() > 0){
        assert(reason[var(analyze_stack.last())] != NULL);
        Clause& c = *reason[var(analyze_stack.last())]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level[var(p)] > 0){
#ifndef NO_XOR_MIN            
                if (xorJustifiable[var(p)]) {
                    xorJustifiable[var(p)] = 0;
                    xorJustifyLit(~p, xor_learnt);
                    if (xor_learnt.size() == 1) {
                        unit = xor_learnt[0];
                        exit=true;
                        DBG("UNIT XOR-REASON in expensive_ccmin\n");
                        return false;
                    }

                }
#endif

                if (reason[var(p)] != NULL && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason[x] == NULL){
                assert(level[x] > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = *reason[x];
                for (int j = 1; j < c.size(); j++)
                    if (level[var(c[j])] > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}
Clause* Solver::xorLearnClause(vec<Lit>& learnt_clause, bool store) {

    Clause* c =NULL;
    assert(learnt_clause.size() > 1);


    c = Clause_new(learnt_clause, true);
    if (store) {
        xorLastLearnt.push(c);
        learnts.push(c);
        attachClause(*c);
        claBumpActivity(*c);
    }

    return c;
}

Clause* Solver::xorProcessImplication(const xorsat::Disjunction& d) {
    // position of the undefined literal in the implied clause
    int lastPos = -1;

    // MiniSAT's container for learnt clauses
    vec<Lit> learnt_clause;

    // flag indicating whether the implication is conflicting
    bool nsat = true;

    // flag indicating whether the implication is satisfied
    bool sat = false;

    DBG("xorProcessImplication(%s)\n", d.toString().c_str());
    // libxorsat's implied clause is copied to a 
    // MiniSAT-compatible container. The position of the undefined
    // literal (if any) is located

    for (vector<xorsat::Literal>::const_iterator l =
            d.literals.begin(); l != d.literals.end(); l++) {
        Var v = l->variable - 1;

        if (value(v) == l_Undef) {
            // there should be only one undefined literal
            //
            DBG("Not seen x%d -> lastPos=%d\n", v+1, 
                    learnt_clause.size());
            assert(lastPos == -1);
            lastPos = learnt_clause.size();

        }

        Lit p = Lit(v, l->negative);
        learnt_clause.push(p);

        if (value(p) != l_False) {
            // if any literal is either undefined or true,
            // then the implied clause can be/is satisfied
            nsat = false;
        }

        if (value(p) == l_True) {
            reportf("Literal ");
            printLit(p);
            reportf(" satisfied\n");
            // all the other literals in the implied clause
            // have to be false in order to justify
            // the implied literal
            sat = true;
        }
    }
    if (sat) {
        // should not happen!
        reportf("DANGER: Satisfied clause as xor-reason.. %s \n", 
                d.toString().c_str());
        return NULL;
    }

    bool learn = false;

    if (lastPos > -1) {
        // if there is an undefined literal and the
        // clause is not satisfied, then the literal 
        // can be justified by the implication
        Lit p = learnt_clause[0];
        learnt_clause[0] = learnt_clause[lastPos];
        learnt_clause[lastPos] = p;
        learn = true;
    }
    if (learnt_clause.size() > 1) {
        // pick the literal with the highest decision level and swap it to
        // be the second in the clause
        int max_i = 1;
        for (int i = 2; i < learnt_clause.size(); i++)
            if (level[var(learnt_clause[i])] > level[var(learnt_clause[max_i])])
                max_i = i;
        Lit p             = learnt_clause[max_i];
        learnt_clause[max_i] = learnt_clause[1];
        learnt_clause[1]     = p;

        if (learn || nsat) {
            // the clause is learnt if an undefined literal
            // can be justified or if the implied clause is
            // conflicting (nsat=true)
            Clause *c = xorLearnClause(learnt_clause, true);


            if (nsat) 
                return c;

        } 
        
        

    } else {
        cancelUntil(0);
        uncheckedEnqueue(learnt_clause[0]);
    }
    return NULL;
}

bool Solver::xorCutTrail(bool force) {

    DBG("xorCutTrail()\n");
    // Cut the XOR trail at a position which differs from the DPLL trail
    // restore the state of XOR solver to that point.
    // (Lazy XOR-backjumping)
    //

    // 'xorTrail' is used to remember the assignments that have been propagated
    // to XOR module
    //


   
    if (force)
        xorValidPrefix = 0;

    for (int i = xorValidPrefix; i < xorTrail.size(); i++) {
        if (trail[i] != xorTrail[i] 
                || (i == trail.size() - 1 && xorTrail.size() > trail.size())
                || (trail.size() <= i)
                || force) {
            if (!force)
                DBG("xorTrail[%d] != trail[%d] -> backjump \n", i, i);

            xorSolver.backjump(backjumps[i]); 

            // clear previous assignments
            // 
            for (int i2 = i+1; i2 < xorTrail.size(); i2++) {
                xorAssigns[var(xorTrail[i2])] = toInt(l_Undef);
                DBG("xorJustifiable[x%d] = 0\n", var(xorTrail[i2])+1);
                xorJustifiable[var(xorTrail[i2])] = 0;
            }

            // clear previous backjump points and cut the trail
            //
            backjumps.shrink(backjumps.size() - i);
            xorTrail.shrink(xorTrail.size() - i);
            return true;
        }

    }
    return xorTrail.size() < trail.size();
}
Clause* Solver::xorProcessConflict(lbool& conflictFlag) {
    xorsat::Disjunction d;


    xorSolver.explain(d);
    int s = d.literals.size();
    if (xorExplainHist.size() <= s)
        xorExplainHist.resize(s+1);
    xorExplainHist[s]++;

    xorExplain++;
    xorConflictLits += d.literals.size();

    if (xor_bump_activity) {
        const std::vector<xorsat::VariableId>& participated = 
            xorSolver.getParticipated();
        for (size_t i = 0; i < participated.size(); i++) {
            DBG("bumping activity of x%d\n", participated[i]);
            varBumpActivity(participated[i]-1);
            if (xor_bump_activity == 2)
                varBumpActivity(participated[i]-1);

        }
    }

 //    reportf("xor conflict : %s\n", d.toString().c_str());

    if (d.literals.size() == 1) { 
        // unit clauses are not added as learnt clauses
        // but added to trail at decision level 0 where
        // they cannot be removed

        DBG("implied unit clause! %s -> dl 0\n", d.toString().c_str());
        conflictFlag = l_Undef;

        bool dl0 = decisionLevel() == 0;
        cancelUntil(0);
        if (d.literals[0].variable == 0) {
            DBG("unsatisfiable");
            // unsatisfiable
            conflictFlag = l_False;
            return NULL;
        }
        Lit p = Lit(d.literals[0].variable - 1,  
                d.literals[0].negative);

        if (!dl0)
            uncheckedEnqueue(p);
        else {
            // unsatisfiable
            conflictFlag = l_False;
            return NULL;
        }
        return NULL;
    }

    Clause* conflict = xorProcessImplication(d);
    return conflict;


}
Clause* Solver::xorEagerPropagate(lbool& conflictFlag, bool force) {
    // backjump the xor-module to the last common point of trails
    if (xorCutTrail())
        conflictFlag = l_Undef;
    else {
        // both trails are empty now
        conflictFlag = l_True;
        if (xor_propagation == xor_propagation_eager && !force)
            return NULL;
    }

    bool saturated = false;
    bool propagated = false;
    bool noAssign = false;
    while (!saturated) {
        saturated = true;
        if (noAssign == false
                && ((xor_rule_priority == xor_rule_priority_external) 
                    || !propagated)) {
            for (int i = xorTrail.size(); i < trail.size(); i++) {
                Lit p = trail[i];
                xorTrail.push(p);

                DBG("XOR: assigning x%d <- %d\n",   var(p) + 1, int(sign(p) == false));

                assert(xorTrail[xorTrail.size() - 1] == trail[xorTrail.size() - 1]);
                xorValidPrefix = i;

                try {
                    backjumps.push(xorSolver.setBackjump());
                } catch (xorsat::Error e) {
                    cout << "xorsat error : " << e.what() << endl;
                    exit(1);
                }
                xorAssigns [var(p)] = toInt(lbool(!sign(p))); 
                xorSolver.assign(var(p) + 1, sign(p) == false);

                saturated = false;
                if (xor_rule_priority == xor_rule_priority_internal)
                    break;
            }
        }
        if (noAssign)
            saturated = false;
        noAssign = false;

        DBG("xorSolver.propagate()\n");
        xorsat::Solver::AssignResult ar = xorSolver.propagate();

        if (ar.implications) {
            propagated = true;
            saturated = false;
            // the external assignment to XOR-module implied one or more
            // literals. The literals along with the justifications
            // will be added to both trails

            const std::vector<xorsat::Literal>& lits= xorSolver.getImplications();

            DBG("Got %zu implied literals\n", lits.size());
            xorImpliedLits += lits.size();

            for (size_t i = 0; i < lits.size(); i++) {
                lbool v = value(lits[i].variable - 1);

                if ((v == l_False && lits[i].negative == true)
                        || (v == l_True && lits[i].negative == false)) {
                    DBG("Value for x%d known. Not asking justification\n",
                            lits[i].variable);
                    printState();
                    xorAlreadyLits++;
                } else {

                    if (v == l_Undef) {
                        Lit l(lits[i].variable - 1, lits[i].negative);

                        DBG("xor-implied literal to trail\n");
                        DBG_(printLit(l));
                        DBG("\n");
                        uncheckedEnqueue(l, NULL);
                        xorJustifiable[lits[i].variable - 1] = 1;
                        DBG("xorJustifiable[x%d] = 1\n", lits[i].variable);

                    } else {
                        DBG("Conflicting xor-implied literal\n");
                        xorUsefulness = 1;
                        xorsat::Disjunction impl;
                        xorSolver.justify(impl, lits[i]);
                        xorIncStats(impl);

                        int s = impl.literals.size();
                        if (xorJustifyHist.size() <= s)
                            xorJustifyHist.resize(s+1);
                        xorJustifyHist[s]++;

                        xorLits += impl.literals.size();
                        xorJustify++;

                        assert(impl.literals.size() > 1);
                        Clause* conflict = xorProcessImplication(impl);

                        if (conflict) 
                            return conflict;

                    }
                }
            }

        }
        if (ar.conflict)  {
            xorUsefulness = 1;
            // The external assignment to XOR-module caused a conflict.
            Clause* conflict = xorProcessConflict(conflictFlag);

            // The rest of the trail will not be propagated to XOR
            // module because the XOR solver is now in conflicting state
            // and does not accept more assignments.
            return conflict;
        } 
//        if (ar.conflict == 0 && ar.implications == 0)
//            break;
        if (xor_propagation == xor_propagation_lazy
                && propagated) {
            DBG("Lazy xor. Getting all xor-implied literals "
                    "before CNF propagation\n");

            noAssign = true;
            saturated = false;
            propagated = false;

            continue;
        }
        DBG("doing minisat propagation\n");
        int oldSize = trail.size();
        Clause* c = propagate();
        if (c) {
            xorUsefulness = 1;
            return c;
        }
        if (trail.size() > oldSize) {
            saturated = false;
        }

    }

    DBG("xor eager propagation saturated\n");
    if (xorUsefulness < 100)
        xorUsefulness++;

    return NULL;
}
Clause* Solver::xorLazyPropagate(lbool& conflictFlag) {
    // backjump the xor-module to the last common point of trails
    if (xorCutTrail())
        conflictFlag = l_Undef;
    else {
        // both trails are empty now
        conflictFlag = l_True;
        return NULL;
    }
    DBG("xorLazyPropagate()\n");
    printState();

    int lastLvl = 0;
    if (decisionLevel() > 0) {
        lastLvl = decisionLevel() - 1;
        while (lastLvl > 0 && trail_lim[lastLvl] > xorTrail.size()) {
            DBG("trail_lim[%d] : %d, xorTrail.size() : %d\n",
                    lastLvl,
                    trail_lim[lastLvl], xorTrail.size());
            lastLvl--;
        }
    }
    DBG("lazy backtrack before xor-propagate to %d from %d\n",
            lastLvl, decisionLevel());



    if (trail_lim.size() <= lastLvl) {
        conflictFlag = l_True;
        return NULL;

    }
  // collect decision literals that have not been propagated
    // to the xor-module
    deque<Lit> pending;
    for (int i = trail_lim[lastLvl]; i < trail.size(); i++) {
        Lit p = trail[i]; 
        if (!reason[var(p)] && xorJustifiable[var(p)] == 0) {
            pending.push_back( p);
            DBG("Pushing pending ");
            DBG_(printLit(p));
            DBG("\n");
        } else
            DBG("xorJustifiable[x%d] : %d\n",
                    var(p)+1, xorJustifiable[var(p)]);
    }


    cancelUntil(lastLvl);
    printState();



       
    Clause* conflict = xorEagerPropagate(conflictFlag, true);
    if (conflict)
        return conflict;
        
    while (!pending.empty()) {
        Lit p = pending.front();
        pending.pop_front();
        if (value(p) == l_Undef) {
            DBG("lazy xor : replaying pending ");
            DBG_(printLit(p));
            DBG("\n");

            newDecisionLevel();
            uncheckedEnqueue(p, NULL);
            printState();

            while (1) {
               Clause* conflict = xorEagerPropagate(conflictFlag);
    
                if (conflict)
                    return conflict;
                if (conflictFlag == l_Undef)
                    continue;
                break;
            }

        }
    }
    if (trail.size() < nVars())
        conflictFlag = l_Undef;
    return NULL;
}


void Solver::xorTagInternalVariables() {
    DBG("xorTagInternalVariables()\n");
    set<int> cnfVars;
    for (int i = 0; i < clauses.size(); i++) {
        Clause& c = *clauses[i];
        for (int i2 = 0; i2 < c.size(); i2++) {
            cnfVars.insert(var(c[i2]));
        }
    }
    int numInternals = 0;
    for (int i = 0; i < nVars(); i++) 
        if (cnfVars.find(i) == cnfVars.end() && value(i) == l_Undef)  {
            xorSolver.setInternal(i+1);
            decision_var[i] = 0;
            numInternals++;

        }
    reportf("found %d xor-internal variables out of %d\n", numInternals, nVars());
}

void Solver::uncheckedEnqueue(Lit p, Clause* from)
{
    assert(value(p) == l_Undef);
    assigns [var(p)] = toInt(lbool(!sign(p)));  // <<== abstract but not uttermost effecient
    level   [var(p)] = decisionLevel();
    reason  [var(p)] = from;
    trail.push(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
Clause* Solver::propagate()
{
    Clause* confl     = NULL;
    int     num_props = 0;
    DBG("propagate()\n");
    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Clause*>&  ws  = watches[toInt(p)];
        Clause         **i, **j, **end;
        num_props++;
        DBG("    - ");
        DBG_(printLit(p));
        DBG("\n");
        for (i = j = (Clause**)ws, end = i + ws.size();  i != end;){
            Clause& c = **i++;
            DBG("   - watch. clause : ");
            DBG_(printClause(c));
            DBG("\n");

            // Make sure the false literal is data[1]:
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;

            assert(c[1] == false_lit);

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            if (value(first) == l_True){
                DBG("    0th watch true -> clause satisfied\n");
                *j++ = &c;
            }else{
                // Look for new watch:
                DBG("    looking for new watch\n");
                for (int k = 2; k < c.size(); k++)
                    if (value(c[k]) != l_False){

                        c[1] = c[k]; c[k] = false_lit;
                        DBG("       - found watch : ");
                        DBG_(printLit(~c[1]));
                        watches[toInt(~c[1])].push(&c);
                        goto FoundWatch; }

                // Did not find watch -- clause is unit under assignment:
                *j++ = &c;
                DBG("    - no watch");
                if (value(first) == l_False){                 
                    DBG(" and false -> MINISAT CONFLICT!\n");
                    DBG_(printClause(c));
                    DBG("\n");

                    confl = &c;
                    qhead = trail.size(); 
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }else {
                    DBG(" and true -> queuing ");
                    DBG_(printLit(first));
                    DBG("\n");
                    uncheckedEnqueue(first, &c);
                }
            }
        FoundWatch:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { bool operator () (Clause* x, Clause* y) { return x->size() > 2 && (y->size() == 2 || x->activity() < y->activity()); } };
void Solver::reduceDB()
{
    DBG("reduceDB()\n");
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt());
    for (i = j = 0; i < learnts.size() / 2; i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i])) 
            removeClause(*learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    for (; i < learnts.size(); i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i]) && learnts[i]->activity() < extra_lim)
            removeClause(*learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkConsistency();
}


void Solver::removeSatisfied(vec<Clause*>& cs)
{
    int i,j;
    for (i = j = 0; i < cs.size(); i++){
        if (satisfied(*cs[i]))
            removeClause(*cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);
    DBG("simplify()\n");

    if (!ok || propagate() != NULL)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);

    // Remove fixed variables from the variable heap:
    order_heap.filter(VarFilter(*this));

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

void Solver::xorPostAnalyzeBackjump() {
    for (int i = 0; i < xorLastLearnt.size(); i++) {
        Clause& c = *xorLastLearnt[i];
        int undefs = 0;
        bool sat = false;
        int maxLevel = 0;
        for (int i2 = 0; i2 < c.size(); i2++) {
            int lvl = level[var(c[i2])];
            if (lvl > maxLevel)
                maxLevel = lvl;
            if (value(c[i2]) == l_Undef)
                undefs++;
            else if (value(c[i2]) == l_True)
                sat = true;
        }
        if (undefs < 2 && !sat) {
            cancelUntil(maxLevel);

//            exit(1);
        }
    }
}

void Solver::analyzeConflict(Clause* confl, vec<Lit>& learnt_clause) {

    xorLastLearnt.clear();
    learnt_clause.clear();
    int backtrack_level = 0;
    analyze(confl, learnt_clause, backtrack_level);
    DBG("DPLL conflict analysis. Backtracking to %d from %d\n",
            backtrack_level, decisionLevel());
    cancelUntil(backtrack_level);
    checkConsistency();
    DBG("Learnt clause after backtrack : ");
    DBG_(printClause(learnt_clause));
    DBG("\n");
    assert(value(learnt_clause[0]) == l_Undef);

    if (learnt_clause.size() == 1){
        uncheckedEnqueue(learnt_clause[0]);
    }else{
        Clause* c = Clause_new(learnt_clause, true);
        learnts.push(c);
        attachClause(*c);
        claBumpActivity(*c);
        uncheckedEnqueue(learnt_clause[0], c);

    }

    varDecayActivity();
    claDecayActivity();
    xorPostAnalyzeBackjump();
}

void Solver::xorPreAnalyzeBackjump(Clause* confl) {

    int maxLevel = 0;
    for (int i = 0; i < confl->size(); i++) {
        Var x = var((*confl)[i]);
        if (level[x] > maxLevel)
            maxLevel = level[x];
    }
    if (decisionLevel() > maxLevel) {
        DBG("Lazy backtrack before analyze to %d from %d\n",
                maxLevel, decisionLevel());
        cancelUntil(maxLevel);
        xorPreAnalyzeJumps++;
    }

}
/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts, int nof_learnts)
{
    assert(ok);

    vec<Lit>    learnt_clause;
    int         conflictC = 0;

    starts++;

    xorsat::Solver::Settings settings;

    settings.minimizeReasons = xor_minimize_reason;
    settings.evenParityElimination = xor_even_elim;
    settings.firstUIPCuts = xor_cuts == xor_cuts_first_uip;
    settings.deepCuts = xor_deep_cuts;
    settings.xorLearn = xor_learn;
    xorSolver.setSettings(settings);

    for (;;){
        DBG("search()\n");
        printState();
        
        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT
            conflicts++; conflictC++;
            DBG("conflict\n");
            xorPreAnalyzeBackjump(confl);

            if (decisionLevel() == 0) return l_False;

            analyzeConflict(confl, learnt_clause);

        }else{


            bool prop = false;
            if (xorTrail.size() != trail.size() && trail.size() > 0)
                prop = true;
            else {
                for (int i = 0; i < xorTrail.size() && i < trail.size(); i++)
                    if (xorTrail[i] != trail[i]) {
                        prop = true;
                        break;
                    }
            }
            bool cnfProp = false;
            if (xor_propagation == xor_propagation_eager && numXorClauses && prop) {
                
                lbool conflict = l_True;
                confl = xorEagerPropagate(conflict);
                if (confl) {
                    conflicts++; conflictC++; 

                    xorPreAnalyzeBackjump(confl);
                    if (decisionLevel() == 0) return l_False;
 
                    analyzeConflict(confl, learnt_clause);
                    cnfProp = true;
                } else if (conflict == l_Undef) {
                    //conflicts++; conflictC++; 
                    cnfProp = true;
                } else if (conflict == l_False)
                    return l_False;


            }
            if (numXorClauses 
                    && ((xor_propagation == xor_propagation_lazy
                        && decisions % (1 + xorUsefulness/10) == 0)
                    || (xorSolver.getNumPendingXors() > 0))) 
            {
                if (xorSolver.getNumPendingXors() > 0) {
                    DBG("Adding %d pending xors\n", xorSolver.getNumPendingXors());

                    xorCutTrail(true);
                    xorSolver.reset();
                    xorLearnt += xorSolver.getNumPendingXors();
                    xorSolver.addPendingXors();
                    
                }

                DBG("Checking XOR expressions\n");
                lbool conflict = l_True;
                Clause* confl =xorLazyPropagate(conflict);
                if (confl) {

                    xorPreAnalyzeBackjump(confl);
                    
                    if (decisionLevel() == 0) return l_False;

                    analyzeConflict(confl, learnt_clause);

                    conflicts++; conflictC++; 
                    cnfProp = true;
                } else if (conflict == l_Undef) {
                    DBG("conflict flag set\n");
                    cnfProp = true;
                } else if (conflict == l_False)
                    return l_False;

            }
            if (cnfProp)
                continue;
                

            // NO CONFLICT
            DBG("conflicts %d / %d\n", conflictC, nof_conflicts);
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify()) {
                DBG("simplify at dl 0 failed\n");
                return l_False;
            }

            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit(polarity_mode, random_var_freq);

                if (next == lit_Undef) {
                    DBG("CNF model found.\n"); 
                    // Model found:
                    if (numXorClauses 
                            && xor_propagation == xor_propagation_lazy) {

                        DBG("Checking XOR expressions\n");
                        lbool conflict = l_True;
                        Clause* confl =xorLazyPropagate(conflict);
                        if (confl) {

                             xorPreAnalyzeBackjump(confl);
                            
                            if (decisionLevel() == 0) return l_False;

                            analyzeConflict(confl, learnt_clause);

                            conflicts++; conflictC++; 
                            continue;
                        } else if (conflict == l_Undef) {
                            DBG("conflict flag set\n");
                            continue;
                        } else if (conflict == l_False)
                            return l_False;

                    }
                    if (xor_internal_vars) {
                        if (xorSolver.solve() == false) {
                            DBG("Gaussian elimination failed\n");
                            if (decisionLevel() == 0)
                                return l_False;

                            lbool flag;
                            Clause* conflict = xorProcessConflict(flag);

                            if (flag != l_False) {
                                analyzeConflict(conflict, learnt_clause);
                                conflicts++;
                                conflictC++;
                                continue;
                            }

                            return l_False;
                        }
                        DBG("Gaussian elimination ok\n");
                    }
                    return l_True;
                }
            }

            // Increase decision level and enqueue 'next'
            assert(value(next) == l_Undef);
            DBG("new decision literal : ");
            DBG_(printLit(next));
            DBG("\n");
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

bool Solver::solve(const vec<Lit>& assumps)
{
    model.clear();
    conflict.clear();

    if (!ok) return false;

    assumps.copyTo(assumptions);

    double  nof_conflicts = restart_first;
    double  nof_learnts   = (numXorClauses*4 + nClauses()) * learntsize_factor;
    lbool   status        = l_Undef;

    if (verbosity >= 1){
        reportf("============================[ Search Statistics ]==============================\n");
        reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        reportf("===============================================================================\n");
    }

    // Search:
    //
    if (xor_internal_vars) 
       xorTagInternalVariables();
    while (status == l_Undef){
        if (verbosity >= 1)
            reportf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts, order_heap.size(), nClauses(), (int)clauses_literals, (int)nof_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts *= restart_inc;
        nof_learnts   *= learntsize_inc;


    }

    if (verbosity >= 1)
        reportf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
#ifndef NDEBUG
        verifyModel();
#endif
    }else{
        assert(status == l_False);
        if (conflict.size() == 0)
            ok = false;
    }

    cancelUntil(0);
    return status == l_True;
}

//=================================================================================================
// Debug methods:


void Solver::verifyModel()
{
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++){
        assert(clauses[i]->mark() == 0);
        Clause& c = *clauses[i];
        for (int j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_True)
                goto next;

        reportf("unsatisfied clause: ");
        printClause(*clauses[i]);
        reportf("\n");
        failed = true;
    next:;
    }

    assert(!failed);

    reportf("Verified %d original clauses.\n", clauses.size());
}


void Solver::checkLiteralCount()
{
    // Check that sizes are calculated correctly:
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (clauses[i]->mark() == 0)
            cnt += clauses[i]->size();

    if ((int)clauses_literals != cnt){
        fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
        assert((int)clauses_literals == cnt);
    }
}
