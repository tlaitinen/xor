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
#include <set>
#include "Solver.h"
#include "Sort.h"
#include "Split.hpp"
#include "Common.hpp"
#include "xorsat.hpp"
#include <cmath>
#include <vector>
#include <iostream>
#include <deque>
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

xorsat::VariableId Solver::xorNewVar() {
    if (unusedAliases.empty()) {
        Var v = newVar();

        aliasCounts.push(0);
        unusedAliases.push_back(v);
    }
    Var v = unusedAliases.back();
    unusedAliases.pop_back();
    decision_var[v]= 0;


    return v+1;
}
void Solver::xorInsertToTrail(int lit, int dl) {

    trail.growTo(trail.size() + 1);
    int pos = trail_lim[dl];

    DBG("xorInsertToTrail(%d,%d) analyze_index=%d trail_lim=%d\n", lit, dl,
            index, pos);
    if (pos > index) {
        if (dl > 0) {
            if (index > trail_lim[dl-1])
                pos = index;
        } else
           pos = index;
    }

    for (int i = trail.size() - 2; i >= pos; i--) {
        trail[i+1] = trail[i];
    }

    Var v = abs(lit) - 1;
    trail[pos] = Lit(v, lit < 0);
    reason[v] = NULL;
    xorJustifiable[v] = 1;
    assigns [v] = toInt(lbool(lit > 0)); 
    level   [v] = dl;

    xorTrail.growTo(xorTrail.size() + 1);
    backjumps.growTo(backjumps.size() + 1);
    for (int i = xorTrail.size() - 2; i >= pos; i--) {
        xorTrail[i+1] = xorTrail[i];
        backjumps[i+1] = backjumps[i];
    }

    xorTrail[pos] = Lit(v, lit < 0);

    for (int i = dl; i < trail_lim.size(); i++)
        trail_lim[i]++;


    xorTrailInc++;

}


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
  , xor_lazy_factor         (2)
  , xor_rule_priority       (xor_rule_priority_internal)
  , xor_internal_vars       (false)
  , xor_store_clauses       (false)
  , xor_to_cnf              (false)
  , xor_exp_length          (100000)
  , xor_bump_activity       (0)
  , xor_even_elim           (false)
  , xor_create_vars         (false)
  , xor_deep_cuts           (false)
  , xor_1uip_cuts           (false)
  , xor_store_exp           (0)
  , xor_tree_exp            (true)
  , xor_learn_all           (false)
  , xor_up_module           (true)
  , conflictLog(NULL)
  , verbosity        (0)

    // Statistics: (formerly in 'SolverStats')
    //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , xorJustified(0), xorActivityBumps(0), xorPreAnalyzeJumps(0)
    , learnts_in_conflicts(0)


  , ok               (true)
  , cla_inc          (1)
  , firstAliasId     (0)
  , var_inc          (1)
  , xorValidPrefix   (0)
  , xorUsefulness (1)
  , xorTrailInc      (0)
  , qhead            (0)
  , upqhead         (0)
  , xorLevel         (0)
  , simpDB_assigns   (-1)
  , simpDB_props     (0)
  , order_heap       (VarOrderLt(activity))
  , random_seed      (91648253)
  , progress_estimate(0)
  , remove_satisfied (true)
  , numXorClauses(0)

{}


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
    activity  .push(0);
    seen      .push(0);
        

    polarity    .push((char)sign);
    decision_var.push((char)dvar);

    // variables are never removed so the variable indices in MiniSAT
    // and in libxorsat will match (with offset of 1)
    upModule.new_var();

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

    vector<up::Lit> lits;
    for (int i = 0; i < ps.size(); i++)
        lits.push_back(up::Lit(var(ps[i]), sign(ps[i])));
    if (ps.size() > 1)
        upModule.add_equation(lits);
    else
        addClause(ps);
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
        vector<int> xc;

        for (int j = 0; j < ps.size(); j++) {
            assert(sign(ps[j]) == false);
            xc.push_back(var(ps[j])+ 1); 
        }
        
        numXorClauses ++;
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
    for (int i = 0; i < c.size(); i++) {
        Var v = var(c[i]);
        if (v >= firstAliasId) {

DBG("firstAliasId: %d, v %d\n", firstAliasId, v);
            aliasCounts[v - firstAliasId]--;
            DBG("aliasCounts[%d] is now %d\n",
                    v - firstAliasId,
                    aliasCounts[v - firstAliasId]);
            if (aliasCounts[v - firstAliasId] == 0) {
                decision_var[v] = 0;
                DBG("moving alias variable x%d back to unused-stack\n", v+1);
                //unusedAliases.push_back(v); 
            }
        }
    }
        
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
        upqhead = qhead;

        trail.shrink(trail.size() - trail_lim[lvl]);
//        upTrail.shrink(upTrail.size() - trail.size());
        trail_lim.shrink(trail_lim.size() - lvl);
        upModule.backtrack(upBackjumps[lvl]);
        upBackjumps.shrink(upBackjumps.size() - lvl);
    }
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
void Solver::xorJustify(Lit p, vec<Lit>& learnt_clause, bool store=false)
{
    xorJustified++;
    DBG(" xor-justifying ");
    DBG_(printLit(p));
    DBG("\n");

    assert(value(p) == l_True);
    assert(xorJustifiable[var(p)]);
    assert(reason[var(p)] == NULL);

    // TJ: These should be class attributes to reduce allocation overhead
    // vec<Lit> learnt_clause;



    std::vector<bx::XorModule::Lit>& impl = xorJustifyImpl;
    upModule.explain(bx::XorModule::Lit(var(p), sign(p)), xorJustifyImpl);

    if (store)
        xorJustifiable[var(p)] = 0;

    



    learnt_clause.clear();
//    learnt_clause.push(p);
    //DBG(" got %s\n", impl.toString().c_str());
    int max_i = 1, prevLevel = 0;
    for(unsigned int i = 0; i < impl.size(); i++)
    {
        Lit p2 = Lit(impl[i].get_var(), impl[i].get_sign());
        learnt_clause.push(p2);
        if (level[var(p2)] > prevLevel && i) {
            max_i = i;
            prevLevel = level[var(p2)];
        }
    }
    if (learnt_clause.size() > 1)
    {
/*        // pick the literal with the highest decision level and swap it to
        // be the second in the clause
        int max_i = 1;
        for (int i = 2; i < learnt_clause.size(); i++)
            if (level[var(learnt_clause[i])] > level[var(learnt_clause[max_i])])
                max_i = i;*/
        if (max_i != 1) {
            Lit pp             = learnt_clause[max_i];
            learnt_clause[max_i] = learnt_clause[1];
            learnt_clause[1]     = pp;
        }
        if (store) {
            Clause* c = xorLearnClause(learnt_clause, store);
            reason[var(p)] = c;
        }
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
void Solver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel,
                     int& learntCount)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    index   = trail.size() - 1;
    out_btlevel = 0;
    checkConsistency();
    printState();

//    xorsat::Disjunction impl;
    std::vector<bx::XorModule::Lit> impl;
    vec<Lit> learnt_clause, xor_learnt;

    learntCount = 0;
    do{
        assert(confl != NULL);          // (otherwise should be UIP)
        Clause& c = *confl;

        if (c.learnt()) {
            claBumpActivity(c);
            learntCount++;
        }
        

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


        // Select next clause to look at:
        while (!seen[var(trail[index--])]) {
            DBG("    skipping ");
            DBG_(printLit(trail[index+1]));
            DBG("\n");
        }
        DBG(" index now : %d\n", index+1);
        p     = trail[index+1];

        while (xorJustifiable[var(p)]) {
            assert(reason[var(p)] == NULL);
            xorTrailInc = 0;
            xorJustify(p, xor_learnt, xor_store_clauses);
            index += xorTrailInc;
            DBG("xor_learnt.size() %d\n", xor_learnt.size());
            if (xor_learnt.size() == 1) {

                for (int i = 0; i < seen.size(); i++)
                    seen[i] = 0;
                out_learnt.clear();
                xor_learnt.copyTo(out_learnt);
                out_btlevel = 0;
                DBG("UNIT XOR-REASON\n");
                return;


            }

            assert(reason[var(p)] || !xor_store_clauses);
            if (!xor_store_clauses) {

                seen[var(p)] = 0;
                pathC--;
                if (pathC > 0) {
                    for (int j = (p == lit_Undef) ? 0 : 1; j < xor_learnt.size(); j++){
                        Lit q = xor_learnt[j];

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
                        } 
                    }
                    while (!seen[var(trail[index--])]) {
                        DBG("    skipping ");
                        DBG_(printLit(trail[index+1]));
                        DBG("\n");
                    }
                    DBG(" index now : %d\n", index+1);
                    p     = trail[index+1];


                } else {
                    goto analyzeDone;
                }
            } else 
                break;
       }
       confl = reason[var(p)];
        
        seen[var(p)] = 0;
        pathC--;
        DBG("  extracting reason for ");
        DBG_(printLit(p));
        DBG(" pathC=%d\n\n",pathC);

    }while (pathC > 0);
analyzeDone:




    out_learnt[0] = ~p;
    DBG("out_learnt1: ");
    DBG_(printClause(out_learnt));
    DBG("\n");

    // Simplify conflict clause:
    //
    int i, j;
    if (expensive_ccmin){
        assert(xorResetReason.size() == 0);

        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);

        bool exit = false;
        for (i = j = 1; i < out_learnt.size(); i++) {

#ifndef NO_XOR_MIN            
            if (xorJustifiable[var(out_learnt[i])] 
                    && reason[var(p)] == NULL) {
                xorJustify(~out_learnt[i], xor_learnt, xor_store_clauses);
                if (xor_store_clauses == false) {
                    reason[var(p)] = Clause_new(xor_learnt, true);
                    xorResetReason.push(var(p));
                }

                if (xor_learnt.size() == 1) {
                    for (int i = 0; i < seen.size(); i++)
                        seen[i] = 0;

                    out_learnt.clear();
                    xor_learnt.copyTo(out_learnt);
                    out_btlevel = 0;
                    DBG("UNIT XOR-REASON in expensive_ccmin\n");
               //     return;
                    exit = true;
                    goto exp_cc_min_done;
                }

            }
#endif
            Lit unit;
            if (reason[var(out_learnt[i])] == NULL
              || !litRedundant(out_learnt[i], abstract_level, exit, unit))
                out_learnt[j++] = out_learnt[i];
            if (exit) {
                for (int i = 0; i < seen.size(); i++)
                    seen[i] = 0;

                out_learnt.clear();
                out_learnt.push(unit);
                out_btlevel = 0;
//                return;
                goto exp_cc_min_done;

            }
        }
exp_cc_min_done:        
        for (int i = 0; i < xorResetReason.size(); i++) {
            free(reason[xorResetReason[i]]);
            reason[xorResetReason[i]] = NULL;
        }
        xorResetReason.clear();
        if (exit)
            return;
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

    bool result = true;
    while (analyze_stack.size() > 0){
        assert(reason[var(analyze_stack.last())] != NULL);
        Clause& c = *reason[var(analyze_stack.last())]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level[var(p)] > 0){
#ifndef NO_XOR_MIN            
                if (xorJustifiable[var(p)] && reason[var(p)] == NULL) {

                    xorJustify(~p, xor_learnt, xor_store_clauses);
                    if (xor_store_clauses == false) {
                        assert(reason[var(p)] == NULL);
                        reason[var(p)] = Clause_new(xor_learnt, true);
                        xorResetReason.push(var(p));
                    }
                    
                    if (xor_learnt.size() == 1) {
                        unit = xor_learnt[0];
                        exit=true;
                        DBG("UNIT XOR-REASON in expensive_ccmin\n");
                        return false;
                    }
                }

#endif
                if (reason[var(p)] != NULL
                        && (abstractLevel(var(p)) & abstract_levels) != 0){
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
void Solver::xorIncAliasCount(vec<Lit>& learnt_clause) {
    for (int i = 0; i < learnt_clause.size(); i++) {
        Lit l = learnt_clause[i];
        Var v = var(l);
        if (v >= firstAliasId) {
            aliasCounts[v - firstAliasId]++;
            if (aliasCounts[v - firstAliasId] == 1) {
                if (!decision_var[v]) {
                    DBG("making alias variable %d a decision variable : ", v);
                    decision_var[v] = 1 ; // xor_branch_vars != xor_branch_vars_no_alias);
                }
            }

            DBG("aliasCounts[%d] is now %d\n",
                    v - firstAliasId, aliasCounts[v - firstAliasId]);
        }
    }

}

Clause* Solver::xorLearnClause(vec<Lit>& learnt_clause, bool store) {

    Clause* c =NULL;
    assert(learnt_clause.size() > 1);

    //xorIncAliasCount(learnt_clause);

    c = Clause_new(learnt_clause, true);
    if (store) {
        xorLastLearnt.push(c);
        learnts.push(c);
        attachClause(*c);
        claBumpActivity(*c);
    }

    return c;
}

Clause* Solver::xorProcessImplication(const std::vector<bx::XorModule::Lit>* d, bool up) { // const xorsat::Disjunction& d) {
    // position of the undefined literal in the implied clause
    int lastPos = -1;

    // MiniSAT's container for learnt clauses
    vec<Lit> learnt_clause;

    // flag indicating whether the implication is conflicting
    bool nsat = true;

    // flag indicating whether the implication is satisfied
    bool sat = false;

    DBG("xorProcessImplication\n"); // (%s)\n", d.toString().c_str());
    // libxorsat's implied clause is copied to a 
    // MiniSAT-compatible container. The position of the undefined
    // literal (if any) is located
//    for (vector<xorsat::Literal>::const_iterator l =
//            d.literals.begin(); l != d.literals.end(); l++) {
    for (std::vector<bx::XorModule::Lit>::const_iterator l = d->begin(); 
            l != d->end(); l++) {
//        Var v = l->variable - 1;
        Var v = l->get_var();
        if (!up)
            v --;

        if (value(v) == l_Undef) {
            // there should be only one undefined literal
            //
            DBG("Not seen x%d -> lastPos=%d\n", v+1, 
                    learnt_clause.size());
            assert(lastPos == -1);
            lastPos = learnt_clause.size();

        }

//        Lit p = Lit(v, l->negative);
        Lit p = Lit(v, l->get_sign());

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
    DBG_(printClause(learnt_clause));
//    printClause(learnt_clause);    reportf("\n"); // FOO


    if (sat) {
        // should not happen!
        reportf("DANGER: Satisfied clause as xor-reason..  \n");
        exit(0);
//                d.toString().c_str());
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
            Clause *c = xorLearnClause(learnt_clause, xor_store_clauses);
            if (!xor_store_clauses) {
                xorFreeClauses.push(c);
            }



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
    return xorTrail.size() < trail.size();
}
Clause* Solver::xorUpProcessConflict(lbool& conflictFlag) {
//    xorsat::Disjunction d;


//    xorSolver.explain(d);
    const std::vector<up::Lit>* d = upModule.get_conflict();

 //    reportf("xor conflict : %s\n", d.toString().c_str());

    if (d/*.literals*/->size() == 1) { 
        // unit clauses are not added as learnt clauses
        // but added to trail at decision level 0 where
        // they cannot be removed

        DBG("implied unit clause!  -> dl 0\n"); // , d.toString().c_str());
        conflictFlag = l_Undef;

        cancelUntil(0);
        if ((*d).size() == 0) {
            conflictFlag = l_False;
            return NULL;
        }

        Lit p((*d)[0].get_var(), (*d)[0].get_sign());        

        if (value(p) == l_Undef)
            uncheckedEnqueue(p);
        else {
            // unsatisfiable
            conflictFlag = l_False;
            return NULL;
        }
        return NULL;
    }

    Clause* conflict = xorProcessImplication(d, true);
    return conflict;


}
Clause* Solver::xorProcessConflict(lbool& conflictFlag) {
        return NULL;


}
Clause* Solver::xorUpPropagate(lbool& conflictFlag) {
    bool saturated = false;
    bool propagated = false;

    while (!saturated) {
        const std::vector<up::Lit>* implied = upModule.get_implied_lits();

        saturated = true;
        for (; upqhead < trail.size(); ) {
            Lit p = trail[upqhead++];

            DBG("UP: assigning x%d <- %d\n",   var(p), int(sign(p) == false));

//            assert(upTrail[upTrail.size() - 1] == trail[upTrail.size() - 1]);

            upModule.assume(var(p), sign(p) == false);

            saturated = false;
            if (xor_rule_priority == xor_rule_priority_internal)
                break;

        }
//        while (1) {

            size_t firstImplied = upModule.get_first_implied();
            bool result = upModule.propagate();
            upModule.reset_first_implied();
            if (implied->size() > firstImplied) {
                propagated = true;
                saturated = false;
                // the external assignment to XOR-module implied one or more
                // literals. The literals along with the justifications
                // will be added to both trails

                DBG("Got %zu implied literals\n", implied->size() - firstImplied);

                for (size_t i = firstImplied; i < /*lits*/implied->size(); i++) {
                    up::Lit il = (*implied)[i];
                    DBG("xor-implied %zu/%zu: %cx%d\n", i+1, implied->size(),
                            il.get_sign() ? '-' : ' ',
                            il.get_var());
                    lbool v = value(il.get_var());

                    if ((v == l_False && il.get_sign() == true)
                            || (v == l_True && il.get_sign() == false)) {

                        DBG("Value for x%d known. Not asking justification\n",
                                il.get_var());
                        printState();
                    } else {

                        if (v == l_Undef) {
                            Lit l(il.get_var(), il.get_sign());

                            DBG("xor-implied literal to trail\n");
                            DBG_(printLit(l));
                            DBG("\n");
                            uncheckedEnqueue(l, NULL);
                            xorJustifiable[il.get_var()] = 2;
                            DBG("xorJustifiable[x%d] = 2\n", il.get_var());


                        } else {
                            DBG("Conflicting xor-implied literal");
                            DBG_(Lit l(il.get_var(), il.get_sign()));
                            DBG_(printLit(l));
                            DBG("\n");

                            std::vector<up::Lit> impl;
                            upModule.explain(il, impl);
                            if (impl.size() == 1) {
                                Lit l(il.get_var(), il.get_sign());
                                if (decisionLevel() == 0) {
                                    conflictFlag = l_False;
                                    return NULL;
                                } else {
                                    cancelUntil(0);
                                    uncheckedEnqueue(l);
                                    conflictFlag = l_Undef;
                                    return NULL;
                                }

                            }
                                    
                            Clause* conflict = xorProcessImplication(&impl, true);

                            if (conflict) 
                                return conflict;

                        }
                    }
                }

            } 
            if (!upModule.is_sat()) {

                DBG("UP: conflict");
                // The external assignment to XOR-module caused a conflict.
                Clause* conflict = xorUpProcessConflict(conflictFlag);

                // The rest of the trail will not be propagated to XOR
                // module because the XOR solver is now in conflicting state
                // and does not accept more assignments.
                return conflict;
            } 
//            if (firstImplied == implied->size())
//                break;
//        }
        DBG("doing minisat propagation\n");
        int oldSize = trail.size();
        Clause* c = propagate();
        if (c) {
            return c;
        }
        if (upqhead < trail.size()) {
            DBG("upqhead < trail.size");
            saturated = false;
            propagated = false;
        }
    }
//    reportf("saturated trails %d %d\n", trail.size(), xorTrail.size()); // FOO
    DBG("xor eager propagation saturated\n");

    return NULL;
}

Clause* Solver::xorEagerPropagate(lbool& conflictFlag) {
    // backjump the xor-module to the last common point of trails
    if (xorCutTrail())
        conflictFlag = l_Undef;
    else {
        // both trails are empty now
        conflictFlag = l_True;
        if (xor_propagation == xor_propagation_eager)
            return NULL;
    }
    /*
    // FOO
    reportf("trail:"); 
    for (int i = 0; i < trail_lim.size(); i++) {
        Lit p = trail[trail_lim[i]];
        Var v = var(p);
        lbool s = value(v); 
        reportf(" %d", ((s == l_False) ? -1 : 1) * v);


    }
    reportf("\n");
    // END FOO

*/
    bool saturated = false;
    bool propagated = false;

    while (!saturated) {
        const std::vector<bx::XorModule::Lit>* implied;

        saturated = true;
        if ((xor_rule_priority == xor_rule_priority_external) || !propagated) {
            for (int i = xorTrail.size(); i < trail.size(); i++) {
                Lit p = trail[i];
                xorTrail.push(p);

                DBG("XOR: assigning x%d <- %d\n",   var(p), int(sign(p) == false));

                assert(xorTrail[xorTrail.size() - 1] == trail[xorTrail.size() - 1]);

                xorValidPrefix = i;
                xorAssigns [var(p)] = toInt(lbool(!sign(p))); 

                saturated = false;
                if (xor_rule_priority == xor_rule_priority_internal)
                    break;
            }
        }
        DBG("xorSolver.propagate()\n");
//        while (1) {

            size_t firstImplied = implied->size();
            bool result;
            if (implied->size() > firstImplied) {
                propagated = true;
                saturated = false;
                // the external assignment to XOR-module implied one or more
                // literals. The literals along with the justifications
                // will be added to both trails

                DBG("Got %zu implied literals\n", implied->size() - firstImplied);

                for (size_t i = firstImplied; i < /*lits*/implied->size(); i++) {
                    bx::XorModule::Lit il = (*implied)[i];
                    DBG("xor-implied %zu/%zu: %cx%d\n", i+1, implied->size(),
                            il.get_sign() ? '-' : ' ',
                            il.get_var()-1);
                    lbool v = value(il.get_var() - 1);

                    if ((v == l_False && il.get_sign() == true)
                            || (v == l_True && il.get_sign() == false)) {

                        DBG("Value for x%d known. Not asking justification\n",
                                il.get_var()-1);
                        printState();
                    } else {

                        if (v == l_Undef) {
                            Lit l(il.get_var() - 1, il.get_sign());

                            DBG("xor-implied literal to trail\n");
                            DBG_(printLit(l));
                            DBG("\n");
                            uncheckedEnqueue(l, NULL);
                            xorJustifiable[il.get_var()-1] = 1;
                            DBG("xorJustifiable[x%d] = 1\n", il.get_var()-1);


                        } else {
                            DBG("Conflicting xor-implied literal");
                            DBG_(Lit l(il.get_var() - 1, il.get_sign()));
                            DBG_(printLit(l));
                            DBG("\n");
                            xorUsefulness = 1;



                            std::vector<bx::XorModule::Lit> impl;
                            if (impl.size() == 1) {
                                Lit l(il.get_var() - 1, il.get_sign());
                                if (decisionLevel() == 0) {
                                    conflictFlag = l_False;
                                    return NULL;
                                } else {
                                    cancelUntil(0);
                                    uncheckedEnqueue(l);
                                    conflictFlag = l_Undef;
                                    return NULL;
                                }

                            }
                                    
                            Clause* conflict = xorProcessImplication(&impl);

                            if (conflict) 
                                return conflict;

                        }
                    }
                }

            } 
            if (false) {
                xorUsefulness = 1;

                DBG("XOR: conflict");
                // The external assignment to XOR-module caused a conflict.
                Clause* conflict = xorProcessConflict(conflictFlag);

                // The rest of the trail will not be propagated to XOR
                // module because the XOR solver is now in conflicting state
                // and does not accept more assignments.
                return conflict;
            } 
//            if (firstImplied == implied->size())
//                break;
//        }
        if (xor_propagation == xor_propagation_lazy && propagated) {
            DBG("Lazy xor. Getting all xor-implied literals "
                "before CNF propagation\n");

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
        if (trail.size() > oldSize || xorTrail.size() < trail.size()) {
            saturated = false;
            propagated = false;
        }
    }
//    reportf("saturated trails %d %d\n", trail.size(), xorTrail.size()); // FOO
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



       
    Clause* conflict = xorEagerPropagate(conflictFlag);
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
//            xorSolver.setInternal(i+1); TODO: Simplex
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

void Solver::logConflict(vec<Lit>& clause,  int learntCount) {
    /*
    for (int i = 0; i < clause.size(); i++) {
        Lit l = clause[i];
        Var v = var(l);
        int li = toInt(l);

        fprintf(conflictLog, "%c(%d,%d)", (i > 0) ? ',' : '[', li, level[v]);
    }
  fprintf(conflictLog, "]\n");

    */
    fprintf(conflictLog, "%d %d\n", clause.size(), learntCount);

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
//            printf("not sat and not enough undefs! %d/%d\n", undefs, c.size());
//            printf("Backtracking to %d from %d\n", maxLevel, decisionLevel());
            cancelUntil(maxLevel);

//            exit(1);
        }
    }
}

bool Solver::analyzeConflict(Clause* confl, vec<Lit>& learnt_clause) {
    while (confl) {
        xorLastLearnt.clear();

        learnt_clause.clear();
        int backtrack_level = 0;
        int learntCount;
        analyze(confl, learnt_clause, backtrack_level, learntCount);
        confl =  NULL;
        learnts_in_conflicts += learntCount;

        if (xorFreeClauses.size() > 0) {
            for (int i = 0; i < xorFreeClauses.size(); i++) {
                free(xorFreeClauses[i]);
            }

            xorFreeClauses.clear();
        }

        DBG("DPLL conflict analysis. Backtracking to %d from %d\n",
                backtrack_level, decisionLevel());
        cancelUntil(backtrack_level);
        checkConsistency();
        DBG("Learnt clause after backtrack : ");
        DBG_(printClause(learnt_clause));
        DBG("\n");
        assert(value(learnt_clause[0]) == l_Undef);

        if (conflictLog)
            logConflict(learnt_clause, learntCount);

        if (learnt_clause.size() == 1){
            if (value(learnt_clause[0]) == l_False)
                return false;
            uncheckedEnqueue(learnt_clause[0]);
        }else{
            //xorIncAliasCount(learnt_clause);
            Clause* c = Clause_new(learnt_clause, true);
            learnts.push(c);
            attachClause(*c);
            claBumpActivity(*c);
            // reportf("CONFLICT: ");       printClause(*c);      reportf("\n"); // FOO

            uncheckedEnqueue(learnt_clause[0], c);

        }

        int btLevel = decisionLevel();
        const up::XorModule::PendingXors& xors = upModule.getPendingXors();
        if (!xors.empty()) {


            for (up::XorModule::PendingXors::const_iterator i = xors.begin();
                    i != xors.end(); i++) {
                int maxLevel = 0;
                for (std::vector<up::Lit>::const_iterator i2 = i->begin();
                        i2 != i->end(); i2++) {
                    Var v = i2->get_var();
                    if (level[v] > maxLevel)
                        maxLevel = level[v];
//                    if (level[v] < minLevel)
//                        minLevel = level[v];

                    DBG("%d lvl %d\n", v, level[v]);
                }
                if (btLevel > maxLevel)
                    btLevel = maxLevel;
                DBG("Max level %d  \n", maxLevel);
                DBG("got pending xor %s\n",bx::toString(*i).c_str());
            }
            if (btLevel-1 < decisionLevel()) {
                if (btLevel > 0)
                    btLevel--;

                //        reportf("Parity explanation jump from dl %d to dl %d\n",
                //                decisionLevel(), btLevel);
                cancelUntil(btLevel);
            }

            for (up::XorModule::PendingXors::const_iterator i = xors.begin();
                    i != xors.end(); i++) {

                upModule.add_equation(*i, true);
            }

            upModule.clearPendingXors();
        }
    }
    varDecayActivity();
    claDecayActivity();
    upModule.claDecayActivity();

    xorPostAnalyzeBackjump();

    return true;
}


void Solver::xorPreAnalyzeBackjump(Clause* confl) {

    int maxLevel = 0;
    for (int i = 0; i < confl->size(); i++) {
        Var x = var((*confl)[i]);
        if (level[x] > maxLevel)
            maxLevel = level[x];
    }
    DBG("Lazy backtrack before analyze to %d from %d\n",
            maxLevel, decisionLevel());
    if (maxLevel < decisionLevel()) {
       cancelUntil(maxLevel);
       xorPreAnalyzeJumps++;
    }

}

void Solver::noMoreVars() {
    firstAliasId = nVars();
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
    //DBG_(eqModule.set_verbose_level(100));
    //xorsat::Solver::Settings settings;

//    settings.minimizeReasons = xor_minimize_reason;
//    settings.firstUIPCuts = xor_cuts == xor_cuts_first_uip;
    if (xor_store_exp)
        xor_even_elim = true;
    upModule.settings.evenElim = xor_even_elim;
    upModule.settings.xorLearn = xor_store_exp;
    upModule.settings.deepCuts = xor_deep_cuts;
    upModule.settings.firstUipCuts = xor_1uip_cuts;
    upModule.settings.learnAll = xor_learn_all;
    //xorSolver.setSettings(settings);

    xorCutTrail(true);




    for (;;){
        DBG("search()\n");
        printState();
        
        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT

            conflicts++; conflictC++;
            DBG("conflict\n");
            if (xor_propagation == xor_propagation_lazy) 
                xorPreAnalyzeBackjump(confl);

            if (decisionLevel() == 0) return l_False;

            if (!analyzeConflict(confl, learnt_clause))
                return l_False;

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
            if (xor_up_module && numXorClauses) {
                lbool conflict = l_True;
                xorTime.start();
                confl = xorUpPropagate(conflict);
                xorTime.stop();
                if (confl) {

                    conflicts++; conflictC++; 

                    if (decisionLevel() == 0) return l_False;
 
                    analyzeConflict(confl, learnt_clause);

                    continue;
                } else if (conflict == l_Undef) {
                    continue;
                } else if (conflict == l_False)
                    return l_False;
            }





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

                            if (xor_propagation == xor_propagation_lazy) 
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
            if (xor_up_module && numXorClauses) {
                lbool conflict = l_True;
                xorTime.start();
                confl = xorUpPropagate(conflict);
                xorTime.stop();
                if (confl) {

                    conflicts++; conflictC++; 

                    if (decisionLevel() == 0) return l_False;
 
                    analyzeConflict(confl, learnt_clause);

                    continue;
                } else if (conflict == l_Undef) {
                    continue;
                } else if (conflict == l_False)
                    return l_False;
            }

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

//    if (xor_internal_vars) 
//       xorTagInternalVariables();




    assumps.copyTo(assumptions);

    double  nof_conflicts = restart_first;
    double  nof_learnts   = (numXorClauses*4 + nClauses()) * learntsize_factor;
    upModule.setNumLearnts(nof_learnts);
    lbool   status        = l_Undef;

    if (verbosity >= 1){
        reportf("============================[ Search Statistics ]==============================\n");
        reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        reportf("===============================================================================\n");
    }

    // Search:
    //

    while (status == l_Undef){
        if (verbosity >= 1)
            reportf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts, order_heap.size(), nClauses(), (int)clauses_literals, (int)nof_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts *= restart_inc;
        nof_learnts   *= learntsize_inc;
        upModule.setNumLearnts(nof_learnts);


    }
    if (conflictLog)
        fclose(conflictLog);

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
