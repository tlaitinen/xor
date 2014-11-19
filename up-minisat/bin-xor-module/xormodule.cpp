#include "xormodule.hpp"
#include "Simplex.h"
#include "util.hpp"

namespace bx {
using namespace std;


void XorModule::removeDuplicates(std::vector<Lit>& lits, bool evenElim) {
    int last = lits.size() - 1;
#ifdef VERIFY
     for (size_t i = 0; i < lits.size(); i++) {
         assert(vars[lits[i].get_var()].expParity == 0);
     }
#endif
    explainTimestamp++;
    if (settings.evenParityElimination && evenElim) {
        for (size_t i = 0; i < lits.size(); i++) {
            int v = lits[i].get_var();
            vars[v].expParity++;

            D(dbg::prop, "increasing expParity for " << v << " now " << 
                    vars[v].expParity);
        }
    }
    for (int i = 0; i <= last;) {

        int v = lits[i].get_var();
        D(dbg::prop, "checking " << v << " i=" << i << " last=" << last);
        if (inExplanation[v] == explainTimestamp 
                || (settings.evenParityElimination && evenElim && vars[v].expParity % 2 == 0)) {
            lits[i] = lits[last--];
            D(dbg::prop, "removed duplicate: " << v << " expParity : " << vars[v].expParity);
        } else {
            D(dbg::prop, "first occurrence");
            inExplanation[v] = explainTimestamp;
            i++;
        }

        vars[v].expParity = 0;
    }

    lits.resize(last+1);
}

   void XorModule::addPendingImplied()

    {
        for (size_t i = 0; i < assigns.size(); i++) {
            Assign a = assigns[i];
            int v = a.lit.get_var();
            if (vars[v].ts == 0 && a.r1 != 0) {
                D(dbg::prop,"pending implied " << (a.lit.get_sign() ? "-x" : "x") << v
                        << " r1=" << a.r1 << " r2=" << a.r2);
                vars[v].r1 = a.r1;
                vars[v].r2 = a.r2;
                vars[v].ts = a.ts; 
                vars[v].dl = a.dl;
                if (!vars[v].internal)
                    implied_lits.push_back(a.lit);
                else
                    implied_internals.push_back(v);

                if (a.r2) {
                    // if the reason has two terms, then it is a ternary ->
                    // unary xor-implied literal
                    stats.ternaryXorImplied++;
                }
                else
                    stats.binaryXorImplied++;
            }
        }
    }

    void XorModule::ternaryConflict(Clause* c)
    {
        // find the representative of the equivalence class
        // where the symbol Top is
        Fud::Result top;
        fud.find(0, top);

#ifdef DEBUG
        int sum = 0;
#endif
        // add three literals to the conflict clause
        for (int i = 0; i < 3; i++) {

            int v = c->v[i];

            // find the representative of the equivalence
            // class where the ith variable 'v' is
            Fud::Result r;
            fud.find(v, r);

            // each variable should be assigned
            assert(r.var == top.var);

            // determine the value of 'v'
            bool value = r.parity == top.parity;
#ifdef DEBUG
            sum += int(value);
#endif
            addPendingImplied();
            // negate the value
            D(dbg::prop,"ternary conflict item: " << ((value) ? "-x" : "x") << v);
            conflict.push_back(Lit(v, value));
        }
#ifdef DEBUG
        sum += c->p;
        D(dbg::state,toString());
        assert(sum % 2 == 0);
#endif
        // increment statistics counter
        stats.terXorConflicts++;
#ifdef VERIFY
        verify(conflict);
#endif

    }

    bool XorModule::implyBinXor(Clause* c, int e1, int e2, Lit reason) {    
        // find representatives of the equivalence classes of 'e1' and 'e2'
        Fud::Result e1r; 
        fud.find(e1, e1r);
        Fud::Result e2r;
        fud.find(e2, e2r);

        // compute the parity between variables 'e1' and 'e2'
        // (depends on the xor-assumption and the parity of the clause)
        int parity = (int(reason.get_sign()) + c->p) & 1;

            D(dbg::prop,"implied bin-xor x" << e1 << ((parity == 1) ? " != x" : " == x") << e2 << " by clause " 
                << c->v[0] << " " << c->v[1] << " " << c->v[2] << " parity " << c->p);





        Fud::Result top;
        fud.find(0, top);


        incTimestamp();

        if (e1r.var == e2r.var) {
            D(dbg::prop,"same equivalence class");
            D(dbg::prop,"pushEdge(" << e1 << ", " << e2 << ", p=" << parity << ", ts=" <<timestamp);
            D(dbg::prop, "e1r.var " << e1r.var << " p=" << e1r.parity << ", e2r.var " << e2r.var << " p=" << e2r.parity);

            // add an edge to the binary constraint graph
            bcg.pushEdge(e1, e2, parity, reason, timestamp, backjumps.back().dl);


            // if the two variables are already in the same equivalence class
            // and the new binary xor-clause differs in parity from the
            // existing parity, we have a conflict

            if (int(e1r.parity != e2r.parity) != parity) {
                // find first a conflicting path
                D(dbg::prop, "conflict!");

                if (settings.fastExp) {


                    fud.explain(conflict, e1, e2, stats.evenParityEliminated);
                    conflict.push_back(reason.neg());
#ifdef VERIFY
        verify(conflict);
#endif

                    return false;
                }
                // we have a conflict

                participated.clear();
//                 bcg.toGraphviz("bcg.dot", 0,0,timestamp,false);

                bcg.explainPath(e1, e1, timestamp, conflict, participated);

                removeDuplicates(conflict, true);
                vector<Lit> exp, bigExp;
                for (size_t i = 0; i < conflict.size(); i++) {
                    Lit l = Lit(conflict[i].get_var(), !conflict[i].get_sign());

                    if (vars[l.get_var()].r1 != 0) {
                        explain(l, exp);
                        copy(exp.begin()+1, exp.end(), back_inserter(bigExp));
                    } else {
                        assert(vars[l.get_var()].internal == false);
                        bigExp.push_back(conflict[i]);
                    }

                }
                conflict.clear();
                copy(bigExp.begin(), bigExp.end(), back_inserter(conflict));
                removeDuplicates(conflict, false);
                //explain(Lit(0,false), conflict);
                conflictVar = e1;
                if (conflict.empty())
                    conflict.push_back(Lit(0,true));
/*
                if (e1r.var != top.var || conflict.size() <= 3) {
                    // if we have a conflicting equivalence class
                    // without the symbol Top, we have to use the
                    // conflicting path, but if the symbol Top
                    // is in the equivalence class, we can sometimes 
                    // get very short conflict explanations 

                    stats.binXorConflicts++;
                    stats.binXorConflictLits += conflict.size();

                    if (conflict.size() == 0) {
                        conflict.push_back(Lit(0,true));
                    }
                    // TODO: conflict.size() == 2 pendingBinXors

                    if (settings.storeXorExp    && false
                            && conflict.size() >= 3
                            &&  conflict.size() <= settings.storeXorExp) {
                        set<int> varSet;
                        bool rhs = true;

                        for (size_t i = 0; i < conflict.size(); i++) {
                            varSet.insert(conflict[i].get_var());
                            if (conflict[i].get_sign())
                                rhs = !rhs;
                        }

                        pair<PendingXors::iterator,bool> i = 
                            pendingXors.insert(make_pair(varSet, rhs));


                        if (i.second) {

                            //                bcg.toGraphviz("bcg" + bx::toString(varSet) + "_" + bx::toString(rhs) + ".dot", 0,0,timestamp,false);

                            D(dbg::prop, "Adding pending xor " 
                                    << bx::toString(varSet)
                                    << " = " << rhs);
                            D(dbg::prop, "conflict: " << bx::toString(conflict));
                        }
                    }


                } else {
                    conflict.clear();
                    // but if we got a conflict clause that has more than 3
                    // literals, we can do better by just taking the
                    // ternary xor-clause, that we used to imply the last
                    // binary-xor-clause that caused the conflict, and form
                    // the conflict clause
                    ternaryConflict(c);
                }
*/

                assert(!conflict.empty());
#ifdef VERIFY
//                verify(conflict);
#endif
                return false;

            } else {
                D(dbg::prop,"same value");
                // the variables are already in the same equivalence
                // class and the new binary xor-clause agrees
                // with the existing parity, so we're done
                return true;
            }
        }

        // at this point we're joining two equivalence classes 
        assert(e1r.var != e2r.var);

        // normally, we want to check the ternary xor-clauses
        // of the smaller equivalence class, so 
        // we'll pick the "first" equivalence class if 
        // it is smaller...
        int checkVar = (e1r.size < e2r.size) ? e1 : e2;

        // ... but in case the first equivalence class is assigned, and we
        // have to list the variables in the second equivalence class as
        // xor-implied literals, we need to list the variables of the
        // second equivalence class anyway, 'hasValue' becomes true if the
        // other equivalence class is assigned
        bool hasValue = false;

        // 'value' holds the value of the variable that belongs to the
        // assigned equivalence class ('e1' or 'e2')
        bool value;

        // check if one of the equivalence classes to be joined is assigned
        if (e1r.var == top.var) {
            hasValue = true;
            // we pick the second equivalence class despite the size
            checkVar = e2;
            value = e1r.parity == top.parity;
            D(dbg::prop,"x" << e1 << " already has value " << value);
        } else if (e2r.var == top.var) {
            hasValue = true;
            // we pick the first equivalence class despite the size
            checkVar = e1;
            value = e2r.parity == top.parity;
            D(dbg::prop,"x" << e2 << " already has value " << value);
        }

        // check the parity between the equivalence classes
        if (hasValue && parity) {
            value = !value;
            D(dbg::prop,"flipping value because of parity");
        }


        D(dbg::prop,"picking the equivalence class of x" << checkVar);
        subgraph.clear();
        subgraph.push_back(std::make_pair(checkVar, 0));
        bcg.subgraph(checkVar, subgraph);


        // add an edge to the binary constraint graph
        // after the subgraph has been retrieved
        bcg.pushEdge(e1, e2, parity, reason, timestamp, backjumps.back().dl);
        D(dbg::prop,"pushEdge(" << e1 << ", " << e2 << ", p=" << parity << ", ts=" <<timestamp);


        D(dbg::prop,"union(x" << e1 << ",x"<<e2<<", p="<<parity<<")");

        // update the equivalence class tracking data structure
        fud.union_(e1, e2, parity, reason);

//        fud.toGraphviz(bx::toString(timestamp) + "fud.dot");
        D(dbg::prop,"joined equivalence class sizes : " << e1r.size << " and " <<
                e2r.size);
        // check every variable in the picked equivalence class
        for (Subgraph::iterator i = subgraph.begin(); i != subgraph.end(); i++) {
            std::pair<int, int> check = *i;

            if (!hasValue) {
                // if neither of the equivalence classes was not assigned, 
                // we add the variables of the smaller equivalence class to the
                // equivalence propagation queue, so we can later check the
                // ternary xor-clauses of each new variable in the equivalence
                // class to find out whether we can infer new xor-implied
                // literals
                if (inEqvQueue[check.first] ==false) {
                    D(dbg::prop,"queuing x" << check.first 
                            << " for equivalence propagation");
                    inEqvQueue[check.first] = true;
                    eqvQueue.push_back(check.first);
                    eqvQueueOps.push_back(EqvQueueOp());

                } else {
                    D(dbg::prop,"not queue x" << check.first
                            << " for eq propagation (already in eqvQueue)");
#ifdef DEBUG
                    bool found = false;
                    for (size_t i2 = 0; i2 < eqvQueue.size(); i2++) {
                        if (eqvQueue[i2] == check.first)
                            found = true;
                        
                    }
                    assert(found);

#endif
                }
            } else {
                // otherwise, we assign the variables of the other
                // equivalence class 
                bool sign = ((int(value) + check.second) & 1) == 0;

                D(dbg::prop,"eqv class up implied. x" << check.first << " := " 
                        << int(sign == false) << " (parity=" << check.second << ")");

                Lit lit(check.first, sign);
                assigns.push_back(Assign(lit, check.first, 0, timestamp, backjumps.back().dl));
                assignOps.push_back(AssignOp());
            }

        }

        return true;
    }

    bool XorModule::ternaryBinRule(Lit reason) {

        int var = reason.get_var();
        Var& v = vars[var];

        // unit propagation : add edges to binary constraint graph
        for (Clauses::iterator ci = v.clauses.begin();  
                ci != v.clauses.end(); ci++ ) {
            if (!clauseActive[*ci])
                continue;

            Clause* c = &clauses[*ci];
            clauseActive[*ci] = false;
            clauseActivations.push_back(*ci);

            // find the two variables that will be in the implied binary
            // xor-clause
            int e1, e2;
            if (var == c->v[0]) {
                // last two
                e1 = c->v[1];
                e2 = c->v[2];
            } else if (var == c->v[1]) {
                // first and third
                e1 = c->v[0];
                e2 = c->v[2];
            } else {
                // first two
                e1 = c->v[0];
                e2 = c->v[1];
                assert(c->v[2] == var);
            }
            // process the implied binary xor-clause


            if (!implyBinXor(c, e1, e2, reason)) {
                return false;
            }
        }
        return true;
    }
    void XorModule::incTimestamp() {
        timestamp++;
        if (timestamp == MAX_TIMESTAMP) {
            TimestampRemapper tsRemap;
            for (int i = 0; i < assigns.size(); i++) {
                tsRemap.add(assigns[i].ts);
            }
            for (int i = 0; i < assignOps.size(); i++) {
                tsRemap.add(assignOps[i].a.ts);
            }

            for (int i = 0; i < vars.size(); i++) {
                if (vars[i].ts > 0)
                    tsRemap.add(vars[i].ts);
            }
            bcg.addTimestamps(tsRemap);
            int max = tsRemap.compress();
            bcg.remapTimestamps(tsRemap);
            for (int i = 0; i < vars.size(); i++) {
                if (vars[i].ts != 0)
                    vars[i].ts = tsRemap.remap(vars[i].ts);
            } 
            for (int i = 0; i < assigns.size(); i++) {
                assigns[i].ts = tsRemap.remap(assigns[i].ts);
            }
            for (size_t i = 0; i < assignOps.size(); i++) {
                assignOps[i].a.ts = tsRemap.remap(assignOps[i].a.ts);
            }
            timestamp = max ;
        }

    }


    bool XorModule::ternaryUnaryRule(int varId) {

        D(dbg::prop,"checking clauses of x" << varId);
        assert(varId >= 0 && varId < vars.size());
        Var& v = vars[varId];
        bool impliedSomething = false;
    
        // find the representative of the equivalence class
        // where the special variable Top is (id=0)
        Fud::Result top;
        fud.find(0, top);

        // iterate all clauses of the variable 'varId'
        for (Clauses::iterator ci = v.clauses.begin(); 
                ci != v.clauses.end(); ci++) {
            if (!clauseActive[*ci])
                continue;

            Clause* c = &clauses[*ci];



            // clauses already checked have the same timestamp
            if (c->ts >= clauseTimestamp) {
                continue;
            }
            D(dbg::prop," - clause " << c->v[0] << " " << c->v[1] << " " << c->v[2] << " parity " << c->p);

            // set the timestamp of the operation
            c->ts = clauseTimestamp;

            // 'implied' holds the index of the xor-implied variable in the
            // xor-clause
            int implied = 0;

            // 'value' holds the inferred value of the xor-implied variable 
            int value;

            // 'r1' and 'r2' are the two variables in the same equivalence
            // class used to infer the value for the variable 'implied'
            int r1, r2;

            // find the representatives of the first variables in the 
            // ternary xor-clause ('c->v[0]' and 'c->v[1]')
            Fud::Result v1;
            fud.find(c->v[0], v1);   
            Fud::Result v2;
            fud.find(c->v[1], v2);   

            // if the parity w.r.t is the same ('v1.parity == v2.parity'), then
            // the variables 'c->v[0]' and 'c->v[1]' have the same value

            if (v1.var == v2.var) {
                // third variable is implied
                implied = c->v[2];
                r1 = c->v[0];
                r2 = c->v[1];
                
                value = (1 + c->p + int(v1.parity != v2.parity)) & 1;
                D(dbg::prop,"third variable implied. v1.parity " << v1.parity
                        << " v2.parity " << v2.parity);
            } else {
                Fud::Result v3;
                fud.find(c->v[2], v3);   
                if (v1.var == v3.var) {
                    // second variable is implied 
                    implied = c->v[1];
                    r1 = c->v[0];
                    r2 = c->v[2];
                    value = (1 + c->p + int(v1.parity != v3.parity)) & 1;
                    D(dbg::prop,"second variable implied. v1.parity " << v1.parity
                        << " v3.parity " << v3.parity);

                } else if (v2.var == v3.var) {
                    // first variable is implied 
                    implied = c->v[0];
                    r1 = c->v[1];
                    r2 = c->v[2];
                    value = (1 + c->p + int(v2.parity != v3.parity)) & 1;
                    D(dbg::prop,"first variable implied. v2.parity " << v2.parity
                        << " v3.parity " << v3.parity);

                }
            }
            if (implied) {
                // a variable was implied

                Fud::Result ir;
                fud.find(implied, ir);
                D(dbg::prop,"bin-xor implied x" << implied << ":=" << value 
                    << " r1=" << r1 << " r2=" << r2);              


                if (ir.var == top.var) {
                    // the variable has already a value
                    int oldValue = ir.parity == top.parity;

                    // due to internal variables we may enter here
                    if (oldValue != value) {

                        D(dbg::prop, "found a conflicting equivalence class a bit late... maybe due to internal variables");
                        cout << "FAILED!" << endl;
                        exit(1);
                        //conflict.push_back(Lit(implied, !value));

                        participated.clear();
                        assert(vars[implied].internal);
                        _explain(vars[implied], oldValue ? implied : -implied, vars[implied].r1, vars[implied].r2, timestamp, conflict, participated);


                        _explain(vars[implied], value ? implied : -implied, r1, r2, timestamp, conflict, participated);



                        removeDuplicates(conflict, false);
                        explainTimestamp++;
                        int last = conflict.size() - 1;

                    for (int i = 0; i <= last;) {

                        int v = conflict[i].get_var();
                        D(dbg::prop, "checking " << v << " i=" << i << " last=" << last);
                        if (inExplanation[v] == explainTimestamp) {
                            conflict[i] = conflict[last--];
                            D(dbg::prop, "removed duplicate: " << v << " expParity : " << vars[v].expParity);
                        } else {
                            D(dbg::prop, "first occurrence");
                            inExplanation[v] = explainTimestamp;
                            i++;
                        }
                    }
                    conflict.resize(last+1);

#ifdef VERIFY
                        verify(conflict);
#endif
                        return false;

                    }

                } else {
                    // add the implied variable to the propagation queue
                    // for assignment now
                    Lit lit(implied, value == 0);
                    assigns.push_back(Assign(lit, r1, r2, timestamp, backjumps.back().dl));
                    assignOps.push_back(AssignOp());
                    return true;
                }
            }
        }           
        return false;
    }

    bool XorModule::eqvPropagate() {

        D(dbg::prop,"eqvPropagate()");
        if (eqvQueue.empty()) {

            D(dbg::prop,"eqvQueue empty");
            return false;
        }

        // timestamping is used to check whether a xor-clause has already
        // been propagated 
        clauseTimestamp++;
        if (clauseTimestamp == MAX_TIMESTAMP) { 
            // when the clause timestamp reaches its maximum value
            // reset the timestamp in clauses and the timestamp counter
            for (int i = 0; i < clauses.size(); i++) {
                clauses[i].ts = 0;
            }
            clauseTimestamp = 1;
        }

        while (!eqvQueue.empty()) {
            int v = eqvQueue.front();
            eqvQueue.pop_front();
            inEqvQueue[v] = false;
            eqvQueueOps.push_back(EqvQueueOp(v));


//            eqvQueue.pop_front();
            if (ternaryUnaryRule(v) == true) {
                // continue propagation
                eqvQueue.push_front(v);
                inEqvQueue[v] = true;
                eqvQueueOps.push_back(EqvQueueOp().front());

//                incEqvTimestamp();
                return true;
            } 
        }
        D(dbg::prop,"eqvQueue empty");

        //incEqvTimestamp();
        return false;
    }

    bool XorModule::_propagate() {
        size_t oldImplied = implied_lits.size();
        while (1) {

            if (!assigns.empty()) {
#ifdef DEBUG
                std::string q;
                for (size_t i = 0; i < assigns.size(); i++) {
                    char buf[16];
                    Assign a = assigns[i];
                    snprintf(buf, 16, " %cx%d", a.lit.get_sign() ? '-' : ' ', a.lit.get_var());
                    q += std::string(buf);
                }
                D(dbg::prop,"propagation queue " << q);
#endif
                // increment first the edge timestamp, so that
                // new edges added to the binary constraint graph
                // do not break old explanations
                incTimestamp();

                // pop one literal from the propagation queue
                Assign a = assigns.front();
                assigns.pop_front();
                assignOps.push_back(AssignOp(a));

                int v = a.lit.get_var();
                int parity = int(a.lit.get_sign());
                /*if (vars[v].alias) {
                    D(dbg::prop,  "variable " << v << " is an assigned alias!" );
                    exit(1);

                }*/

                // find out if the variable has already been assigned
                Fud::Result top;
                fud.find(0, top);
                Fud::Result vr;
                fud.find(v, vr);   


                D(dbg::prop,"propagate(). popped x" << v << " := " << (a.lit.get_sign() == false));

                if  (top.var == vr.var) {
                    // already assigned
                    int oldParity = int(top.parity != vr.parity);

                    if (parity != oldParity) {
                        D(dbg::prop,"already assigned, conflicting value");

                        // if we get a conflicting literal from the propagation
                        // queue, there are two possibilities: 
                        // either i) it is a xor-assumption that conflicts with a previously
                        // inferred xor-implied literal, or ii) it is a xor-implied literal
                        // that conflicts with a previously assigned xor-assumption
                        if (vars[v].r1 != 0) {
                            // case i) xor-assumption
                            assert(a.r1 == 0);

                            // we explain the previous xor-implied literal
                            // and get a conflict clause
                            conflict.clear();
                            conflict.push_back(Lit(v, !a.lit.get_sign()));

                            participated.clear();

                            _explain(vars[v], a.lit.get_sign() ? -v : v, a.r1, a.r2, a.ts, conflict, participated);
                            removeDuplicates(conflict, true);

                            


                            //                            bcg.explainPath(a.r1, a.r2, a.ts, conflict, participated);
                            stats.xorExplanations++;
                            stats.xorExplanationLits += conflict.size();
#ifdef VERIFY
                            verify(conflict);
#endif


                        } else {
                            // case ii) xor-implied literal

                            if (a.r1 != 0) {

                                // we explain the new xor-implied literal
                                // and get a conflict clause
                                explain(a.lit, conflict);                        
                            } else {

                                addPendingImplied();


                                explain(Lit(v, !a.lit.get_sign()), conflict);                        

                                stats.xorExplanations++;
                                stats.xorExplanationLits += conflict.size();
#ifdef DEBUG
                                printLiterals(conflict);
#endif
                                //                                    exit(1);
                            }
                        }

                        assert(!conflict.empty());
                        return false;
                    } else {
                        if (vars[v].ts != 0) {
                            D(dbg::prop,"already assigned ts=" << vars[v].ts << ", same value -> ignoring");
#ifdef CHECK
                            checkNoActiveClauses(v);
#endif
                            // same value, ignore assignment (if not implied)
                            continue;
                        }
                    }
                } 

                // at this point, the variable is not assigned
                //assert(vars[v].r1 == 0);

                D(dbg::prop,"assigning x" << v << " := " << (a.lit.get_sign() == false) << " dl=" << a.dl);
                // mark the variable as implied (if it is, xor-assumptions have the reason a.r1==0)
                vars[v].r1 = a.r1;
                vars[v].r2 = a.r2;
                vars[v].ts = a.ts;
                vars[v].dl = a.dl;


                if (a.r1) {
                    // it is a xor-implied literal
                    if (!vars[v].internal)
                        implied_lits.push_back(a.lit);
                    else
                        implied_internals.push_back(v);
                    if (a.r2) {
                        // if the reason has two terms, then it is a ternary ->
                        // unary xor-implied literal
                        stats.ternaryXorImplied++;

                    }
                    else {
                        stats.binaryXorImplied++;
                    }
                } else {
                    xorAssumptions.push_back(v);

                }

                // storage for holding the equivalence class
                //                std::vector< std::pair<int, int> > subgraph;
                subgraph.clear();

                if (top.var != vr.var) {
                    // assignment of the equivalence class 

                    // find the other variables in the same equivalence class
                    bcg.subgraph(v, subgraph);

                    D(dbg::prop,"union(x" << v << ",x0,p="<<parity<<")");
                    D(dbg::prop,"pushEdge(x" << v << ", x0, p=" << parity << ", r=" 
                            << (a.lit.get_sign() ? "-" : "") << v << ", ts=" << timestamp);
                    // put the variable in the same equivalence class with the
                    // special variable Top
                    fud.union_(v, 0, parity, a.lit);

                    // add an edge to the binary constraint graph
                    bcg.pushEdge(v, 0, parity, a.lit, timestamp, backjumps.back().dl);
                }


                if (top.var != vr.var) {
                    D(dbg::prop,"the equivalence class was assigned. subgraph of size " << subgraph.size());
                    for (Subgraph::iterator i = subgraph.begin(); i != subgraph.end(); i++) {
                        std::pair<int, int> implied = *i;
                        // never try to assign the special symbol Top
                        if (implied.first == 0)
                            continue;

                        bool sign = (implied.second + parity) & 1;
                        D(dbg::prop,"up implied. x" << implied.first << " by x" << v << " par " << implied.second);

                        Lit lit(implied.first, sign);
                        incTimestamp();
                        assigns.push_back(Assign(lit, implied.first, 0, timestamp, backjumps.back().dl));
                        assignOps.push_back(AssignOp());

                    }
                }
                // check for implied binary xor-clauses and conflicts
                if (!ternaryBinRule(a.lit))  {
                    assert(conflict.empty() == false);
                    return false;
                }
            }

            if (implied_lits.size() > oldImplied) {
                D(dbg::prop,"implied something. back to SAT-solver");
                break;
            }
            if (assigns.empty() == false)
                continue;

            if (eqvPropagate() == false)
                break;

            if (implied_lits.size() > oldImplied) {
                D(dbg::prop,"implied something. back to SAT-solver");
                break;
            }
        }
        D(dbg::prop,"xor-propagation saturated");
        return true;

    }

    void XorModule::setup() {
        if (initialized)
            return;
        initialized = true;
        fud.setup(vars.size());
        bcg.setup(vars.size());
        //assigns.setup(vars.size() * 2 + 1);
        //eqvQueue.setup(vars.size() + 1);
        conflictVar = 0;
    }
    XorModule::XorModule(Interface& owner_) : owner(owner_), fud(settings), timestamp(1),  clauseTimestamp(0), initialized(false), numGraphs(0)
    {
        explainTimestamp = 0;
        vars.push_back(Var());
        inEqvQueue.push_back(false);
        inParticipated.push_back(0);
        inExplanation.push_back(0);

    }

    int XorModule::new_var() {
        int id = vars.size();
        vars.push_back(Var());
        inEqvQueue.push_back(false);
        inParticipated.push_back(0);
        inExplanation.push_back(0);
        fud.setup(vars.size());
        bcg.setup(vars.size());
#ifdef VERIFY
        while (1) {
            if (simplex.new_var() == id)
                break;
        }
#endif

        return id;
    }
    void XorModule::add_ternary_xor(const std::vector<int>& lhs, const bool rhs) {
        assert(lhs.size() == 3);
        int parity = 1 - int(rhs);
        for (int i = 0; i < 3; i++) {
            int v1 = lhs[i%3];
            int v2 = lhs[(i+1)%3];
            if (v1 > v2) {
                int tmp = v1;
                v1 = v2;
                v2 = tmp;
            }
            aliasMap[ make_pair(v1,v2) ] = clauses.size();
        }
#ifdef VERIFY
        bool sat = simplex.is_sat();
        vector<unsigned int> vlhs;
        copy(lhs.begin(), lhs.end(), back_inserter(vlhs));
        simplex.add_equation(vlhs, rhs);
        unsigned int bt = simplex.set_backtrack_point();
         
        D(dbg::prop,  "model: " << bx::toString(model_lits));
        for (size_t i2 = 0; i2 < model_lits.size(); i2++) {
            Lit &l = model_lits[i2];
            if (vars.size() <= l.get_var())
                continue;
            Var& v = vars[l.get_var()];
            simplex.assume(l.get_var(), !l.get_sign());

            if (sat && !simplex.is_sat()) {
                D(dbg::prop,  "Broken ternary xor : " << bx::toString(lhs) << " = " << rhs<< endl);
                D(dbg::prop,  "Instance became unsatisfiable!" << endl);
//                exit(1);
            }
        }
 
        simplex.backtrack(bt);
          

#endif
        clauses.push_back(Clause(lhs[0], lhs[1], lhs[2], parity));
        clauseActive.push_back(true);

        D(dbg::prop,"clause " << lhs[0] << " " << lhs[1] << " " << lhs[2] << "  = " << (1-parity));


        for (int i = 0; i < 3; i++) {
            int v = lhs[i];

            assert(v > 0 && v < vars.size());
            vars[v].clauses.push_back(clauses.size() - 1);
        }      
    }


    void XorModule::getCommonAliasMapPairs(set<int>& lhs, set<pair<int, int> >& excluded, vector<pair<int, int> >& pairs) {

        pairs.clear();
        if (lhs.empty())
            return;
        set<int> taken;
        for (set<int>::iterator i = lhs.begin(); i != lhs.end(); i++) {
            set<int>::iterator i2 = i;
            i2++;
            
            if (taken.find(*i) != taken.end())
                continue;
            for (; i2 != lhs.end(); i2++) {
                if (taken.find(*i2) != taken.end())
                    continue;
                int v1 = *i;
                int v2 = *i2;
                if (v1 > v2) {
                    int tmp = v1;
                    v1 = v2;
                    v2 = tmp;
                }
                pair<int, int> p = make_pair(v1,v2);
                if (aliasMap.find(p) != aliasMap.end() && excluded.find(p) == excluded.end()) {
                    
                    pairs.push_back(p);
                    taken.insert(v1);
                    taken.insert(v2);
                    break;
                }
            }
        }
    }

    void XorModule::optimize_and_add_xor(const std::vector<int>& lhs, bool rhs) {
        set<int> varsLeft;
        vector<pair<int, int> > commonPairs;
        D(dbg::prop,  "\noptimize " << bx::toString(lhs) << " = " << rhs << endl);
        for (size_t i = 0; i < lhs.size() ; i++) {
            varsLeft.insert(lhs[i]);
        }
        set< pair<int, int> >dealt;
        do {

            getCommonAliasMapPairs(varsLeft, dealt, commonPairs);

            if (!commonPairs.empty()) {
                for (size_t i = 0; i < commonPairs.size(); i++) {
                    pair<int, int>& p = commonPairs[i];
                    
                    // D(dbg::prop, "common pair " << p.first << " " << p.second);
                    D(dbg::prop,  "common pair " << p.first << " " << p.second << endl);

                    if (varsLeft.find(p.first) == varsLeft.end()
                            || varsLeft.find(p.second) == varsLeft.end()) {
                        D(dbg::prop,  "one already eliminated. skipping" << endl);
                        continue;
                    }
                    dealt.insert(p);
                    Clause&c = clauses[aliasMap[p]];
                    int varId = -1;
                    D(dbg::prop,  "clause " << c.v[0] << " " << 
                            c.v[1] << " " << c.v[2] << " p=" << c.p);
                    for (int i2 = 0; i2 < 3; i2++) { 

                        if (c.v[i2] != p.first && c.v[i2] != p.second) {
                            varId = c.v[i2];
                        }
                    }


                    D(dbg::prop,  endl);
                    if (!c.p) {
                        rhs = !rhs;
                        D(dbg::prop,  "parity inverted due to " << varId << endl);

                    }
                    assert(varId != -1);

                  D(dbg::prop,  "existing alias: " << varId << endl);
                    stats.optExistingUsed++;


                    if (varsLeft.find(varId) == varsLeft.end())
                        varsLeft.insert(varId);
                    else 
                        varsLeft.erase(varId);
                    
                    varsLeft.erase(p.first);
                    varsLeft.erase(p.second);

                }

            } else if (varsLeft.size() > 3) {
                vector<int> part;
                vector<int> handled;
                vector<int> extras;
                int addExtras = varsLeft.size() - 3;
                for (set<int>::iterator i = varsLeft.begin(); 
                        i != varsLeft.end() && addExtras > 0; i++) {
                    part.push_back(*i);
                    if (part.size() == 2) {
                        copy(part.begin(), part.end(), back_inserter(handled));
                        
                        int extra = owner.xorNewVar();
                        stats.optNewVars++;
                        vars[extra].internal = true;
                        part.push_back(extra);
                        D(dbg::prop, "adding tree-like xor " << bx::toString(part));
                        add_ternary_xor(part, false);
                        extras.push_back(extra);
                        part.clear();
                        addExtras--;
                    }
                }
                for (size_t i = 0; i < extras.size(); i++)
                    varsLeft.insert(extras[i]);
                for (size_t i = 0; i < handled.size(); i++)
                    varsLeft.erase(handled[i]);
            }

        } while (varsLeft.size() > 3);

        vector<int> newLhs;
        for (set<int>::iterator i = varsLeft.begin(); i != varsLeft.end();
                i++) {
            newLhs.push_back(*i);
        }

        if (newLhs.empty()) {
            D(dbg::prop,  "empty clause! rhs = " << rhs << endl);
            if (rhs)
                dl0Lits.push_back(Lit(0, true));
            return;
        } else 
        if (newLhs.size() == 1) {
            stats.optUnit++;
            Var& v = vars[newLhs[0]];
            v.internal = false;
            dl0Lits.push_back(Lit(newLhs[0], rhs == false));
            D(dbg::prop,  "unit clause! " << newLhs[0] << " = " << rhs << endl);
        } else if (newLhs.size() == 2) {
            stats.optBinary++;


            D(dbg::prop,  "adding binary clause ! " << bx::toString(newLhs));
            int extra = owner.xorNewVar();
            stats.optNewVars++;

            newLhs.push_back(extra);
            add_ternary_xor(newLhs, !rhs);
            dl0Lits.push_back(Lit(extra, false));
#ifdef VERIFY
            model_lits.push_back(Lit(extra, false));
#endif
        } else {
            getCommonAliasMapPairs(varsLeft, dealt, commonPairs);
            if (commonPairs.empty()) {


                D(dbg::prop,  " adding ternary xor " << bx::toString(newLhs) << " = " << rhs << endl);

                add_ternary_xor(newLhs, rhs);
            } else {
                 D(dbg::prop,  " not adding ternary xor " << bx::toString(newLhs) << " = " << rhs << endl);

            }
        }
    }

    void XorModule::add_long_xor(const std::vector<int>& lhs, const bool rhs) {

        vector<int> part;
        int extra = 0;
        for (size_t i = 0; i < lhs.size(); i++) {
            part.push_back(lhs[i]);
            if (part.size() == 2 && i < lhs.size() - 2) {
                extra = owner.xorNewVar();
                vars[extra].internal = true;
                part.push_back(extra);
                add_ternary_xor(part, false);
                part.clear();                
                part.push_back(extra);
            }
        }
        add_ternary_xor(part, rhs);

    }
    void XorModule::add_equation(const std::vector<int>& lhs, const bool rhs) {



      if (!initialized) {
          set<int> llhs;
          for (size_t i = 0; i < lhs.size(); i++) {
              assert(llhs.find(lhs[i]) == llhs.end());
              llhs.insert(lhs[i]);
          }
          pendingXors.insert(make_pair(llhs, rhs));
          return;
      }
   //   if (lhs.size() == 3) {

//          add_ternary_xor(lhs, rhs); 
    //  } else {
          if (!settings.optimizeClauses) {
              add_long_xor(lhs, rhs);
          } else {
              optimize_and_add_xor(lhs, rhs);
          }
                      
      //}



    }
    bool XorModule::propagate() {

#ifdef CHECK
        checkConsistency();
#endif
        bool result = _propagate();
#ifdef CHECK
        checkConsistency();
        checkTimestamps();
#endif

        return result;

    }
    void XorModule::assume(const int var, const bool value) {

        if (!initialized)
            setup();
        assert(conflict.empty());
        assert(var > 0 && var < vars.size());

       incTimestamp();
        
       D(dbg::prop, "assign at dl=" << backjumps.back().dl);
       Assign a(Lit(var, value == false), 0, 0, timestamp, backjumps.back().dl);
        assigns.push_back(a);

        assignOps.push_back(AssignOp());
        D(dbg::prop,"adding assign op. Pop()");
    }

    int XorModule::newBinXor(int r1, int r2, int dl, int ts) {
        if (r1 > r2) {
            int tmp = r1;
            r1 = r2;
            r2 = tmp;
        }


        AliasMap::iterator a = aliasMap.find(make_pair(r1,r2));

        int varId;
        Fud::Result r1cls, r2cls;

        fud.find(r1, r1cls);
        fud.find(r2, r2cls);
        assert(r1cls.var == r2cls.var);
        int rhs = (r1cls.parity == r2cls.parity);

        if (a != aliasMap.end()) {
            
            Clause&c = clauses[a->second];
            for (int i = 0; i < 3; i++) { 
                if (c.v[i] != r1 && c.v[i] != r2)
                    varId = c.v[i];
            }
            if (c.p != 1 - rhs)
                varId = -varId;
            D(dbg::prop, "found existing variable for pair " << r1 << " " << r2 << ": " << varId);
        } else {
            varId = owner.xorNewVar();
            vector<int> lhs;
            lhs.push_back(varId);
            lhs.push_back(r1);
            lhs.push_back(r2);
            D(dbg::prop, "Adding a new clause " << varId << " " << 
                r1 << " " << r2 << " p=" << (1-rhs));

            add_equation(lhs, rhs);
            clauseActive.back() = false;
            Var& var = vars[varId];
            var.r1 = r1;
            var.r2 = r2;
            var.alias = true;
            D(dbg::prop, " current edgecount " << bcg.edgeCount());
            for (int bj = backjumps.size() - 1; bj >= 0; bj--) {
                //            D(dbg::prop, "backjump " << bj << " edges = " << backjumps[bj].edges);
                Backjump& b = backjumps[bj];
                if (b.dl == dl) {
                    D(dbg::prop, "alias " << varId << " at level " << dl);
                    var.ts = ts;
                    b.binXorActivations.push_back(clauseActive.size() - 1);
                    b.aliasVars.push_back(varId);
                    Lit lit(varId, false);
                    assert (bj+1 < backjumps.size());
                    int edges = backjumps[bj+1].edges;
                    D(dbg::prop, "inserting to edgeCount " << edges);
                    D(dbg::prop, "prev level edgeCount " << b.edges);
                    bcg.insertEdge(edges, r1, r2, 1 - rhs, lit, var.ts+1, dl);
                    for (int b = bj+1; b < backjumps.size(); b++) {
                        backjumps[b].edges += 2;
                    }
                    break;
                } 
            }

            owner.xorInsertToTrail(varId, dl);
        }


/*        Fud::Result top;
        fud.find(0, top);
        fud.union_(0, varId, 0);*/

//        bcg.toGraphviz("bcg.dot", r1, r2, timestamp, false, bx::toString(varId));

        return varId;
    }

    void XorModule::_explain(Var& v, int var, int r1, int r2, int ts, std::vector<Lit>& explanation, std::vector<int>& participated) {
                D(dbg::prop, "_explain(" << var << ",r1=" << r1 << ",r2=" << r2 << ",ts=" << ts);

            if (r2 == 0) {

                Lit l2 (abs(var), var < 0);
                bcg.fastExplain(l2, /*settings.pathExplanationLength - 1, */explanation, participated);
                //assert(explanation.size()-firstPos <= settings.pathExplanationLength);


            } else {
/*                if (v.exp.empty() == false ) {
                    std::copy(v.exp.begin(), v.exp.end(), std::back_inserter(explanation));;
                    std::copy(v.path.begin(), v.path.end(), std::back_inserter(participated));;

                } else {
                    size_t firstPos = explanation.size();
                    size_t firstParticipated = participated.size();
    */
                    std::vector<Lit> exp, tmpExp;

                    std::vector<int> part, tmpPart;

                    bcg.explainPathNoConflict(r1, r2, ts, exp, part); // explanation, participated);


                    if (exp.size() > 2 && settings.createVars)  {


                        int current = backjumps.back().dl;
                        D(dbg::prop, "Current dl " << current);
//                        printLiterals(exp);
                        int p = 0;
                        int left=-1;

                        int maxDl = 0, maxTs = 0;
                        for (size_t i = 0; i < exp.size(); i++) {
                            pair<int, int> info = bcg.getInfo(part[i], part[i+1], ts);
                            int cts = info.first;
                            int dl = info.second; 
                            D(dbg::prop, "var " << exp[i].get_var() );
                            D(dbg::prop,  part[i] << " -> " << part[i+1] << " ts=" << cts << " dl=" << dl << endl);
                            if (dl < current && part[i+1] != r2 && part[i+1] != r1) {
                                if (left == -1)
                                    left = part[i];
                                if (dl > maxDl)
                                    maxDl = dl;
                                if (cts > maxTs)
                                    maxTs = cts;

                                tmpExp.push_back(exp[i]);
                                tmpPart.push_back(part[i]);

                                p++;     
                            } else {

                                if (p > 1) {

                                    D(dbg::prop, "Alias for " << p << " terms" );
                                    D(dbg::prop, "new bin-xor " << left << " xor " << part[i] << " dl=" << maxDl << " ts=" << maxTs );
                                    
                                    int alias = newBinXor(left, part[i], maxDl, maxTs);

//                                    bcg.toGraphviz("alias.dot", left, part[i], maxTs, false);

                                    explanation.push_back(Lit(abs(alias), !(alias < 0)));

                                    std::copy(tmpPart.begin(), tmpPart.end(), 
                                                std::back_inserter(participated));

                                } else {
                                    for (int i2 = 0; i2 < tmpExp.size(); i2++)
                                        D(dbg::prop, bx::toString(tmpExp[i2]) );

                                    std::copy(tmpExp.begin(), tmpExp.end(), 
                                            std::back_inserter(explanation));
                                    std::copy(tmpPart.begin(), tmpPart.end(), 
                                            std::back_inserter(participated));

                                }
                                tmpExp.clear();
                                tmpPart.clear();
                                D(dbg::prop, bx::toString(exp[i]) );
                              
                                explanation.push_back(exp[i]);
                                participated.push_back(part[i]);
                                p = 0;

                            
                                left = -1;

                                maxTs = 0;
                                maxDl = 0;
                            }

                            D(dbg::prop, "Exp " << i << " : " << bx::toString(exp[i]) << " dl=" << dl );
                                
                        }

                        for (int i2 = 0; i2 < tmpExp.size(); i2++)
                            D(dbg::prop, bx::toString(tmpExp[i2]) );
                        tmpPart.push_back(part.back());

                        if (p > 1) {

                            D(dbg::prop, "Alias for " << p << " terms" );
                                    D(dbg::prop, "new bin-xor " << left << " xor " << part.back() << " dl=" << maxDl << " ts=" << maxTs );

                            int alias = newBinXor(left, part.back(), maxDl, maxTs);
                            explanation.push_back(Lit(abs(alias), !(alias < 0)));

//                            std::copy(tmpExp.begin(), tmpExp.end(), 
                            //        std::back_inserter(explanation));
                            std::copy(tmpPart.begin(), tmpPart.end(), 
                                    std::back_inserter(participated));


                        } else {
                            std::copy(tmpExp.begin(), tmpExp.end(), 
                                    std::back_inserter(explanation));
                            std::copy(tmpPart.begin(), tmpPart.end(), 
                                    std::back_inserter(participated));
                        }


                        D(dbg::prop, bx::toString(explanation));
                        D(dbg::prop, bx::toString(part) );
                        D(dbg::prop, part.size() << " terms in participated" );
                        
                    } else {
                        std::copy(exp.begin(), exp.end(), std::back_inserter(explanation));
                        std::copy(part.begin(), part.end(), std::back_inserter(participated));
                    }



/*                    std::copy(explanation.begin() + firstPos, explanation.end(),  std::back_inserter(v.exp));
                    std::copy(participated.begin() + firstParticipated, participated.end(),  std::back_inserter(v.path));

                }*/

            }


    }

    void XorModule::explain(Lit lit, std::vector<Lit>& explanation)  {
//                 bcg.toGraphviz("bcg.dot", 0,0,timestamp,false);
        D(dbg::state, toString());
/*        if (settings.fastExp) {
            explanation.clear();
            explanation.push_back(lit);

            Var v = vars[lit.get_var()];
            D(dbg::prop, "explaining " << (lit.get_sign() ? "-" : "")
                    << lit.get_var());
            fud.explain(explanation, v.r1, v.r2, stats.evenParityEliminated);
            stats.xorExplanations++;
            stats.xorExplanationLits += explanation.size();


//        bcg.toGraphviz("bcg.dot", v.r1,v.r2, timestamp, false, "");
//            fud.toGraphviz(bx::toString(timestamp) + "fud.dot");
#ifdef VERIFY
        verify(explanation);
#endif


            return;
        }
*/
        explainTimestamp ++;


        long long prevEvenParityEliminated = stats.evenParityEliminated;

        participated.clear();
        if (settings.evenParityElimination)
            clearExpParity.clear();
        explanation.clear();
        explanation.push_back(lit);
        if (settings.evenParityElimination) {

            clearExpParity.push_back(lit.get_var());
            vars[lit.get_var()].expParity++;
        }
        //toExplain.clear();
        toExplain.push(ToExplain(lit.get_var() * (lit.get_sign() ? -1 : 1), timestamp));

        D(dbg::prop,"toExplain.push(" << lit.get_var() << ")");

        //        std::D(dbg::prop, "START" << std::endl;
        while (!toExplain.empty()) {

            int var = toExplain.top().var;
            D(dbg::prop, "popped toExplain " << var << " ts=" << toExplain.top().ts);

            toExplain.pop();
            Var& v = vars[abs(var)];                
            if (v.expParity % 2 == 0 && settings.evenParityElimination) {
                D(dbg::prop, "not explaining " << var << " because of even parity");
                stats.evenParityEliminated++;

                continue;
            }



            assert(v.r1 != 0);

            //            std::D(dbg::prop, "EXPLAIN " << var << std::endl;
            size_t firstPos = explanation.size();
            size_t firstParticipated = participated.size();

            if (settings.fastExp) {
                fud.explain(explanation, v.r1, v.r2, stats.evenParityEliminated);
            } else {

                _explain(v, var, v.r1, v.r2, v.ts, explanation, participated);
            }

            if (settings.evenParityElimination) {
                for (size_t i = firstPos; i < explanation.size(); i++) {
                    int v = explanation[i].get_var();
                    vars[v].expParity++;
                    if (vars[v].expParity == 1)
                        clearExpParity.push_back(v);
                }
            }



            int pos = firstParticipated;
            int last = participated.size() - 1;
            while (pos <= last) { 

                if (inParticipated[participated[pos]] == explainTimestamp) {
                    D(dbg::prop, "participated pos " << pos);
                    D(dbg::prop, "participated last " << last);
                    D(dbg::prop, "participated size " << participated.size());

                    participated[pos] = participated[last]; 
                    last--;
                    continue;
                } 
                inParticipated[participated[pos]] = explainTimestamp;
                pos++;
            }
            participated.resize(last+1);

    pos = firstPos;
    last = explanation.size() - 1;
    D(dbg::prop,"firstPos " << firstPos << " explanation.size() " << explanation.size());
    while (pos <= last) {

        Lit& l = explanation[pos];

        if (inExplanation[l.get_var()] == explainTimestamp) {
            D(dbg::prop, "" << l.get_var() << " already in the explanation");

            explanation[pos] = explanation[last--]; 
            continue;
        }
        inExplanation[l.get_var()] = explainTimestamp;
        Var& vl = vars[l.get_var()];
        //                std::D(dbg::prop, "GOT " << ::toString(l)<< std::endl;
        D(dbg::prop,"explanation[" << pos << "] : " << l.get_var() << " ts=" << vl.ts << " last bj=" << backjumps.back().timestamp
                << " r1=" << vl.r1 << " r2=" << vl.r2);
        if (settings.deepCuts && (vl.r1 != 0) || vl.internal/* || (vl.r1 != 0 && vl.dl >= backjumps.back().dl)*/) {
            //                    std::D(dbg::prop, "OMG" << std::endl;
            toExplain.push(ToExplain(l.get_var() * (l.get_sign() ? 1 : -1), vl.ts));

            D(dbg::prop,"toExplain.push(" << l.get_var() << ")");

            explanation[pos] = explanation[last--]; // .back();
            //                    explanation.pop_back();
        } else {
            pos++;
        }
    }
    explanation.resize(last+1);


            
        }

        if (settings.evenParityElimination) {

            D(dbg::prop, "explanation now " << bx::toString(explanation));
            D(dbg::prop, "toExplain loop done");
           int last = explanation.size() - 1;
            
            for (int i = 1; i <= last; ) {
                Var& v = vars[explanation[i].get_var()];

                if (v.expParity % 2 == 0) {
                    D(dbg::prop, "evenParityEliminated " << explanation[i].get_var()<<  " : " << v.expParity);
                    explanation[i] = explanation[last--];
                    stats.evenParityEliminated++;
                }  else
                    i++;
            }


            explanation.resize(last+1);
            /*
            for (set<Clause*>::const_iterator i = activeClauses.begin();
                    i != activeClauses.end(); i++) {
                Clause* c = *i;
                vars[c->v[0]].expParity = 0;
                vars[c->v[1]].expParity = 0;
                vars[c->v[2]].expParity = 0;
            }
            */
            for (size_t i = 0; i < clearExpParity.size(); i++)
                vars[clearExpParity[i]].expParity = 0;

        }
#ifdef VERIFY
        verify(explanation);
#endif

        int last = explanation.size() - 1;
            
        bool rhs = true;
        for (int i = 1; i <= last; ) {

            Var& v = vars[explanation[i].get_var()];
            if (v.dl == 0) {
                D(dbg::prop, "eliminated due to dl=0 " << explanation[i].get_var()<<  " : " << v.expParity);
//                if (explanation[i].get_sign())
//                    rhs = !rhs;

                explanation[i] = explanation[last--];

                stats.dl0Eliminated++;
            }  else
                i++;
        }


        explanation.resize(last+1);


        if (settings.storeXorExp 
                && stats.evenParityEliminated > prevEvenParityEliminated
                && explanation.size() >= 2
                &&  explanation.size() <= settings.storeXorExp) {
            set<int> varSet;

            for (size_t i = 0; i < explanation.size(); i++) {
                varSet.insert(explanation[i].get_var());
                if (explanation[i].get_sign())
                    rhs = !rhs;
            }
            pair<PendingXors::iterator,bool> i = 
                pendingXors.insert(make_pair(varSet, rhs));


            if (i.second) {

                stats.learntClauses++;
//                bcg.toGraphviz("bcg" + bx::toString(varSet) + "_" + bx::toString(rhs) + ".dot", 0,0,timestamp,false);

                D(dbg::prop, "Adding pending xor " 
                        << bx::toString(varSet)
                        << " = " << rhs);
                D(dbg::prop, "explanation: " << bx::toString(explanation));
            }
        }


        stats.xorExplanations++;
        stats.xorExplanationLits += explanation.size();
        switch(explanation.size()) {
            case 1:
                stats.unaryExplanations++;
                break;
            case 2: 
                stats.binaryExplanations++;
                break;
            case 3:
                stats.ternaryExplanations++;
                break;
            case 4:
                stats.quadExplanations++;
                break;
        }
                
    }
    void XorModule::simplify(std::vector<Lit>& dl0Lits_) {
        assert(backjumps.size() > 0);
        assert(backjumps.back().dl == 0);
        for (PendingXors::iterator i = pendingXors.begin(); 
                i != pendingXors.end(); i++) {

            D(dbg::prop, "Storing pending xor : " 
                    << bx::toString(i->first) <<  " = "  
                    << i->second);
            vector<int> lhs;

            for (set<int>::const_iterator i2 = i->first.begin();
                    i2 != i->first.end(); i2++)
                lhs.push_back(*i2);
#ifdef VERIFY
            Simplex splex;
            FILE* f = fopen("splex.tr", "w");
            splex.set_record_stream(f);
            while (splex.new_var() < vars.size()) {}
            for (size_t i2 = 0; i2 < clauses.size(); i2++) {
                vector<unsigned int> lhs;
                bool rhs = true;
                
                Clause& c = clauses[i2];
                for (size_t i3 = 0; i3 < 3; i3++)
                    lhs.push_back(c.v[i3]);
                rhs = 1 - c.p;
                splex.add_equation(lhs, rhs);
            }
            vector<unsigned int> llhs;
            copy(lhs.begin(), lhs.end(), back_inserter(llhs));

            splex.add_equation(llhs, i->second);
            for (size_t i2 = 0; i2 < implied_lits.size(); i2++) {
                Lit &l = implied_lits[i2];
                Var& v = vars[l.get_var()];
                if (v.dl == 0)
                    splex.assume(l.get_var(), !l.get_sign());
            }
            if (splex.is_sat() == false) {
                D(dbg::prop, "possibly broken pending xor!");
            }


        
        fclose(f);
#endif

            add_equation(lhs, i->second);

        }
        pendingXors.clear();

        dl0Lits_.clear();
        copy(dl0Lits.begin(), dl0Lits.end(), back_inserter(dl0Lits_));
        dl0Lits.clear();
        cout << "xor clauses : " << clauses.size() << endl;
    }
    int XorModule::set_backtrack_point(int dl) {
        if (!initialized)
            setup();
        int s = (int) backjumps.size();
#ifdef DEBUG
        std::string state = toString();
#endif
        backjumps.push_back(Backjump(fud.unionCount(), bcg.edgeCount(), implied_lits.size(), implied_internals.size(), 
                    xorAssumptions.size()));
        backjumps.back().assignOps = assignOps.size();
        backjumps.back().eqvQueueOps = eqvQueueOps.size();
        backjumps.back().clauseActivations = clauseActivations.size();


        backjumps.back().timestamp = timestamp;
        backjumps.back().dl = dl;
#ifdef DEBUG_NO
        backjumps[backjumps.size() - 1].state = state;
        D(dbg::prop,"Stored state: " << state);
#endif
        D(dbg::prop,"set backtrack point " << s << " dl=" <<dl);
        return s;
    }

    void XorModule::backtrack(int backtrack_point) {


        D(dbg::prop,"backtracking to " << backtrack_point);
        assert(backtrack_point < backjumps.size());
        Backjump& b = backjumps[backtrack_point];
       
        D(dbg::prop, "decision level=" << b.dl);
        for (int i = backtrack_point; i < backjumps.size(); i++) {
            Backjump& b2 = backjumps[i];
            
            for (int i2 = 0; i2 < b2.aliasVars.size(); i2++) {
                D(dbg::prop, "reseting alias state for " << b2.aliasVars[i2]);
                Var& v = vars[b2.aliasVars[i2]];
                v.alias = false;
                v.ts = 0;
                v.r1 = 0;
                v.r2 = 0;
                
            }
            
            for (int i2 = 0; i2 < b2.binXorActivations.size(); i2++) {
                clauseActive[b2.binXorActivations[i2]] = true;
                D(dbg::prop, "activating clause " << b2.binXorActivations[i2]);
            }

        }
        fud.deunion(b.unions);
        bcg.popEdges(b.edges);
        for (int i = b.implied; i < implied_lits.size(); i++) {
            Lit l = implied_lits[i];
            vars[l.get_var()].exp.clear();
            vars[l.get_var()].path.clear();

            vars[l.get_var()].r1 = 0;
            vars[l.get_var()].r2 = 0;
            vars[l.get_var()].ts = 0;
        }

        for (int i = b.internals; i < implied_internals.size(); i++) {
            Var& v = vars[implied_internals[i]];
            v.ts = v.r1 = v.r2 = 0;
        }
             
        for (int i = assignOps.size() - 1; i >= b.assignOps; i--)  {
            AssignOp& ao = assignOps[i]; 
            if (ao.op == AssignOp::Push) {
                D(dbg::prop,"pushing back assign " << (ao.a.lit.get_sign() ? "-x" : "x") << ao.a.lit.get_var());

                assigns.push_front(ao.a);
            } else {
                D(dbg::prop,"popping assign");
                assigns.pop_back();
            }
        }
        assignOps.resize(b.assignOps);
        for (int i = eqvQueueOps.size() - 1; i >= b.eqvQueueOps; i--) {
            EqvQueueOp& eo = eqvQueueOps[i]; //.back();
            if (eo.op == EqvQueueOp::Push) {
                D(dbg::prop,"pushing back eqvQueue " << eo.v);
                eqvQueue.push_front(eo.v);
                inEqvQueue[eo.v] = true;
            } else if (eo.op == EqvQueueOp::PopFront) {
                D(dbg::prop,"pop_front eqvQueue");

                int v = eqvQueue.front();
                eqvQueue.pop_front();
                inEqvQueue[v] = false;

            } else {
                D(dbg::prop,"pop_back eqvQueue");
                int v = eqvQueue[eqvQueue.size() - 1];
                inEqvQueue[v] = false;

                eqvQueue.pop_back();
            }
        }
        eqvQueueOps.resize(b.eqvQueueOps);
        

        for (int i = clauseActivations.size() - 1 ; i >= b.clauseActivations; i--) {
            clauseActive[clauseActivations[i]] = true;
        }
        clauseActivations.resize(b.clauseActivations);

        implied_lits.resize(b.implied);
        implied_internals.resize(b.internals);

        for (int i = b.assigned; i < xorAssumptions.size(); i++) {
            vars[xorAssumptions[i]].ts = 0;
        }
        xorAssumptions.resize(b.assigned);

#ifdef DEBUG_NO
        std::string state = b.state;
#endif
        backjumps.resize(backtrack_point);

        //eqvQueue.clear();
#ifdef DEBUG_NO
        if (toString() != state) {
            D(dbg::prop,"BACKTRACK FAILED!!!!");
            D(dbg::prop,"ORIGINAL : ");
            D(dbg::prop,b.state);
            D(dbg::prop,"RESTORED : ");
            D(dbg::prop,toString());
        }
        assert(toString() == state);

        D(dbg::prop,"restored state: " << toString());
#endif

#ifdef CHECK
        for (size_t i = 1; i < vars.size(); i++) {
            if (vars[i].ts != 0)
                checkNoActiveClauses(i);
        }
#endif
        conflict.clear();
        participated.clear();
        //incEqvTimestamp();
    }

void XorModule::remove_clauses_of(int var) {
    // TODO
}
#ifdef CHECK
void XorModule::checkNoActiveClauses(int var) {
    Var& v = vars[var];


        for (Clauses::iterator ci = v.clauses.begin();  
                ci != v.clauses.end(); ci++ ) {
            if (clauseActive[*ci])
                cout << "Var x" << var << " has active clause!" << endl;
            assert (!clauseActive[*ci]);
        }


}
void XorModule::checkConsistency() {


    Fud::Result top;
    fud.find(0, top);
    vector<int> implied;
    implied.resize(vars.size());
    for (int i = 0; i < implied_lits.size(); i++) {
        Lit l = implied_lits[i];

        Var& v = vars[l.get_var()];
        assert(v.r1 != 0 || v.dl == 0);
        implied[l.get_var()] = 1;

    }

    for (int i = 1; i < vars.size(); i++) {
        Fud::Result r;
        fud.find(i, r);
        vector< pair<int, int> > sg;
        bcg.subgraph(i, sg);
        bool hasTop1 = r.var == top.var;
        bool parity1 = r.parity == top.parity;
        bool hasTop2 = false;
        bool parity2 = false;
        if (implied[i])
            assert(vars[i].r1 != 0 || vars[i].dl == 0);

        if (top.var == r.var) {
/*            if (conflict.empty() && vars[i].ts == 0) {
                D(dbg::prop,"Var x" << i << " has a value but is not assigned/xor-implied");
            }
            assert(conflict.empty() == false || vars[i].ts != 0);*/
        }

        for (size_t i2 = 0; i2 < sg.size(); i2++) {
            if (sg[i2].first == 0)  {
                hasTop2 = true;
                parity2 = sg[i2].second == false;
            }
        }
        
        bool fail = (hasTop1 != hasTop2) || (hasTop1 && hasTop2 && parity1 != parity2);
        if (fail && conflict.empty()) {
            D(dbg::state,toString());
            bcg.toGraphviz("bcg.dot", 0, 0, timestamp,true);
            D(dbg::prop,"fud differs from bcg with var id=" << i);
            D(dbg::prop,"hasTop1 " << hasTop1 << " hasTop2 " << hasTop2 << " parity1 " << parity1
                    << " parity2 " << parity2);

            assert(false);
        }


        if (vars[i].alias) {
            Fud::Result r1, r2;
            fud.find(vars[i].r1, r1);
            fud.find(vars[i].r2, r2);
            if (r1.var != r2.var) {
                D(dbg::prop, "alias x" << i << " broken. x" 
                        << vars[i].r1 << " and x" << vars[i].r2 << " in different equivalence classes!");
                D(dbg::prop, toString());
            }
            assert(r1.var == r2.var);

        }
    }

    for (size_t i = 0; i < xorAssumptions.size(); i++) {
        int v = xorAssumptions[i];
        assert(vars[v].ts != 0);
        assert(vars[v].r1 == 0);
        assert(vars[v].r2 == 0);
    }

    for (size_t i = 0; i < implied_lits.size(); i++) {
        Lit l= implied_lits[i];
        int v = l.get_var();
        if (vars[v].dl == 0)
            continue;
        assert(vars[v].ts != 0);
        assert(vars[v].r1 != 0);
    }
    for (int i = 0; i < clauses.size(); i++) {
        Clause& c = clauses[i];
        int sum = c.p;
        bool undef = false;
        for (int i2 = 0; i2 < 3; i2++) {
            Fud::Result r;
            fud.find(c.v[i2], r);
            if (r.var == top.var) {
                if (r.parity == top.parity)
                    sum++;
            } else
                undef = true;
        }
/*        if (sum % 2 == 0 && undef == false) {
            if (conflict.empty()) {
                D(dbg::prop,"clause id=" << i << " unsatisfied and no conflict.");
                bcg.explainPath(0,0,timestamp,conflict,participated);
                D(dbg::prop,toString());
                assert(false);
            }
        }*/
    }
    for (int i = 0; i < backjumps.size(); i++) {
        Backjump& bj= backjumps[i];
        if (bj.edges > bcg.edgeCount())
            D(dbg::prop, "Backjump " << i << " edges=" << bj.edges << " > " << bcg.edgeCount());
        assert(bj.edges <= bcg.edgeCount());
    }

}
void XorModule::checkTimestamps() {
    for (size_t i = 0; i < vars.size(); i++) {
        Var& v = vars[i];
        assert(v.ts <= timestamp);
        assert(v.ts >= 0);
    }
    for (size_t i = 0; i < assigns.size(); i++) {
        Assign a = assigns[i];
        assert(a.ts <= timestamp);
        assert(a.ts >= 0);
    }
    for (size_t i = 0; i < clauses.size(); i++) {
        Clause& c = clauses[i];
        assert(c.ts <= clauseTimestamp);
        assert(c.ts >= 0);
    }

    bcg.checkTimestamps(timestamp);
    fud.checkTimestamps();
}
#endif
#ifdef DEBUG

string XorModule::toString() {
    if (!dbg::state)
        return "";
        string res;
        res += "FUD:\n" + fud.toString() + "\n\nBCG:\n" + bcg.toString() + "\n\n";
        Fud::Result top;
        fud.find(0, top);
        
        for (int i = 0; i < vars.size(); i++) {
            char buf[512];
            Var& v = vars[i];
            Fud::Result r;
            fud.find(i, r);
            const char* value = "(unknown)";
            if (r.var == top.var) 
                value = (r.parity == top.parity) ? "1" : "0";

            snprintf(buf, 512, "Var id=%d value=%s r1=%d r2=%d ts=%d alias=%d\n",
                    i, value, v.r1, v.r2, v.ts, v.alias);


            res += string(buf);
            
        }

        for (int i = 0; i < backjumps.size(); i++) {
            char buf[512];
            snprintf(buf, 512, "Backjump id=%d\n", i);
            res += string(buf);
        }

        for (int i = 0; i < clauses.size(); i++) {
            char buf[512];
            Clause& c = clauses[i];
            snprintf(buf, 512, "Clause %d: x%d x%d x%d %d %s\n",
                    i, c.v[0], c.v[1], c.v[2], c.p, clauseActive[i] ? "" : "(deactivated)");
            res += string(buf);
        }
        for (int i = 0; i < assigns.size(); i++) {
            char buf[512];
            Assign a = assigns[i];
            snprintf(buf, 512, "Assign %d: lit=%d r1=%d r2=%d ts=%d dl=%d\n",
                    i,
                    (a.lit.get_sign() ? -1 : 1) * a.lit.get_var(),
                    a.r1, a.r2, a.ts, a.dl);
            res += string(buf);
        }
        for (int i = 0; i < eqvQueue.size(); i++) {
            char buf[512];
            snprintf(buf, 512, "EqvQueue %d: x%d\n",
                    i, eqvQueue[i]);
            res += string(buf);
        }


        return res;
    }


#endif
    void XorModule::printLiterals(std::vector<Lit>& lits) {
        set<int> s;
        for (size_t i = 0; i < lits.size(); i++) {
            Lit l = lits[i];
            s.insert((l.get_sign() ? -1 : 1) * l.get_var());
        }
        D(dbg::prop, "(" << s.size() << " terms) : ");
        for (set<int>::iterator i = s.begin(); i != s.end(); i++)
            D(dbg::prop, (((*i) < 0) ? " -x" : " x") << abs(*i));
        D(dbg::prop, "");
    }



#ifdef VERIFY


void XorModule::verify(vector<Lit>& lits) {
    D(dbg::prop, "verifying " << bx::toString(lits));
    unsigned int bt = simplex.set_backtrack_point();
    bool unsat = false;
    set<int> already;
    /*
    for (int i = 0; i < xorAssumptions.size(); i++) {
        int vv = xorAssumptions[i];

        Var& v = vars[vv];
        Fud::Result top;
        fud.find(0, top);
        Fud::Result r;
        fud.find(vv,r);
        bool value = r.parity == top.parity;
        if (v.dl == 0) {
            D(dbg::prop, "dl0 literal " << vv << " := " << value);
            already.insert(vv);
            if (simplex.assume(vv, value) == false) {
                unsat = true;
                break;
            }

        }
    }*/


    for (int i = 0; i < lits.size(); i++) {
        Lit& l = lits[i];
        bool value = l.get_sign() == false;
        Var& v = vars[l.get_var()];
        assert (!v.internal || i == 0);
        if (l.get_var() == 0 && value == false)
            return;
        assert(v.ts != 0);

        if (already.find(l.get_var()) != already.end())
            continue;
        if (simplex.assume(l.get_var(), !value) == false) {
            unsat = true;
            break;
        }
    }
    if (!unsat) {
        cerr << "Clause verification failed: ";
        for (int i = 0; i < lits.size(); i++)  {
            Lit& l = lits[i];
            cerr << (l.get_sign() ? " -x" : " x") << l.get_var();
        }
        cerr << endl;
        cerr << "Unsat=" << unsat << endl;
        for (int i = 0; i < xorAssumptions.size(); i++) {
            int v = xorAssumptions[i];
            Fud::Result top;
            fud.find(0, top);
            Fud::Result r;
            fud.find(v,r);
            bool value = r.parity == top.parity;
            cerr << "TRAIL: a " << (value ? "" : "!") << v << endl;
        }
        fud.toGraphviz("fud.dot");

        exit(1);

    }  else {
        //#ifdef DEBUG
        cout << "Clause ok: ";
        for (int i = 0; i < lits.size(); i++)  {
            Lit& l = lits[i];
            cout << (l.get_sign() ? " -x" : " x") << l.get_var() << " (" << vars[l.get_var()].ts << ")";
        }
        cout <<  endl;
        //#endif
    }


    simplex.backtrack(bt);


}

#endif

}
