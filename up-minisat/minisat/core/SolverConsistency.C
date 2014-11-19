#include "Solver.h"
#include "Split.hpp"
#include "Common.hpp"
#include <cstdio>
#include <map>
#include <set>
using namespace std;
#ifdef DEBUG

void Solver::checkConsistency() {
    map<Clause*, string> clauseName;

    for (int i = 0; i < clauses.size(); i++) {
        Clause* c = clauses[i];
        char buf[8];
        snprintf(buf, 8, "c%-2d", i);
        clauseName[c] = buf;

    }

    reportf("LEARNTS-------------------------------------------------------\n");
    for (int i = 0; i < learnts.size(); i++) {
        Clause* c = learnts[i];
        char buf[8];
        snprintf(buf, 8, "l%-2d", i);
        clauseName[c] = buf;

    }
    for (int i = 0; i < seen.size(); i++)
        assert(seen[i] == 0);

    // CHECK: watch-literals <-> clauses relation consistent
    for (int i = 0; i < watches.size(); i++) {
        Lit lit(toLit(i));
        vec<Clause*>& ws = watches[i];
        for (int j = 0; j < ws.size(); j++) {
            Clause* c = ws[j];
            bool watchLiteralInClause = false;
            for (int k = 0; k < c->size(); k++) {
                Lit lit2((*c)[k]);
                if (var(lit2) == var(lit) && sign(lit2) != sign(lit)) {
                    watchLiteralInClause = true;
                    break;
                }
            }
            assert(watchLiteralInClause);
        }
    }

    // CHECK: variable vector sizes consistent
    assert(watches.size()      == nVars() * 2);
    assert(reason.size()       == nVars());
    assert(assigns.size()      == nVars());
    assert(level.size()        == nVars());
    assert(activity.size()     == nVars());
    assert(seen.size()         == nVars());
    assert(polarity.size()     == nVars());
    assert(decision_var.size() == nVars());

    // CHECK: learnt clauses are almost unique
    map<string, int> learntNames;
    for (int i = 0; i < learnts.size(); i++) {
        Clause* c = learnts[i];
        xorsat::Split content;
        for (int j = 0; j < c->size(); j++)  {
            Lit l = (*c)[j];
            content.push_back(string(sign(l) ? "~x" : " x") 
                    + xorsat::toString(var(l)));
        }
        learntNames[content] += 1;
     //   assert(learntNames[content] <= 3);
    }

    // CHECK: a correct number of decision levels
    int levels = 0;
    int dl0 = 0;
    if (trail_lim.size() > 0)
        dl0 = trail_lim[0];
    for (int i = 0; i < trail.size(); i++) {
        Var v = var(trail[i]);
        if (reason[v] == NULL && xorJustifiable[v] == 0) {
            assert(level[v] >= levels);
            levels = level[v];
        }
    }

    assert(levels == trail_lim.size());

    int lim = -1;
    for (int i = 0; i < trail_lim.size(); i++) {
        assert(trail_lim[i] > lim);
        lim = trail_lim[i];
    }


    // CHECK: literals in trail are justified by preceding literals
    map<int, int> varPos;
    int lower = 0;
    int upper = trail.size();
    for (int i = 0; i < trail.size(); i++) {
        Lit p = trail[i];
        Var v = var(p);
        varPos[v] = i;
        upper = trail.size();
        if (level[v] < decisionLevel())
            upper = trail_lim[level[v]];
        if (level[v] > 0)
            lower = trail_lim[level[v]-1];

        if (i < lower || i >= upper) {
            printState();
            reportf("Literal ");
            printLit(p);
            reportf("is in wrong decision level lower=%d upper=%d\n", lower, upper);

            assert(false);
        } 

        if (reason[v]) {
            Clause& c = *reason[v];
            for (int i2 = 1; i2 < c.size(); i2++) {
                if (value(c[i2]) != l_False) {
                    printState();
                    reportf("CLAUSE %s broken justification for \n",
                            clauseName[reason[v]].c_str());
                    printLit(c[i2]);

                }
                assert(value(c[i2]) == l_False);
                Var v2 = var(c[i2]);
                if (varPos.find(v2) == varPos.end()) {
                    printState();
                    reportf("CLAUSE %s : ", clauseName[reason[v]].c_str());
                    printLit(c[i2]);
                    reportf(" does not appear in the trail before ");
                    printLit(p);
                    reportf("\n");
                }
                assert(varPos.find(v2) != varPos.end());
            }
        }
        
    }


}
void Solver::printState() {



    reportf("MiniSAT solver state:\n");
    reportf("CLAUSES-------------------------------------------------------\n");


    map<Clause*, string> clauseName;

    for (int i = 0; i < clauses.size(); i++) {
        Clause* c = clauses[i];
        char buf[8];
        snprintf(buf, 8, "c%-2d", i);
        clauseName[c] = buf;
        reportf("    c%-2d : ", i);
        printClause(*c);
        reportf("\n");

    }

    reportf("LEARNTS-------------------------------------------------------\n");
    for (int i = 0; i < learnts.size(); i++) {
        Clause* c = learnts[i];
        char buf[8];
        snprintf(buf, 8, "l%-2d", i);
        clauseName[c] = buf;

        reportf("    l%-2d : ", i);
        printClause(*c);
        reportf("\n");
    }
    reportf("TRAIL---------------------------------------------------------\n");
    for (int i = 0; i < trail.size(); i++) {
        Lit l = trail[i];
        string rs;
        Var v = var(l);
        Clause* c = reason[v];
        if (c) 
            rs = " (reason=" + clauseName[c] + ")";
        if (xorJustifiable[v])
            rs = " (xor)";
        reportf("    %4s%4s %-2d : %sx%d (lvl=%d)%s\n", 
                (upTrail.size()==i) ? "X>" : "  ",
                qhead==i ? "->" : "  ",
                i, sign(l) ? "~" : " ", v,  level[v], rs.c_str());
    }
    reportf("    %4s%4s\n", 
                (upTrail.size()==trail.size()) ? "X>" : "  ",
                qhead==trail.size() ? "->" : "  ");
    reportf("XORTRAIL------------------------------------------------------\n");
    for (int i = 0; i < upTrail.size(); i++) {
        Lit l = upTrail[i];
        string rs;
        Var v = var(l);
        Clause* c = reason[v];
        if (c) 
            rs = " (reason=" + clauseName[c] + ")";
        reportf("    %4s%4s %-2d : %sx%d (lvl=%d)%s\n", 
                "  ",
                qhead==i ? "->" : "  ",
                i, sign(l) ? "~" : " ", v,  level[v], rs.c_str());
    }
    reportf("    %4s%4s\n", 
                "X>",
                qhead==upTrail.size() ? "->" : "  ");


    reportf("END-OF-TRAIL--------------------------------------------------\n\n");
    reportf("DL\n");
    for (int i = 0; i < trail_lim.size(); i++)
        reportf("trail_lim[%d] : %d\n", i, trail_lim[i]);

    /*
    reportf("REASONS-------------------------------------------------------\n");
    for (int i = 0; i < nVars(); i++) {
        Clause* c = reason[i];

        // CHECK: reason clauses exist
        reportf("x%-2d : ", i+1);
        if (c) {
            assert(clauseName.find(c) != clauseName.end());
        }

        reportf("%s\n", c ? clauseName[c].c_str() : "");

    }

    reportf("WATCHES-------------------------------------------------------\n");
    for (int i = 0; i < watches.size(); i++) {
        Lit l(toLit(i));
        vec<Clause*>& cs = watches[i];
        xorsat::Split content;
        for (int j = 0; j < cs.size(); j++) {
            Clause* c = cs[j];
            content.push_back(clauseName[c]);

        }
        reportf("%sx%-2d : %s\n", sign(l) ? "~" : " ", var(l)+1, 
                content.join(", ").c_str());


    }
    reportf("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n");
*/

}
#endif
