#include "DSimplex.hpp"
#include <algorithm>
#include <iostream>
#include <assert.h>
#include <sstream>
#include <set>
//#define DEBUG
#ifdef DEBUG
#define D(x) { std::cout << x << std::endl; }
#else
#define D(x)
#endif
template <class T> std::string toString(T t) {
    std::ostringstream ost;
    ost << t;
    return ost.str();
}

template <> std::string toString<std::vector<int> > (std::vector<int> lits) {
    std::ostringstream ost;
    for (size_t i = 0; i < lits.size(); i++) {
        if (i)
            ost << " ";
        ost << toString(lits[i]);
    }
    return ost.str();
}




using namespace std;
DSimplex::DSimplex()
    : mtx(NULL), unsat(false), prevImpliedSize(0) {
        vars.push_back(Var());

}
DSimplex::~DSimplex() {
    delete mtx;
}


int DSimplex::new_var() {

#ifdef CHECK
    while (1) {
        if (simplex.new_var() == vars.size())
            break;
    }
#endif

    vars.push_back(Var());

    return vars.size() - 1;
}

void DSimplex::add_equation(const std::vector<int>& lhs,
                            const bool rhs) {
    for (size_t i = 0; i < lhs.size(); i++) {
        while(vars.size() <= lhs[i])
            new_var();
    }
#ifdef CHECK
    vector<unsigned int> lhsu;
    copy(lhs.begin(), lhs.end(), back_inserter(lhsu));
    simplex.add_equation(lhsu, rhs);
#endif
  /* Sort and simplify */
    vector<int> l;
    copy(lhs.begin(), lhs.end(), back_inserter(l));
  std::sort(l.begin(), l.end());
  unsigned int j = 0;
  for(unsigned int i = 0; i < l.size(); ) {
    if(i+1 < l.size() and l[i] == l[i+1])
      i += 2;
    else
      l[j++] = l[i++];
  }
  l.resize(j);
  /* Analyze the result */
  if(l.size() == 0) {
    if(rhs == false) {
      /* 0 = 0 */
      return;
    }
    /* 0 = 1 */
    unsat = true;
    return;
  }
    D("row " << equations.size() << " : " << toString(l) << " = " << rhs);

    equations.push_back(Equation(l, rhs));
}
std::string DSimplex::getState() const {
    string s;
#ifdef DEBUG
    for (int i = 0; i <  mtx->getHeight(); i++) {
        mtx->getRow(i, row);
        int nonBasic = -1;
        vector<int> basics;

        for (size_t i2 = 0; i2 < row.size(); i2++) {
            if (!vars[row[i2]].basic) {
                nonBasic = row[i2];
            } else
                basics.push_back(row[i2]);
        }
        sort(basics.begin(), basics.end());
        s += "[" + toString(i) + "]: " + toString(nonBasic) + " := " + toString(basics) + "\n";
    }
    vector<int> assigned;
    for (size_t i = 1; i < vars.size(); i++) {
        int v = mtx->getValue(i);
        if (v)
            assigned.push_back(v * i);
    }
    s += ("Assigned: " + toString(assigned) + "\n");
//    simplex.print(stdout);
#endif
    return s;
}

void DSimplex::dumpState() const {
#ifdef DEBUG
    for (int i = 0; i <  mtx->getHeight(); i++) {
        mtx->getRow(i, row);
        int nonBasic = -1;
        vector<int> basics;

        for (size_t i2 = 0; i2 < row.size(); i2++) {
            if (!vars[row[i2]].basic) {
                nonBasic = row[i2];
            } else
                basics.push_back(row[i2]);
        }
        sort(basics.begin(), basics.end());
        D("[" << i << "]: " << nonBasic << " := " << toString(basics));
    }
    vector<int> assigned;
    for (size_t i = 1; i < vars.size(); i++) {
        int v = mtx->getValue(i);
        if (v)
            assigned.push_back(v * i);
    }
    D("Assigned: " << toString(assigned));
//    simplex.print(stdout);
#endif
}

void DSimplex::check() {
#ifdef CHECK

    for (size_t i = 0; i < implied_lits.size(); i++) {
        int v = abs(implied_lits[i]);
        if (vars[v].basic)
            D("basic implied literal " << implied_lits[i]);
        assert(!vars[v].basic);
    }
    for (int i = 0; i <  mtx->getHeight(); i++) {
        mtx->getRow(i, row);
        int nonBasic = 0;
        int values = 0;
        bool nonBasicValue = false;
        for (size_t i2 = 0; i2 < row.size(); i2++) {
            int v = row[i2];
            bool value = mtx->get(v,i);
            if (value)
                values++;
            if (!vars[v].basic) {

                if (value)
                    nonBasicValue = true;

                nonBasic++;
            }
        }
        if (nonBasicValue)
            assert(values == (int) row.size());
        if (nonBasic != 1)
            D("Row " << i << " broken. " << nonBasic << " non-basic variables");
        assert(nonBasic == 1);
    }

    if (is_sat() && false) {
        const vector<Simplex::Lit>& simplied_ = *simplex.get_implied_lits();
        set<int> simplied;
        for (size_t i = 0; i < simplied_.size(); i++) {
            int v = simplied_[i].get_var() 
                * (simplied_[i].get_sign() ? -1 : 1);
            simplied.insert(v);
        }
        set<int> implied;
        for (size_t i = 0; i < implied_lits.size(); i++) {
            implied.insert(implied_lits[i]);
        }
        assert(simplied == implied);

    }
#endif
}
void DSimplex::explain(int lit, std::vector<int>& exp){
    int v = abs(lit);
    assert(v >= 0 && v < (int)vars.size());
    assert(!vars[v].basic);
    assert(mtx != NULL);
    assert(mtx->getValue(v) != 0);
    exp.clear();
    D("implied lit " << lit << " row " << vars[v].eq);

    mtx->getAssigned(vars[v].eq, exp);

    for (size_t i = 0; i < exp.size(); i++) {
        if (abs(exp[i]) == v) {
            exp[i] = exp[0];
            exp[0] = lit;

            D("Simplex::explain : " << toString(exp));
            verify(exp);
            return;
        }
    }
    D("invalid exp for " << lit << " row " << vars[v].eq);
    dumpState();
    assert(false); /* not in exp*/ 
}

void DSimplex::simplify() {

    assert(mtx == NULL);

    mtx = new Matrix(vars.size(), equations.size());
    D("vars " << vars.size() << " equations " << equations.size());
    mtx->assign(0,1,implied_lits,implied_by);
    for (size_t i = 0; i < equations.size(); i++) {
        Equation& eq = equations[i];
        for (size_t i2 = 0; i2 < eq.lhs.size(); i2++) {
            vector<int>& lhs = eq.lhs;
            mtx->set(lhs[i2], i, 1);
        }
        mtx->set(0,i,eq.rhs);
    }
    int numEq = 0;
    D("selecting non-basic vars");
    for (size_t i = 0; i < equations.size(); i++) {
        if (mtx->numOnesRow(i)) {
            mtx->getRow(i, row);
            int instances = equations.size()+1;
            int minInst = -1;
            D("row " << i << " : " << toString(row));
            int nonBasic = -1;
            int numVars = 0;
            for (size_t i2 = 0; i2 < row.size(); i2++) {

                if (row[i2] == 0)
                    continue;
                numVars++;
                if (!vars[row[i2]].basic) {
                    minInst = -1;
                    nonBasic = row[i2];
                    D(row[i2] << " is non-basic");
                    break;
                } else {
                    int ones = mtx->numOnesCol(row[i2]);

                    D("counting number of instances for " << row[i2] <<
                            " : " << ones);
                    if (ones < instances) {
                        instances = ones;
                        minInst = row[i2];
                    }
                }
            }
            if (nonBasic == -1) {

                D("no non-basic for row " << i );

                if (minInst == -1) {
                    D("but no non-assigned basic vars");
                    D("clearing satisfied row");
                    for (size_t i2 = 0; i2 < row.size(); i2++) {
                        mtx->set(row[i2], i, 0);
                    }
//                    dumpState();
                }  else {
                    D("pivot var "<< minInst << " by " << i << " instances " <<
                            instances);
                    vars[minInst].basic = false;
                    vars[minInst].eq = i;
                    size_t prev = implied_lits.size();
                    int r = mtx->pivot(minInst, i, implied_lits, implied_by);
                    if (r != -1) {
                        mtx->getRow(r,row);
                        D("row " << r << " unsat! " << toString(row));
                        for (size_t i2 = 0; i2 < row.size(); i2++)
                            D("getValue(" << row[i2] << "): " << mtx->getValue(row[i2]));
                        unsat = true;
//                        dumpState();

                        return;
                    }

//                    dumpState();
                }
            }
            numEq++;
        }
    }
    dumpState();
    implied_lits.clear();
    implied_by.clear();
    for (size_t i = 0; i < mtx->getHeight(); i++) {
        mtx->getRow(i, row);
        int varCount = 0;
        int implied = 0;
        bool top = false;
        for (size_t i2 = 0; i2 < row.size(); i2++) {
            if (row[i2]) {
                varCount++;
                implied = row[i2];
            } else
                top = true;
        }
        if (varCount == 1) {
            implied_lits.push_back(top ? implied : -implied);
            implied_by.push_back(i);
        }
    }
    for (size_t i = 0; i < implied_lits.size(); i++) {
        int v = implied_lits[i];
        D("implied literal[" << i << "] : " << v);
        if (mtx->assign(abs(v), v > 0, implied_lits, implied_by) != -1) {
            D("unsat!");
            unsat = true;
            return;
        }
    }
    numEq -= implied_lits.size();
    assert(numEq >= 0);
//    cout << "simplex: number of equations " << equations.size() << " -> " << numEq << endl;
  //  cout << "simplex: implied literals " << implied_lits.size() << endl;
    Matrix* mtx2 = new Matrix(vars.size(), numEq);
    mtx2->assign(0,1,implied_lits,implied_by);

    int newRow = 0;
    for (size_t y = 0; y < equations.size(); y++) {
        
        mtx->getRow(y,row);
        int numVars = 0;
        for (size_t i = 0; i < row.size(); i++) {
            if (row[i])
                numVars++;
        }
        if (numVars <= 1) {
            continue;
        }
        D("row " << newRow << " : " << toString(row));
        for (size_t i = 0; i < row.size(); i++) {

            if (row[i] && !vars[row[i]].basic)
                vars[row[i]].eq = newRow;

            mtx2->set(row[i],newRow,1);
        }
        newRow++;
    }
    equations.clear();
    assert(newRow == numEq);
    delete mtx;
    mtx = mtx2;
    vector<int> foo;
    vector<int> foo2;
    for (size_t i = 0; i < implied_lits.size(); i++) {

        mtx->assign(abs(implied_lits[i]), implied_lits[i] > 0,foo,foo2);
    }


}

int DSimplex::set_backtrack_point() {
    assert(mtx != NULL);

    backjumps.push_back(Backjump());
    Backjump& bj = backjumps.back();
    bj.implied = implied_lits.size();
    bj.prevImpliedSize = prevImpliedSize;
    bj.mtxBt = mtx->set_backtrack_point();
#ifdef CHECK
    bj.simplexBt = simplex.set_backtrack_point();
#endif
    return backjumps.size() - 1;
}
void DSimplex::backtrack(int bt) {
    assert(mtx != NULL);
    assert(bt >= 0 && bt < (int) backjumps.size());
    Backjump& bj = backjumps[bt];
    implied_lits.resize(bj.implied);
    implied_by.resize(bj.implied);
#ifdef CHECK
    simplex.backtrack(bj.simplexBt);
#endif

    prevImpliedSize = bj.prevImpliedSize;

    mtx->backtrack(bj.mtxBt);
    backjumps.resize(bt);
    conflict.clear();
}
int DSimplex::pickPivotVar(int eq, int var) {
    mtx->getRow(eq, row);
    int instances = mtx->getHeight()+1;
    int minInst = -1;
    for (size_t i = 0; i < row.size(); i++) {
        if (row[i] && row[i] != var && mtx->getValue(row[i]) == 0) {
            int ones = mtx->numOnesCol(row[i]);
            if (ones < instances) {
                minInst = row[i];
                instances = ones;
            }
        }
    }
    assert(minInst != -1);
    return minInst;
}
void DSimplex::assignImplied() {
    assert(implied_lits.size() == implied_by.size());
    for (size_t i = 0; i < implied_lits.size(); i++) {
        D("implied_lits[" << i << "] : " << implied_lits[i]);
        D("implied_by[" << i << "] : " << implied_by[i]);
    }

    for (size_t i = prevImpliedSize; i < implied_lits.size(); i++) {
        int v = implied_lits[i];
        int eq = implied_by[i];
        Var& var = vars[abs(v)];
        var.eq = eq;
        D(v << " implied by " << eq);
        assert(var.basic == false);
        int r = mtx->assign(abs(v), v > 0, implied_lits, implied_by);
        if (r != -1) {
            mtx->getAssigned(r, conflict);
            D("conflict " << toString(conflict)); 
            return;
        }
    }
    prevImpliedSize = implied_lits.size();
}
void DSimplex::_assign(int v, bool value) {
    Var& var = vars[v];
    int val = mtx->getValue(v);
    if (val) {
        if (value != (val > 0)) {
            D("already assigned variable!");
            return;
        } else {
            // ignore
            return;
        }
    } else {
        if (!var.basic) {
            D("var " << v << " not basic. pivot by " << var.eq);

            // make the variable basic

            int v2 = pickPivotVar(var.eq, v);

            int r = mtx->pivot(v2, var.eq, implied_lits, implied_by);
            var.basic = true;

            Var& var2 = vars[v2];
            var2.basic = false;
            var2.eq = var.eq;

            D("var " << v2 << " is now non-basic");
            dumpState();
            if (r != -1) {
                mtx->getAssigned(r, conflict);
                D("conflict " << toString(conflict)); 
                return;
            }

        }
        int row = mtx->assign(v, value, implied_lits, implied_by);
        if (row != -1) {
            mtx->getAssigned(row, conflict);
            D("conflict " << toString(conflict)); 
            return;
        }
    }

}
bool DSimplex::assume(int v, bool value) {
    D("assume(" << v << "," << value << ")");
    assert(mtx != NULL);
    assert(v >= 1 && v < (int) vars.size());
    dumpState();
    _assign(v, value);
    assignImplied();
    dumpState();
#ifdef CHECK
//    simplex.assume(v, value);
    if (simplex.is_sat() != is_sat()) {
        D("DSmplex is_sat " << is_sat() << " Simplex is_sat " << simplex.is_sat());
    }
    assert(simplex.is_sat() == is_sat());
#endif

    check();

    return conflict.empty();
}
void DSimplex::verify(vector<int>& lits) {
#ifdef CHECK
    D("Verify : " << toString(lits));
    unsigned int bt = simplex.set_backtrack_point();

    for (int i = 0; i < lits.size(); i++) {
        int l = lits[i];
        bool value = l > 0;
        Var& v = vars[abs(l)];

        if (simplex.assume(abs(l), !value) == false) {
            break;
        }
    }
    if (simplex.is_sat()) {

        cerr << "Clause verification failed: " << toString(lits);
        cerr << "Unsat=" << unsat << endl;
        simplex.print(stdout);
        exit(1);

    }  else {
        cout << "Clause ok: " << toString(lits) << endl;
    }


    simplex.backtrack(bt);
#endif

}

