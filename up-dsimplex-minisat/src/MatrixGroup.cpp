#include "MatrixGroup.hpp"
#include <iostream>
#include "Cluster.hpp"
#include <set>
//#define DEBUG
using namespace std;

bool MatrixGroup::propagateNewImplied() {
    while (!matricesToCheck.empty()) {
        int i = matricesToCheck.back();
        matrixQueued[i] = false;
        matricesToCheck.pop_back();

        IdMapper& mtx = *matrices[i];
        const vector<int>& implied = *mtx.get_implied_lits();

        if (impliedCount[i] != implied.size()) {
            for (size_t i2 = impliedCount[i]; i2 < implied.size(); i2++) {
                int l = implied[i2];
                if (implied_by[abs(l)] == -1) {
                    //                                            std::cout << "implied " << l << " by " << i << endl;
                    implied_lits.push_back(l);
                    implied_by[abs(l)] = i;                  
                    value[abs(l)] = l > 0;
                    // propagate the value of the variable to other matrices
                    const vector<int>& inMtx = varInMtx[abs(l)];
                    for (size_t i3 = 0; i3 < inMtx.size(); i3++) {
                        int m = inMtx[i3];
                        if ( m == i)
                            continue;
                        if (matrices[m]->assume(abs(l), l > 0) == false) {
                            unsatWithAssumptions = true;
                            cerr << "matrix " << m << " is unsat!" << endl;
                            cerr << "conflict size " << matrices[m]->get_conflict()->size() << endl;
                        }
                        if (!matrixQueued[m]) {
                            matrixQueued[m] = true;
                            matricesToCheck.push_back(m);
                        }
                    }
                } else {
                    if (int(l > 0) != value[abs(l)]) {
                        //                              cout << "value of " << l << " different in matrix " << i << endl;
                        exp.clear();
                        explain(-l, exp);
                        exp[0] = exp.back();
                        exp.pop_back();
                        //                            cout << "explain matrix " << i << endl;
                        mtx.explain(l, conflict);
                        conflict[0] = conflict.back();
                        conflict.pop_back();
                        copy(exp.begin(), exp.end(), back_inserter(conflict));
                        unsatWithAssumptions = true;
                    }
                }
            }
            impliedCount[i] = implied.size();
        }
    }
    return unsatWithAssumptions == false;
}
bool MatrixGroup::syncImplied() {
    bool saturated = false;

    bool confl = false;
    while (!saturated && conflict.empty()) {
        saturated = true;
        for (size_t i = 0; i < matrices.size(); i++) {
            IdMapper& mtx = *matrices[i];
            const vector<int>& implied = *mtx.get_implied_lits();

            if (impliedCount[i] != implied.size()) {
                for (size_t i2 = impliedCount[i]; i2 < implied.size(); i2++) {
                    int l = implied[i2];
                    if (implied_by[abs(l)] == -1) {
                        saturated = false;
//                                            std::cout << "implied " << l << " by " << i << endl;
                        implied_lits.push_back(l);
                        implied_by[abs(l)] = i;                  
                        value[abs(l)] = l > 0;
                        // propagate the value of the variable to other matrices
                        const vector<int>& inMtx = varInMtx[abs(l)];
                        for (size_t i3 = 0; i3 < inMtx.size(); i3++) {
                            int m = inMtx[i3];
                            if (matrices[m]->assume(abs(l), l > 0) == false)
                                confl = true;


                        }
                    } else {
                        if (int(l > 0) != value[abs(l)]) {
//                              cout << "value of " << l << " different in matrix " << i << endl;
                            exp.clear();
                            explain(-l, exp);
                            exp[0] = exp.back();
                            exp.pop_back();
//                            cout << "explain matrix " << i << endl;
                            mtx.explain(l, conflict);
                            conflict[0] = conflict.back();
                            conflict.pop_back();
                            copy(exp.begin(), exp.end(), back_inserter(conflict));
                            confl = true;


                        }

                    }

                }
                impliedCount[i] = implied.size();
            }
        }
    }
    if (confl)
        unsatWithAssumptions = true;
    return confl == false;
}
void MatrixGroup::simplify(int mtxCount) {
#ifdef VERIFY
    vds->simplify();
#endif
    if (ds) {       
        ds->simplify();
        if (!ds->is_sat())
            unsat = true;
        else
            split(mtxCount);
        delete ds;
        ds = NULL;
    } 

    varNums.resize(matrices.size());
    for (size_t i = 0; i < varInMtx.size(); i++) {
        for (size_t i2 = 0; i2 < varInMtx[i].size(); i2++) {
            int p = varInMtx[i][i2];
            varNums[p]++;
        }
    }

    impliedCount.resize(matrices.size());
    for (size_t i = 0; i < matrices.size(); i++) {
        matrices[i]->simplify();

        cout << "Matrix[" << i <<"]: " << varNums[i] << "x" << 
            rowNums[i] <<  " => "
            << matrices[i]->getVarNum()-1 << "x" << matrices[i]->getRowNum() << endl;
        if (!matrices[i]->is_sat())
            unsat = true;
 
        const vector<int>& initial = *matrices[i]->get_implied_lits();
        copy(initial.begin(), initial.end(), back_inserter(implied_lits));
    }
    syncImplied();
}


void MatrixGroup::split(int mtxCount) {
    const vector<int>& initial = *ds->get_implied_lits();
    copy(initial.begin(), initial.end(), back_inserter(implied_lits));

    Cluster cluster(ds->getRowNum());
    vector<vector<int> > var2rows;
    var2rows.resize(ds->getVarNum());
    vector<int> row;

    for (int y = 0; y < ds->getRowNum(); y++) {

        ds->getRow(y, row);
        for (size_t i = 0; i  < row.size(); i++) {
            if (row[i]) {

//                cout << row[i] << " add row " << y  << endl;
                var2rows[row[i]].push_back(y);
            }
        }
    }
    for (size_t i = 0; i < var2rows.size(); i++) {
        for (size_t j = 0; j < var2rows[i].size(); j++) {
            for (size_t k = j+1; k < var2rows[i].size(); k++) {

//                cout << "var " << i << endl;
                cluster.incDeg(var2rows[i][j], var2rows[i][k]);
            }
        }
    }

    cout << "Original matrix " << ds->getVarNum() << "x" << ds->getRowNum() << endl;
    vector< vector<int> > clusters;
    cluster.cluster(clusters, mtxCount > 1);
    implied_by.resize(ds->getVarNum());
    for (size_t i = 0; i < implied_by.size(); i++) {
        implied_by[i] = -1;
    }

    value.resize(ds->getVarNum());
    varInMtx.resize(ds->getVarNum());
    rowNums.resize(clusters.size());
    varNums.resize(clusters.size());
    matrixQueued.resize(clusters.size());
    for (int i = 0; i < clusters.size(); i++) {
        matrices.push_back(new IdMapper());
        for (int j = 0; j < clusters[i].size(); j++) {
            int mtx = i;
            ds->getRow(clusters[i][j], row);
            bool rhs = false;
            vector<int> lhs;
            for (size_t i2 = 0; i2 < row.size(); i2++) {
                if (row[i2] == 0)
                    rhs = !rhs;
                else {
                    int v = row[i2];
                    bool found = false;
                    for (size_t i3 = 0; i3 < varInMtx[v].size(); i3++) {
                        if (varInMtx[v][i3] == mtx) {
                            found = true;
                            break;
                        }
                             
                    }
                    if (!found)
                        varInMtx[v].push_back(mtx);

                    lhs.push_back(v);
                }
            }
            matrices[mtx]->add_equation(lhs, rhs);
            rowNums[mtx]++;
        }
    }
   
    return;
    
    for (int i = 0; i < mtxCount; i++)
        matrices.push_back(new IdMapper());

    for (size_t i = 0; i < implied_by.size(); i++) {
        implied_by[i] = -1;
    }

    int rowsPerMtx = ds->getRowNum() / mtxCount;
    if (rowsPerMtx == 0)
        rowsPerMtx = 1;


    for (int y = 0; y < ds->getRowNum(); y++) {
        int mtx = y / rowsPerMtx;        
        if (mtx >= matrices.size())
            mtx = matrices.size() - 1;

        ds->getRow(y, row);
        bool rhs = false;
        vector<int> lhs;
        for (size_t i = 0; i < row.size(); i++) {
            if (row[i] == 0)
                rhs = !rhs;
            else {
//                varInMtx[row[i]] |= 1<<mtx;

                lhs.push_back(row[i]);
            }
        }
        matrices[mtx]->add_equation(lhs, rhs);
        rowNums[mtx]++;
    }

/*    for (size_t i = 0; i < varInMtx.size(); i++) {
        uint32_t tmp = varInMtx[i];
        while(tmp) {
            int p = __builtin_ctz(tmp);
            uint32_t m = 1 << p;
            tmp &= ~m;
            varNums[p]++;
        }
    }*/

}

#ifdef VERIFY
void MatrixGroup::verifyImplied() {
    if (matrices.size() == 1)
        return;
    set<int> implied;
    set<int> impliedUnion;
    set<int> vdsImplied;
    const vector<int>* vdsImpl = vds->get_implied_lits();
     for (size_t i = 0; i < implied_lits.size(); i++) {
        implied.insert(implied_lits[i]);
    }

    vds->dumpState();
    for (size_t i = 0; i < matrices.size(); i++) {
        IdMapper& mtx = *matrices[i];
        const vector<int>& impl = *mtx.get_implied_lits();
        for (size_t i2 = 0; i2 < impl.size(); i2++) {
            assert(unsat || implied.find(impl[i2]) != implied.end());
            impliedUnion.insert(impl[i2]);
#ifdef DEBUG
            cout << impl[i2] << " implied by mtx " << i << endl;
#endif

        }
    }
#ifdef DEBUG
    for (size_t v = 0; v < varInMtx.size(); v++) {
        for (size_t m = 0; m < varInMtx[v].size(); m++) {
            cout << "Var " << v << " in mtx " << m  << endl;
        }
    }
    cout << "is_sat(): " << is_sat() << endl;
    cout << "implied.size() : " << implied.size() << endl;
    cout << "impliedUnion.size() : " << impliedUnion.size() << endl;
#endif

    assert(!is_sat() || implied.size() == impliedUnion.size());
#ifdef DEBUG 
    cout << "Split matrices" << endl;
    for (size_t i = 0; i < matrices.size(); i++) {
        matrices[i]->dumpState();
    }
#endif
    for (size_t i = 0; i < vdsImpl->size(); i++) {

       int  l = (*vdsImpl)[i];
       if (implied.find(l) == implied.end())
           cout << "reference simplex implied " << l << endl;
        vdsImplied.insert(l);
    }
    assert(is_sat() == vds->is_sat());    
     assert(!is_sat() || (implied == vdsImplied));
    assert((cout << "VERIFIED!" << endl) == cout);
}
#endif

