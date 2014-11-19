#ifndef _matrixgroup_hpp_
#define _matrixgroup_hpp_
#include "IdMapper.hpp"
#include <vector>
#include <iostream>
class MatrixGroup {
    struct Backjump {
        std::vector<int> points;
        std::vector<int> impliedCounts;
        int implied;
#ifdef VERIFY
        int vds;
#endif
    };
    std::vector<IdMapper*> matrices;
    std::vector<int> implied_lits;
    std::vector<int> implied_by;
    std::vector<char> value;
    std::vector<int> impliedCount;
    std::vector< std::vector<int > > varInMtx;
    std::vector<int> conflict;
    std::vector<int> exp;
    std::vector<Backjump> backjumps;
    std::vector<bool> matrixQueued;
    std::vector<int> matricesToCheck;

    bool unsat;
    bool unsatWithAssumptions;
    DSimplex* ds;
#ifdef VERIFY
    DSimplex* vds;
#endif
    std::vector<int> rowNums;
    std::vector<int> varNums;


    bool propagateNewImplied();
    bool syncImplied();
    
    void split(int mtxCount);
public:
    MatrixGroup() : unsat(false), unsatWithAssumptions(false), ds(NULL) {
        ds = new DSimplex();
#ifdef VERIFY
        vds = new DSimplex();
#endif
    }
    void manualPartition() {
        //std::cout << "manual matrix partitioning" << std::endl;
        delete ds;
        ds = NULL;
    }
    ~MatrixGroup() {
        if (ds)
            delete ds;
#ifdef VERIFY
        delete vds;
#endif
        for (size_t i = 0; i < matrices.size(); i++)
            delete matrices[i];
    }

    void add_equation(const std::vector<int>& lhs,
                     const bool rhs) {
        if (!ds) {
            add_equation(0, lhs, rhs);
            return;
        }
#ifdef VERIFY
        vds->add_equation(lhs, rhs);
#endif
 
        ds->add_equation(lhs, rhs);
    }
    void add_equation(int mtx, 
                      const std::vector<int>& lhs,
                      const bool rhs) {
#ifdef VERIFY
        vds->add_equation(lhs, rhs);
#endif
        // std::cout << "add_equation(" << mtx << ",";

        while(matrices.size() <= mtx) {
            matrices.push_back(new IdMapper());
        }
        while (matrixQueued.size() <= mtx) {
            matrixQueued.push_back(false);
        }
        for (size_t i2 = 0; i2 < lhs.size(); i2++) {
            int v = lhs[i2];

            //std::cout << ((i2 == 0) ? "[" : ",") << v;
            bool found = false;
            if (varInMtx.size() <= v)
                varInMtx.resize(v + 1) ;
            if (value.size() <= v)
                value.resize(v + 1);
            if (implied_by.size() <= v)
                implied_by.resize(v + 1, -1);
            std::vector<int>& inMtx = varInMtx[v];
            for (size_t i3 = 0; i3 < inMtx.size(); i3++) {
                if (inMtx[i3] == mtx) {
                    found = true;
                    break;
                }
            }
            if (!found)
                inMtx.push_back(mtx);
        }
        //std::cout << "]," << rhs << std::endl;
        matrices[mtx]->add_equation(lhs, rhs);
        if (rowNums.size() <= mtx)
            rowNums.resize(mtx + 1);
        rowNums[mtx]++;
    }
        

    int getRowNum() {
        if (ds)
            return ds->getRowNum();
        return 0;
    }

    void explain(int lit, std::vector<int>& explanation) {
        assert(abs(lit) >= 0 && abs(lit) < implied_by.size());
        assert(implied_by[abs(lit)] != -1);

//        std::cout << "explain " << lit << " from matrix " << implied_by[abs(lit)] << std::endl;
        matrices[implied_by[abs(lit)]]->explain(lit, explanation);
    }
    bool assume(int var, bool value) {
        bool result = true;
        if (var >= varInMtx.size()) {
//            std::cout << "nothing known about " << var << std::endl;
            return true;
        }/*
        uint32_t tmp = varInMtx[var];
        while(tmp) {
            int p = __builtin_ctz(tmp);
            uint32_t m = 1 << p;
            tmp &= ~m;

            assert(p >= 0 && p < matrices.size());
*/
#ifdef VERIFY
        vds->assume(var, value);
#endif
            for (size_t p = 0;  p < varInMtx[var].size(); p++) {
                int mtx = varInMtx[var][p];

                if (matrices[mtx]->assume(var, value) == false) {
                    result = false;
                    unsatWithAssumptions = true;
                }

                matricesToCheck.push_back(mtx);            
                matrixQueued[mtx] = true;
            }
//        }
        result = propagateNewImplied();
#ifdef VERIFY
        verifyImplied();
#endif
 
        return result;
    }

    void simplify(int mtxCount=1);

    int set_backtrack_point() {
        backjumps.push_back(Backjump());
        Backjump& b = backjumps.back();
#ifdef VERIFY
        b.vds = vds->set_backtrack_point();
#endif
        for (size_t i = 0; i < matrices.size(); i++) {

            b.points.push_back(matrices[i]->set_backtrack_point());                
            b.impliedCounts.push_back(impliedCount[i]);
        }
        b.implied = implied_lits.size();
//        std::cout << "set_backtrack " << backjumps.size() - 1 << std::endl;
        return backjumps.size() - 1;

    }
    void backtrack(int bt) {
        Backjump& b = backjumps[bt];
#ifdef VERIFY
        vds->backtrack(b.vds);
#endif
//        std::cout << "backtrack " << bt << std::endl;

        for (size_t i = 0; i < matrices.size(); i++) {
            matrices[i]->backtrack(bt);
            impliedCount[i] = b.impliedCounts[i];

        }
        for (size_t i = b.implied; i < implied_lits.size(); i++) {
//            std::cout << "implied_by[" << abs(implied_lits[i]) << "] = -1" << std::endl;
            implied_by[abs(implied_lits[i])] = -1;
        }
        implied_lits.resize(b.implied);
#ifdef VERIFY
        verifyImplied();
#endif
        backjumps.resize(bt);
        conflict.clear();
        unsatWithAssumptions = false;
    }

    bool is_sat() const {
        if (!conflict.empty())
            return false;
        if (unsat)
            return false;
        if (unsatWithAssumptions)
            return false;

        return true;
    }
    const std::vector<int>* get_conflict() const {

        if (!conflict.empty())
            return &conflict;
        for (size_t i = 0; i < matrices.size(); i++)
            if (!matrices[i]->get_conflict()->empty())
                return matrices[i]->get_conflict();
        return &conflict;
    }

    const std::vector<int>* get_implied_lits() const {
        return &implied_lits;
    }

#ifdef VERIFY
    void verifyImplied();
#endif

};
 
#endif
