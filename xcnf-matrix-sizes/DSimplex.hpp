#ifndef __densesimplex_hpp_
#define __densesimplex_hpp_

#include <vector>
#include "Matrix.hpp"
#include <algorithm>
class DSimplex {
        DSimplex(const DSimplex&);
        DSimplex& operator=(const DSimplex&);
    public:    

    private:

        struct Backjump {
            size_t implied;
            size_t prevImpliedSize;
            int mtxBt;
            int simplexBt;
        };
        struct Equation {
            std::vector<int> lhs;
            bool rhs;
            Equation(const std::vector<int>& lhs_,
                    bool rhs_)
                : lhs(lhs_), rhs(rhs_) {}
        };
        struct Var {
            bool basic, eliminated;
            int eq;
            Var() : basic(true), eliminated(false), eq(-1){}
        };
        std::vector<int> conflict;
        std::vector<Backjump> backjumps;
        std::vector<int> implied_lits;
        std::vector<int> implied_by;
        std::vector<Var> vars;
        mutable std::vector<int> row;
        Matrix* mtx;
        std::vector<Equation> equations;
        bool unsat;
        size_t prevImpliedSize;

        int pickPivotVar(int row, int notThis);
        void assignImplied();
        void _assign(int v, bool value);
 
        void check();
        void verify(std::vector<int>& exp);
    public:

        std::string getState() const;

        void dumpState() const;
        DSimplex();
        ~DSimplex();

        int new_var();
        void add_equation(const std::vector<int>& lhs,
                          const bool rhs);

        void explain(int lit, std::vector<int>& explanation);
        Matrix* simplify();

        int set_backtrack_point();
        void backtrack(int bt);

        bool is_sat() const {
            return ! (unsat or !conflict.empty());
        }
        bool assume(int var, bool value);
        const std::vector<int>* get_conflict() const {
            return &conflict;
        }

        const std::vector<int>* get_implied_lits() const {
            return &implied_lits;
        }
        int getRowNum() const {
            if (!mtx)
                return equations.size();
            return mtx->getHeight();
        }
        int getVarNum() const {
            return vars.size();
        }
        void getRow(int r, std::vector<int>& row) {
            if (mtx)
                mtx->getRow(r, row); 
            else {
                row.clear();
                std::copy(equations[r].lhs.begin(), equations[r].lhs.end(),
                        std::back_inserter(row));
                if (equations[r].rhs)
                    row.push_back(0);
            }
        }

};

#endif
