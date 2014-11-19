#ifndef _idmapper_hpp_
#define _idmapper_hpp_
#include "DSimplex.hpp"
class IdMapper {
    DSimplex ds;
    std::vector<int> implied_lits;
    std::vector<int> conflict;
    std::vector<int> ext2int, int2ext;

    void new_var(int orig);
    int mapInt2Ext(int lit) const;
    int mapExt2Int(int lit) const;
    void syncImplied();
public:

    void add_equation(const std::vector<int>& lhs,
                     const bool rhs);

    void explain(int lit, std::vector<int>& explanation) ;
    bool assume(int var, bool value);

    void simplify() {
        ds.simplify();
        syncImplied();

    }

    int set_backtrack_point() {
        return ds.set_backtrack_point();
    }
    void backtrack(int bt) {
        ds.backtrack(bt);
        implied_lits.resize(ds.get_implied_lits()->size());
        conflict.clear();
    }
    int getVarNum() const {
        return ds.getVarNum();
    }
    int getRowNum() const {
        return ds.getRowNum();
    }
    bool is_sat() const {
        return ds.is_sat();
    }
    const std::vector<int>* get_conflict() const {
        return &conflict;
    }

    const std::vector<int>* get_implied_lits() const {
        return &implied_lits;
    }
    void dumpState();



};
    
#endif
