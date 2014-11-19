#include "IdMapper.hpp"
#include <algorithm>
#include <iostream>
#include "Split.hpp"
#include "util.hpp"
//#define DEBUG
using namespace std;
void IdMapper::new_var(int orig) {
    //cout << "new_var(" << orig << ")" << endl;
    while ((int)ext2int.size() <= orig)
        ext2int.push_back(-1);
    
    int v = ds.new_var();
    ext2int[orig] = v;
    while ((int)int2ext.size() <= v)
        int2ext.push_back(-1);
    int2ext[v] = orig;
    //cout << "ext2int[" << orig << "] = " << ext2int[orig] << endl;
    // cout << "int2ext[" << v << "] = " << int2ext[v] << endl;

}
int IdMapper::mapInt2Ext(int lit) const {
    int v = abs(lit);
    bool sign = lit < 0;
    assert(v < int2ext.size());
    assert(int2ext[v] != -1);
    return int2ext[v] * (sign ? -1 : 1);
}
int IdMapper::mapExt2Int(int lit) const {
    int v = abs(lit);
    bool sign = lit < 0;
    assert(v < ext2int.size());
 
    assert(ext2int[v] != -1);
    return ext2int[v] * (sign ? -1 : 1);
}

void IdMapper::add_equation(const vector<int>& lhs,
                            const bool rhs) {
    vector<int> l;
    copy(lhs.begin(), lhs.end(), back_inserter(l));
    for (size_t i = 0; i < l.size(); i++) {
        if ((int)ext2int.size() <= l[i] || ext2int[l[i]] == -1)
            new_var(l[i]);
        l[i] = ext2int[l[i]];
    }
    ds.add_equation(l, rhs);


}

void IdMapper::syncImplied() {
    const vector<int>* intImplied = ds.get_implied_lits();
    for (size_t i = implied_lits.size(); i < intImplied->size(); i++) {
        implied_lits.push_back(mapInt2Ext((*intImplied)[i]));
    }
    const vector<int>* c = ds.get_conflict();
    for (size_t i = 0; i < c->size(); i++) {
        conflict.push_back(mapInt2Ext((*c)[i]));
    }

}
void IdMapper::explain(int lit, vector<int>& explanation)  {
//    std::cout << "idMapper explain  " << lit << endl;
    ds.explain(mapExt2Int(lit), explanation);
    for (size_t i = 0; i < explanation.size(); i++) {
        explanation[i] = mapInt2Ext(explanation[i]);
    }    
}

void IdMapper::dumpState() {
#ifdef DEBUG
    Split state(ds.getState(), "\n");
    for (size_t i = 0; i < state.size(); i++) {
        Split parts(state[i]);
        for (size_t i2 = 0; i2 < parts.size(); i2++) {
            if (isdigit(parts[i2][0]) || parts[i2][0] == '-') {
                if (parts[i2] == "0")
                    parts[i2] = "T";
                else
                    parts[i2] = bx::toString(mapInt2Ext(atoi(parts[i2].c_str())));
            } 
        }
        state[i] = parts.join(" ");
    }
    cout << "IDMAPPER STATE" << endl << endl;
    cout << state.join("\n") << endl << endl;
    
#endif
}
bool IdMapper::assume(int var, bool value) {
    if (var >= ext2int.size() || ext2int[var] == -1)
        return true;

    bool result = ds.assume(ext2int[var], value);
  
    syncImplied();
    return result;
}
