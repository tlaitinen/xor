#include <boost/config.hpp>
#include <vector>
#include <list>
#include <iterator>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <set>
#include <boost/tokenizer.hpp>
#include "DSimplex.hpp"

using namespace std;

vector<DSimplex*> mtx;
vector<Matrix*> matrices;
vector< set<int> > varInMtx;
set<int> cnfVars;
void printClause(const vector<int>& c, bool stdOut = true) {
    ostream& o = stdOut ? cout : cerr;
    o << "x";
    for (size_t i = 0; i < c.size(); i++) {
        o << " " << c[i];
    }
    o << " 0" << endl;
}
bool startsWith(const string& s1, const string& s2) {
    return s1.substr(0, s2.size()) == s2;
}
int readClauses() {
    string line;
    int maxVar = 0;

    int xorCycleComponent = 0;
    bool xorTreelikeComponent = false;
    while (getline(cin, line)) {

        if (line.empty())
            continue;
        if (line[0] != 'x') {
            string prefix = "c xor-cycle-component";
            if (startsWith(line, prefix)) {
                xorCycleComponent = atoi(line.substr(prefix.size(), line.size()).c_str());
                xorTreelikeComponent = false;
                continue;
            }
            if (startsWith(line, "c xor-tree-like-component")) {
                xorTreelikeComponent = true;
                continue;
            }

            cout << line << endl;
            if (line[0] != '-' && !isdigit(line[0]))
                continue;
        }

        typedef boost::tokenizer<boost::char_separator<char> > 
            tokenizer;
        boost::char_separator<char> sep(" ");
        tokenizer tok(line, sep);
        vector<int> lhs;
        bool rhs = true;
        for (tokenizer::iterator i = tok.begin();
                i != tok.end(); i++) {
            int num = atoi((*i).c_str());
            if (num) {

                lhs.push_back(abs(num));
                if (num < 0)
                    rhs = !rhs;
            }


        }
        if (line[0] == 'x') {
            while (mtx.size() <= xorCycleComponent) 
                mtx.push_back(new DSimplex());

            int m = 0;
            if (xorTreelikeComponent)
                mtx[0]->add_equation(lhs, rhs);
            else {
                m = xorCycleComponent;
                mtx[xorCycleComponent]->add_equation(lhs, rhs);
            }
            for (size_t i = 0; i < lhs.size(); i++) {
                if (varInMtx.size() <= lhs[i])
                    varInMtx.resize(lhs[i] + 1);
                varInMtx[lhs[i]].insert(m);
            }
        } else {
            for (size_t i = 0; i < lhs.size(); i++)
                cnfVars.insert(lhs[i]);
        }
    }
}
void eliminate(int v) {
    assert(varInMtx[v].size() == 1);
    int mId = *varInMtx[v].begin();
    DSimplex& m_= *mtx[mId];
    Matrix& m = *matrices[mId];

    int minOccurrences = m_.getVarNum() + 1;
    int defRow = -1;

    vector<int> row;
    vector<int> rows;
    m.getCol(v,rows);
    if (rows.empty()) {
        // already eliminated
        return;
    }
    assert(rows.size() > 0);
    for (size_t i = 0; i < rows.size(); i++) {
        int r = rows[i];
        m.getRow(r, row);
        int numVars = 0;
//        bool found =false;
        for (size_t i = 0; i < row.size(); i++) {
            if (row[i]) {
                numVars++;
//                if (row[i] == v)
//                    found = true;
            }
        }
//        if (found)
//            rows.push_back(r);
        if (/*found && */numVars < minOccurrences) {
            minOccurrences = numVars;
            defRow = r;
        }
    }
    assert(defRow != -1);
    
    for (size_t i = 0; i < rows.size(); i++) {
        int r = rows[i];
        if (r != defRow)
            m.addRow(defRow, r);
    }
    
    vector<int>  nums;
    m.getRow(defRow, row);
    m.addRow(defRow, defRow);
    bool rhs = false;
    for (size_t i = 0; i < row.size(); i++) {
        int v = row[i];
        if (!v) {
            rhs = !rhs;
        } else {
            nums.push_back(v);
        }
    }
    if (!rhs)
        nums[0] = -nums[0];
   printClause(nums, false);

//   cout << "after eliminating " << v << endl;
//    cout << m_.getState() << endl;
}
void dumpMatrix(DSimplex& m, int mtxId) {
    vector<int> row;
    vector<int> nums;

    bool first = true;
    for (int r = 0; r < m.getRowNum(); r++) {
        nums.clear();
        m.getRow(r, row);
        bool rhs = false;
        if (row.empty())
            continue;
        for (size_t i = 0; i < row.size(); i++) {
            int v = row[i];
            if (!v) {
                rhs = !rhs;
            } else {
                nums.push_back(v);
            }
        }
        if (nums.empty())
            continue;
        if (!rhs)
            nums[0] = -nums[0];
        if (first) {
            first= false;
            if (mtxId == 0) {
                if (mtx.size() > 1)
                    cout << "c xor-tree-like-component" << endl;
            } else
                cout << "c xor-cycle-component " << mtxId << endl;

        }
        printClause(nums);
    }
    
}
int main() {
    readClauses();
    for (size_t i = 0; i < mtx.size(); i++) {
        matrices.push_back(mtx[i]->simplify());
    }


    int numEliminated = 0;
    for (size_t i =1; i < varInMtx.size(); i++) {
        if (varInMtx[i].size() == 1 && cnfVars.find(i) == cnfVars.end()) {
            eliminate(i);
            numEliminated++;
        }
    }


    for (size_t i = 1; i < mtx.size(); i++) {
        if (mtx[i]->getRowNum() > 0) {
            dumpMatrix(*mtx[i], i);
        }
    }

    if (!mtx.empty()) {
        dumpMatrix(*mtx[0], 0);
    }

    cout << "c eliminated " << numEliminated << " xor-internal variables" << endl;
    return 0;
}

