#include <boost/config.hpp>
#include <vector>
#include <list>
#include <iterator>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <set>
#include <boost/tokenizer.hpp>
#include "IdMapper.hpp"
#include "Simplex.h"

using namespace std;

//vector<IdMapper*> mtx;
//vector<Matrix*> matrices;
//vector< set<int> > varInMtx;
//set<int> cnfVars;

bool startsWith(const string& s1, const string& s2) {
    return s1.substr(0, s2.size()) == s2;
}
void processMatrix(int i, int varNum, Simplex* d, bool treelike=false) {
   
/*    for (size_t i = 0; i < mtx.size(); i++) {
        Matrix* m = mtx[i]->simplify();
        cout << "M[" << i << "]: ";
        if (!m) {
            cout << "UNSAT" << endl; 
        } else {
            cout << m->getWidth()-1 << " " << m->getHeight() << endl;

        }
    }
*/
//    Matrix* m = d->simplify();
    cout << "M[" << i << "]: ";
    
    if (d->is_sat() == false) {
        cout << "UNSAT" << endl; 
    } else {
        cout << varNum << " " << d->getRowNum() << " " << (int) treelike << endl;

    }
}
int readClauses() {
    string line;
    int maxVar = 0;
    //IdMapper* d = new IdMapper();
    Simplex* d = new Simplex();
    set<int> vars;


    int clauses = 0;
    int mtx = 0;
    bool treelike = false;
    while (getline(cin, line)) {

        if (line.empty())
            continue;
        if (line[0] != 'x') {
            string prefix = "c xor-cycle-component";
            bool dump = false;
            if ((startsWith(line, "c xor-cycle-component")
                    || startsWith(line, "c xor-tree-like-component")
                    || startsWith(line, "c xor-cluster"))) {
        

                if (clauses > 0) {
                    processMatrix(mtx, vars.size(), d, treelike);

                    vars.clear();

                    delete d;
                    maxVar = 0;
//                    d = new IdMapper();
                    d = new Simplex();
                    clauses = 0;
                    mtx++;

                }

                treelike = startsWith(line, "c xor-tree-like-component");
            }

            if (line[0] != '-' && !isdigit(line[0]))
                continue;
        }

        typedef boost::tokenizer<boost::char_separator<char> > 
            tokenizer;
        boost::char_separator<char> sep(" ");
        tokenizer tok(line, sep);
        vector<unsigned int> lhs;
        bool rhs = true;
        for (tokenizer::iterator i = tok.begin();
                i != tok.end(); i++) {
            int num = atoi((*i).c_str());
            if (num) {
                while (abs(num) > maxVar) {
                    maxVar = (int) d->new_var();
                }
                if (line[0] == 'x')
                    vars.insert(abs(num));
                lhs.push_back(abs(num));
                if (num < 0)
                    rhs = !rhs;
            }


        }
        if (line[0] == 'x') {

            d->add_equation(lhs, rhs);
            clauses++;
        }

    }
    if (clauses > 0) {
        processMatrix(mtx, vars.size(), d, treelike);

    }
    delete d;
}

int main() {
    readClauses();
    return 0;
}

