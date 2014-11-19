
#include <sys/time.h>

#include <assert.h>
#include <algorithm>
#include <set>
#include <deque>
#include <map>
#include <vector>
#include <list>
#include <math.h>
#include <iterator>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <boost/tokenizer.hpp>

#ifdef DEBUG
#define D(x) cerr << x;
#else
#define D(x)
#endif

using namespace std;
void printClause(const vector<int>& c) {
    cout << "x";
    for (size_t i = 0; i < c.size(); i++) {
        cout << " " << c[i];
    }
    cout << " 0" << endl;
}
void readClauses(vector<vector<int> >& clauses,
                vector<int>& ccomponent) {

    string line;
    bool treelike = false;
    int cmpId = -1;
    while (getline(cin, line)) {

        if (line.empty())
            continue;
        if (line.substr(0, 21) == "c xor-cycle-component") {
            treelike= false;
            cmpId = atoi(line.substr(21, line.size()).c_str());

            if (cmpId == 0) {
                cerr << "Could not parse xor-cycle-component id in line '" << line << "'" << endl;
            }
            continue;

        } else if (line.substr(0, 25) == "c xor-tree-like-component") {
            cout << line << endl;
            treelike = true;
            continue;
        }
        if (line[0] != 'x' || treelike) {
           cout << line << endl;
            continue;
        }
        if (cmpId < 1) {
            cerr << "expected c xor-cycle-component" << endl;
            exit(-1);
            continue;
        }

        typedef boost::tokenizer<boost::char_separator<char> > 
            tokenizer;
        boost::char_separator<char> sep(" ");
        tokenizer tok(line, sep);
        vector<int> nums;
        for (tokenizer::iterator i = tok.begin();
                i != tok.end(); i++) {
            int num = atoi((*i).c_str());
            if (num) {
                nums.push_back(num);
            }

        }
        ccomponent.push_back(cmpId);
        clauses.push_back(nums);
    }
}

struct Info {
    int componentId;
    int vars;
};
struct Sorter {
    bool operator()(const Info& i1, const Info& i2) const {
        return (i1.vars < i2.vars);
    }
};
int main(int argc, char** argv) {

    vector< vector<int> > allClauses;
    vector<int> ccomponent;
    readClauses(allClauses, ccomponent);
    map<int, vector< vector<int> >  > clauseComponents;

    for (size_t i = 0; i < allClauses.size(); i++) {
        clauseComponents[ccomponent[i]].push_back(allClauses[i]);
    }
    allClauses.clear();
    vector< Info> infos;
    for (map<int, vector< vector<int> > >::const_iterator cci = 
            clauseComponents.begin(); cci != clauseComponents.end(); cci++) {

        set<int> vars;
        const vector< vector<int> >& clauses = cci->second;
        for (size_t i = 0; i < clauses.size(); i++) {
            for (size_t i2 = 0; i2 < clauses[i].size(); i2++) {
                vars.insert(abs(clauses[i][i2]));
            }
        }
        Info info;
        info.componentId = cci->first;
        info.vars = vars.size();
        infos.push_back(info);
        cerr << "Component[" << cci->first <<"]: " << vars.size() << "x" << cci->second.size() << endl;

    }    
    sort(infos.begin(), infos.end(), Sorter());

    vector< vector<int> > current;
    set<int> currentVars;
    int nextComponentId = 1;
    for (size_t i = 0; i < infos.size(); i++) {
        int cId = infos[i].componentId;
        cerr << "Adding component[" << 
            cId << "]: " << 
            infos[i].vars << "x" << clauseComponents[cId].size() << endl;

        const vector<vector<int> >& clauses = clauseComponents[cId];
        for (size_t i = 0; i < clauses.size(); i++) {
            for (size_t i2 = 0; i2 < clauses[i].size(); i2++) {
                currentVars.insert(abs(clauses[i][i2]));
            }
            current.push_back(clauses[i]);
        }
        if (currentVars.size() >= 64 || i == infos.size() - 1) {
            cerr << "Posting matrix: " << currentVars.size() << "x" << current.size() << endl;
            
            cout << "c xor-cycle-component " << nextComponentId++ << endl;
            for (size_t i = 0; i < current.size(); i++) {
                printClause(current[i]);
            }
            current.clear();
            currentVars.clear();
        }
    }  
    return 0;
}

