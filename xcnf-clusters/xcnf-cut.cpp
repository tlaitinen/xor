
#include <sys/time.h>

#include <assert.h>
#include <algorithm>
#include <boost/config.hpp>
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
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/unordered_map.hpp>
#include "igraph.h"
#ifdef DEBUG
#define D(x) cerr << x;
#else
#define D(x)
#endif
int minSaving =  5000;

int globalMaxVar;
using namespace std;
void printClause(const vector<int>& c) {
    cout << "x";
    for (size_t i = 0; i < c.size(); i++) {
        cout << " " << c[i];
    }
    cout << " 0" << endl;
}
int getConnectedComponents(
                           const vector< pair<int, int> >& edges,
                           vector< int >& component
        ) {
    using namespace boost;
    typedef adjacency_list <vecS, vecS, undirectedS> Graph;
    Graph g;

    for (size_t i =0 ; i < edges.size(); i++) {
        add_edge(edges[i].first, edges[i].second, g);
    }
    component.resize(num_vertices(g));
    int numComponents = connected_components(g, &component[0]);
    return numComponents;
}

template <class InputIterator1, class InputIterator2>
  size_t set_intersection_size (InputIterator1 first1, InputIterator1 last1,
                                InputIterator2 first2, InputIterator2 last2)
{
    size_t count = 0;
    while (first1!=last1 && first2!=last2)
    {
        if (*first1<*first2) ++first1;
        else if (*first2<*first1) ++first2;
        else {
            count++;
            ++first1; ++first2;
        }
    }
    return count;
}

class TreeDecomposition {
    vector< vector<int> > clauses;
    vector<int> clauseIds;
    vector< vector<int> > varClauses;
    vector< set<int> > cliques;
    vector< pair<int, int> > edges;
    vector< pair<int, int> > mstEdges;
    map<int, vector<int> > neighbors;
    vector< set<int> > nodeClauses;
    map<int, int> idMap;
    map<int, int> invIdMap;
    map<int, int> clauseIdMap;
    map<int, int> clauseInvIdMap;
       
    int maxVar;
    static int nextCliqueId;
    public:
    pair<int, int> dimensions() const {
        return make_pair(maxVar, clauses.size());
    }
 

    private:
    public:
    TreeDecomposition(const vector< vector<int> >& clauses_,
                      const vector<int>& clauseIds_) 
        : clauses(clauses_), clauseIds(clauseIds_) {
        for (size_t i = 0; i < clauses.size(); i++) {
            vector<int>& c = clauses[i];
            for (size_t j = 0; j < c.size(); j++) {
                int v = abs(c[j]);
                if (varClauses.size() <= v)
                    varClauses.resize(v+1);
                varClauses[v].push_back(i);
            }
        }

            for (size_t i = 0; i < clauseIds.size(); i++) {
                D("clauseIdMap[" << clauseIds[i] << "] = " << i << endl);
                clauseIdMap[clauseIds[i]] = i;
                D("clauseInvIdMap[" << i << "] = " << clauseIds[i] << endl);
                clauseInvIdMap[i] = clauseIds[i];
            }

        }

   void cut(
                 const vector<int>& ivars,
                 vector<vector<int> >& bestClauses) {

       long long orig = getVarNum() * getClauseNum();

       vector< pair<int, int> > cEdges;
       for (size_t i = 0; i < clauses.size(); i++) {
           vector<int>&c = clauses[i];

           cEdges.push_back(make_pair(i,i));
           for (size_t i2 = 0; i2 < c.size(); i2++) {
               int v = abs(c[i2]);
               bool isIvar = false;
               for (size_t i3 = 0; i3 < ivars.size(); i3++) {
                   if (ivars[i3] == v) {
                       isIvar = true;
                       break;
                   }
               }
               if (isIvar)
                   continue;
               assert(v >= 0 && v < varClauses.size());
               for (size_t i3 = 0; i3 < varClauses[v].size(); i3++) {
                   int c2 = varClauses[v][i3];
                   if (c2 != i)
                       cEdges.push_back(make_pair(i, c2));
               }
           }
       }
       vector<int> component;
       getConnectedComponents(cEdges, component);

       map< int, vector<int> > clauseGroups;
       for (size_t i = 0; i < clauses.size(); i++) {
           int c = component[i];
           clauseGroups[c].push_back(i);
       }

       long long decomposedSize = 0;
       int w = ivars.size();
       int extraVars = pow((double) 2, (double) w) - (w + 1);
#ifdef DEBUG
       vector<set<int> > varGroups;
#endif
       for (map<int, vector<int> >::iterator i = clauseGroups.begin();
               i !=  clauseGroups.end(); i++) {
           const vector<int>& cg = i->second;
           set<int> vars;
           for (size_t i2 = 0; i2 < cg.size(); i2++) {
               const vector<int>& clause = clauses[cg[i2]];
               for (size_t i3 = 0; i3 < clause.size(); i3++) {
                   vars.insert(abs(clause[i3]));
               }
           }
#ifdef DEBUG
           varGroups.push_back(vars);
#endif
           cerr << "ClauseGroup " << i->first << " " << vars.size() << "x" << cg.size() << " + " << extraVars << "x" << extraVars << endl;
           decomposedSize += (vars.size() + extraVars) * (cg.size() + extraVars);
       }
#ifdef DEBUG
       for (size_t i = 0; i < varGroups.size(); i++) {
           for (size_t i2 = i+1; i2 < varGroups.size(); i2++) {
               set<int>& v1 = varGroups[i];
               set<int>& v2 = varGroups[i2];
               vector<int> vint;
               set_intersection(v1.begin(), v1.end(),
                       v2.begin(), v2.end(), back_inserter(vint));
               cerr << "ClauseGroup " << i << " with " << varGroups[i].size()
                   << " vars and " << endl;
               cerr << "ClauseGroup " << i2 << " with " << varGroups[i2].size()
                   << " vars" << endl;
               cerr << " has " << vint.size() << " vars in common" << endl;

               for (size_t i3 = 0; i3 < vint.size(); i3++) {
                   bool found = false;
                   for (size_t i4 = 0; i4 < ivars.size(); i4++) {
                       if (ivars[i4] == vint[i3]) {
                           found = true;
                           break;
                       }
                   }
                   if (!found) {
                       cerr << "var groups " << i << " and " << i2 << " share a non-interface variable " << vint[i3] << endl;
                       assert(false);
                   }
               }

           }
       }
#endif
       cerr << "Cutting at ";
       for (size_t i = 0; i < ivars.size(); i++)
           cerr << " " << ivars[i];
       cerr << endl;


       bestClauses.clear();
       for (map<int, vector<int> >::iterator i = clauseGroups.begin();
               i != clauseGroups.end(); i++) {
           bestClauses.push_back(i->second);
       }
       for (size_t i = 0; i < bestClauses.size(); i++) {
           vector<int>& bc = bestClauses[i];
           for (size_t i2 = 0; i2 < bc.size(); i2++) {
//               cerr << "best clause from " << bc[i2];
               bc[i2] = clauseInvIdMap[bc[i2]];
//               cerr << " to " << bc[i2] << endl;
           }
       }
   }
                         
            
   int getVarNum() {
        return maxVar + 1;
   }
   int getClauseNum() {
       return clauses.size();
   }

   void getClauses(int v, vector<int>& cids) {
       cids.clear();
       for (size_t i = 0; i < varClauses[v].size(); i++) {
           cids.push_back(clauseInvIdMap[varClauses[v][i]]);

       }
   }
   void getClause(int c, vector<int>& clause) {
       assert(clauseIdMap.find(c) != clauseIdMap.end());
       clause = clauses[clauseIdMap[c]];
   }

};

int TreeDecomposition::nextCliqueId = 1;

void readClauses(vector<vector<int> >& clauses,
                vector<int>& ccomponent) {

    globalMaxVar = 0;
    string line;
    bool treelike = false;
    int cmpId = -1;
    while (getline(cin, line)) {

        if (line.empty())
            continue;
        if (line.substr(0, 21) == "c xor-cycle-component") {
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
            if (isdigit(line[0]) || line[0] == '-') {
                typedef boost::tokenizer<boost::char_separator<char> > 
                    tokenizer;
                boost::char_separator<char> sep(" ");
                tokenizer tok(line, sep);
                for (tokenizer::iterator i = tok.begin();
                        i != tok.end(); i++) {
                    int num = atoi((*i).c_str());
                    if (num) {
                        if (abs(num) > globalMaxVar)
                            globalMaxVar = abs(num);
                    }

                }
            }

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
                if (abs(num) > globalMaxVar)
                    globalMaxVar = abs(num);
                nums.push_back(num);
            }

        }
        ccomponent.push_back(cmpId);
        clauses.push_back(nums);
    }
}

void getExtraRows(const vector<int>& ivars, 
                  vector< vector<int> >& rows) {
    unsigned int limit = 1;
    unsigned int tmp = ivars.size();
    limit <<= tmp;
    for (unsigned int i = 1; i < limit; i++) {
        vector<int> row;
        for (size_t i2 = 0; i2 < ivars.size(); i2++) {
            tmp = 1;
            tmp <<= i2;
            if (i & tmp) {
                row.push_back(ivars[i2]);
            }
        }
        if (row.size() > 1) {
            row.push_back(++globalMaxVar);
            rows.push_back(row);

        }
    }
}
        
void decompose(const vector< vector<int> >& clauses,
               const vector<int> & clauseIds,
               const vector<int> & ivars) {
    TreeDecomposition tree(clauses, clauseIds);
    vector< vector<int> > clauseGroups;
    tree.cut(ivars, clauseGroups);
    static int cycleComponent = 1;

    if (!ivars.empty()) {
        long long orig = tree.getVarNum() * tree.getClauseNum();
        vector<vector<int> > extraRows;
        getExtraRows(ivars, extraRows);

        for (size_t cg = 0; cg < clauseGroups.size(); cg++) {
            vector<int>& bestClauses = clauseGroups[cg];
            cout << "c xor-cycle-component " << cycleComponent++ << endl;

            for (vector<int>::iterator i = bestClauses.begin(); 
                    i != bestClauses.end(); i++) {
                vector<int> clause;


                tree.getClause(*i, clause);

                printClause(clause);
            }
            for (size_t i = 0; i < extraRows.size(); i++) {
                printClause(extraRows[i]);
            }
        }

    } else {
        cout << "c xor-cycle-component " << cycleComponent++ << endl;

        for (size_t i = 0; i < clauses.size(); i++) {
            printClause(clauses[i]);
        }
    }

}

int main(int argc, char** argv) {

    struct timeval tv1, tv2;
    gettimeofday(&tv1, NULL);
    vector< vector<int> > clauses;
    vector<int> ccomponent;
    readClauses(clauses, ccomponent);
    int nextCliqueId = 1;
    D("DOT: digraph d {" << endl);
    map<int, vector< vector<int> >  > clauseComponents;
    map<int, vector<int>  > clauseId;
    map<int, vector<int> > ivars;

    int cmpId = -1;
    vector<int> iv;
    for (int i = 1; i < argc; i++) {
        int v = atoi(argv[i]);
        if (cmpId == -1) {
            cmpId = v;
            iv.clear();
        } else  {
            if (v == 0) {
                ivars[cmpId] = iv;
                iv.clear();
                cmpId = -1;
            } else {
                iv.push_back(v);
            }
        }
    }
        

    for (size_t i = 0; i < clauses.size(); i++) {
        clauseComponents[ccomponent[i]].push_back(clauses[i]);
        clauseId[ccomponent[i]].push_back(i);
    }
    

    for (map<int, vector< vector<int> > >::const_iterator cci = 
            clauseComponents.begin(); cci != clauseComponents.end(); cci++) {

        cerr << "Component[" << cci->first << "] : " << 
            cci->second.size() << " clauses"
            << endl;
        if (ivars.find(cci->first) != ivars.end())
            cerr << "cutting with " << ivars[cci->first].size() << " variables" << endl;

        decompose(cci->second, clauseId[cci->first], ivars[cci->first]);

    }    
    gettimeofday(&tv2, NULL);
    double msecs = (tv2.tv_sec - tv1.tv_sec) *1000.0 
                  + (tv2.tv_usec / 1000.0 - tv1.tv_usec / 1000.0);
    cerr << "xcnf-cut took " <<  msecs << " ms" << endl;
    D("DOT: }" << endl);       
    return 0;
}

