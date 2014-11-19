
#include <sys/time.h>
#include <fstream>
#include <assert.h>
#include <algorithm>
#include <boost/config.hpp>
#include <boost/graph/copy.hpp>
#include <set>
#include <deque>
#include <map>
#include <vector>
#include <list>
#include <math.h>
#include <sstream>
#include <iterator>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <boost/tokenizer.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/unordered_map.hpp>
#ifdef DEBUG
#define D(x) cerr << x;
#else
#define D(x)
#endif
int minSaving =  1;

int globalMaxVar;
using namespace std;
using namespace boost;
    typedef adjacency_list <vecS, vecS, undirectedS> Graph;

    std::string graphToString(const Graph& g) {
        std::ostringstream ost;
        write_graphviz(ost, g);
        return ost.str();
    }
  template <class T> std::string toString(const T& t) {
        std::ostringstream ost;
        ost << t;
        return ost.str();
    }

 template <> std::string toString(const set<int>& s) {
     std::ostringstream ost;
     for (set<int>::const_iterator si = s.begin(); si != s.end(); si++) {
         if (si != s.begin())
             ost << " ";
         ost << toString(*si);
     }
     return ost.str();
 }
 template <> std::string toString(const vector<int>& s) {
     std::ostringstream ost;
     for (vector<int>::const_iterator si = s.begin(); si != s.end(); si++) {
         if (si != s.begin())
             ost << " ";
         ost << toString(*si);
     }
     return ost.str();
 }



void printClause(const vector<int>& c) {
    cout << "x";
    for (size_t i = 0; i < c.size(); i++) {
        cout << " " << c[i];
    }
    cout << " 0" << endl;
}
int clauseNode(int c) {
    return globalMaxVar + 1 + c;
}
int varNode(int v) {
    return abs(v);
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




void makeGraph(Graph& g, 
               const vector<vector<int> >& clauses) {
    g.clear();
    for (size_t i = 0; i < clauses.size(); i++) {
        const vector<int>& c = clauses[i];
        for (size_t i2 = 0; i2 < c.size(); i2++) {
            D("add_edge(" << varNode(c[i2]) << "," << clauseNode(i) << ")" << endl);
            add_edge(varNode(c[i2]), clauseNode(i), g);
        }
    }
}
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
void readCandidates(const string& path, vector<vector<int> >& candidates) {
    ifstream f;
    f.open(path.c_str());
    string line;
    while (!f.eof()) {
        getline(f, line);
        if (line.empty() || !isdigit(line[0]))
            continue;
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
        sort(nums.begin(), nums.end());
        candidates.push_back(nums);
    }
    D("read " << candidates.size() << " candidate cuts" << endl);
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

void cutGraph(Graph& g,
              const vector<int>& vars,
              const vector<vector<int> >& varClauses,
              vector<int>& component) {

    for (size_t i = 0; i < vars.size(); i++) {
        int v = vars[i];
        clear_vertex(varNode(v), g);
//        remove_vertex(varNode(v), g);
    }
    component.resize(num_vertices(g));
    connected_components(g, &component[0]);
   
    set<int> toCheck;
    for (size_t i = 0; i < vars.size(); i++) {
        int v = vars[i];
        for (size_t i2 = 0; i2 < varClauses[v].size(); i2++) {
            toCheck.insert(varClauses[v][i2]);
            D("var " << v << " in clause " << varClauses[v][i2] << endl);
        }
    }   
    /*
    for (size_t i = 0; i < component.size(); i++) {
        D("component[" << i << "]: " << component[i] << endl);    
    }*/
    for (set<int>::iterator c1 = toCheck.begin(); c1 != toCheck.end(); c1++) {
        for (set<int>::iterator c2 = c1; c2 != toCheck.end(); c2++) {
            if (c1 == c2)
                continue;
            int n1 = clauseNode(*c1),
                n2 = clauseNode(*c2);
            int cmp1 = component[n1], cmp2 = component[n2];
            if (cmp1 == cmp2) {
                D("clauses " << *c1 << " and " << *c2 << " in same component" << endl);
                add_edge(n1, n2, g);
                D("add_edge(" << n1 << "," << n2 << ")"<< endl);
            }
        }
    }
    connected_components(g, &component[0]);
}

typedef map<int, pair<set<int>, set<int> > > Cmap;

void makeCmap(Cmap& cmap,
              const vector<int>& component, 
              const vector< vector<int> >& clauses) {
    for (size_t i = 0; i < clauses.size(); i++) {
        int n = clauseNode(i);
        int c = component[n];
        if (cmap.find(c) == cmap.end())
            cmap[c] = make_pair(set<int>(), set<int>());
        Cmap::iterator cmi = cmap.find(component[n]);
        for (size_t i2 = 0; i2 < clauses[i].size(); i2++) {
            cmi->second.first.insert(abs(clauses[i][i2]));
        }
        cmi->second.second.insert(i);
    }

}
              

long long graphSize(const vector<int>& component, 
                    const vector< vector<int> >& clauses,
                    const vector< vector<int> >& cuts) {
    Cmap cmap;
    makeCmap(cmap, component, clauses);
    long long size = 0;
    for (Cmap::iterator cmi = cmap.begin();
            cmi != cmap.end(); cmi++) {
        int tw = cmi->second.first.size();
        int th = cmi->second.second.size();
        D("cmap[" << cmi->first << "] : " << cmi->second.first.size()
                << "x" << cmi->second.second.size());
        for (size_t i = 0; i < cuts.size(); i++) {
            const vector<int>& cut = cuts[i];
            bool found = false;
            for (size_t i2 = 0; i2 < cut.size(); i2++) {
                if (cmi->second.first.find(cut[i2]) != cmi->second.first.end()) {
                    found = true;
                    break;
                }
            }
            if (found) {
                int w = cut.size();
                int extraVars = pow((double) 2, (double) w) - (w+1);
                D(" + " << extraVars << "x" << extraVars);
                tw += extraVars;
                th += extraVars;                
            }
        }
        D(endl);

        size += tw * th;
    }
    return size;
}

void decompose(const vector< vector<int> >& clauses,
        const vector<int> & clauseIds,
        vector<vector<int> >& allCandidates) {
    vector<vector<int> > varClauses;
    vector<int> component;
    vector<vector<int> >candidates;
    vector<vector<int> > cuts;
    set<int> allVars;

    for (size_t i = 0; i < clauses.size(); i++) {
        const vector<int>& c = clauses[i];
        for (size_t j = 0; j < c.size(); j++) {
            int v = abs(c[j]);

            allVars.insert(v);
            if (varClauses.size() <= v)
                varClauses.resize(v+1);
            varClauses[v].push_back(i);
        }
    }
    for (size_t i = 0; i < allCandidates.size(); i++) {
        vector<int> result;
        vector<int>& cand = allCandidates[i];
        set_intersection(cand.begin(), cand.end(),
                         allVars.begin(), allVars.end(),
                         back_inserter(result));
        if (result.size () == cand.size()) {
            candidates.push_back(cand);
        } 
    }
    cerr << "going to test " << candidates.size() << " out of " << allCandidates.size() << " candidates for this xor-component" << endl;

    static int cycleComponent = 1;
    Graph prev;
    makeGraph(prev, clauses);
    while (true) {

        Graph g;
        copy_graph(prev, g);

        component.resize(num_vertices(g));
        connected_components(g, &component[0]);
        long long currentSize = graphSize(component, clauses, cuts);
        D("current size : " << currentSize << endl);
        long long bestSize = currentSize;
        int bestCandidate = -1;

        for (size_t i = 0; i < candidates.size();) {
            cerr << "testing " << i+1 << "/" << candidates.size() << " (" << cuts.size() << " selected)" << endl;

            g.clear();
            copy_graph(prev, g);

            cutGraph(g, candidates[i], varClauses, component);
            cuts.push_back(candidates[i]);
            long long cutSize = graphSize(component, clauses, cuts);
            cuts.pop_back();
            cerr << "after test-cutting with cut set " << toString(candidates[i]) << " memory consumption improved by " << currentSize - cutSize << endl;
            if (cutSize < bestSize && cutSize < currentSize - minSaving) {

                bestSize = cutSize;
                bestCandidate = i;
                i++;
            }  else {
                candidates[i] = candidates.back();
                candidates.pop_back();
            }
        }
        if (bestCandidate != -1) {
            g.clear();
            copy_graph(prev, g);

            cerr << "cutting with cut set " << toString(candidates[bestCandidate]) << " and this saves " << (currentSize - bestSize) << " elements";
            cutGraph(g, candidates[bestCandidate], varClauses, component);
            cuts.push_back(candidates[bestCandidate]);
            for (size_t i = 0; i < candidates.size(); ) {
                vector<int> r;
                set_intersection(candidates[i].begin(),
                                 candidates[i].end(),
                                 cuts.back().begin(),
                                 cuts.back().end(),
                                 back_inserter(r));
                if (!r.empty()) {
                    D("removing candidate cut set " << toString(candidates[i]) << endl);
                           
                    candidates[i] = candidates.back();
                    candidates.pop_back();
                } else
                    i++;                
            }
            prev.clear();
            copy_graph(g, prev);
        } else
            break;
    }
    component.resize(num_vertices(prev));
    connected_components(prev, &component[0]);
    Cmap cmap;
    makeCmap(cmap, component, clauses);
    vector< vector<vector<int> > > extraRowSets;
    extraRowSets.resize(cuts.size());
    for (size_t i = 0; i < cuts.size(); i++) {
        getExtraRows(cuts[i], extraRowSets[i]);
    }

    for (Cmap::iterator cmi = cmap.begin(); cmi != cmap.end(); cmi++) {
        cout << "c xor-cycle-component " << cycleComponent++ << endl;
        for (set<int>::iterator c = cmi->second.second.begin();
                c != cmi->second.second.end(); c++) {
            printClause(clauses[*c]);
        }

        for (size_t i = 0; i < cuts.size(); i++) {
            const vector<int>& cut = cuts[i];
            bool found = false;
            for (size_t i2 = 0; i2 < cut.size(); i2++) {
                if (cmi->second.first.find(cut[i2]) != cmi->second.first.end()) {
                    found = true;
                    break;
                }
            }
            if (found) {
                cout << "c interface " << toString(cut) << endl;
                for (size_t i2 = 0; i2 < extraRowSets[i].size(); i2++) {
                    printClause(extraRowSets[i][i2]);
                }
            }
        }
    }
}
                 
int main(int argc, char** argv) {

    struct timeval tv1, tv2;
    gettimeofday(&tv1, NULL);
    vector< vector<int> > clauses;
    vector<int> ccomponent;
    vector< vector<int> > candidates;
    readClauses(clauses, ccomponent);
    readCandidates(argv[1], candidates);
    if (argc > 2)
        minSaving = atoi(argv[2]);
    int nextCliqueId = 1;
    map<int, vector< vector<int> >  > clauseComponents;
    map<int, vector<int>  > clauseId;

    for (size_t i = 0; i < clauses.size(); i++) {
        clauseComponents[ccomponent[i]].push_back(clauses[i]);
        clauseId[ccomponent[i]].push_back(i);
    }
    

    for (map<int, vector< vector<int> > >::const_iterator cci = 
            clauseComponents.begin(); cci != clauseComponents.end(); cci++) {

        cerr << "Component[" << cci->first << "] : " << 
            cci->second.size() << " clauses"
            << endl;
        decompose(cci->second, clauseId[cci->first], candidates);

    }    
    gettimeofday(&tv2, NULL);
    double msecs = (tv2.tv_sec - tv1.tv_sec) *1000.0 
                  + (tv2.tv_usec / 1000.0 - tv1.tv_usec / 1000.0);
    cerr << "xcnf-decompose took " <<  msecs << " ms" << endl;
    return 0;
}

