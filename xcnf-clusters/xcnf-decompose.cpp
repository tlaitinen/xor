
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
int minSaving =  10000;

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
    void lexBfs(int vtxNum,
            boost::unordered_map<int, vector<int>  >& edges, vector<int>& out) {
        vector<int> labels;
        vector<bool> numbered;
        labels.resize(vtxNum);
        numbered.resize(vtxNum);

        for (int i = 1; i <= vtxNum; i++) {
            int maxLabel = -1;
            int maxNode = -1;
            for (size_t i2 = 0; i2 < labels.size(); i2++) {
                if (numbered[i2])
                    continue;
                if (labels[i2] > maxLabel) {
                    maxLabel = labels[i2];
                    maxNode = i2;
                }
            }
            assert(maxNode != -1);
            out.push_back(maxNode);
            numbered[maxNode] = true;
            vector<int>& e = edges[maxNode];
            for (size_t i2 = 0; i2 < e.size(); i2++) {
                int w = e[i2];
                assert(w >= 0 && w < numbered.size());
                if (numbered[w])
                    continue;
                assert(w >= 0 && w < labels.size());
                labels[w] += vtxNum - i + 1;
            }

        }
        return;
    }

    void maximalCliques(int vtxNum, 
            boost::unordered_map<int, vector<int>  >& edges, 
            const vector<int>& ordering,
            vector<set<int> >& out) {
        int c = 0;
        vector<int> ordPos;
        ordPos.resize(vtxNum);
        for (size_t i = 0; i < ordering.size(); i++) {
            ordPos[ordering[i]] = i;
        }

        for (size_t i = 0; i < ordering.size(); i++) {
            int v = ordering[i];
            set<int> clique;
            for (size_t k = 0; k < edges[v].size(); k++) {
                int w = edges[v][k];
                if (ordPos[w] > i) {
                    // cout << "edge between " << v << " and " << w << endl;
                    clique.insert(w);
                }
            }
            if (clique.empty())
                continue;

            clique.insert(v);
            bool isSubset = false;
            for (size_t j = 0; j < out.size(); j++) {
                if (includes(out[j].begin(), out[j].end(),
                            clique.begin(), clique.end())) {
                    isSubset = true;
                    break;
                }

            }
            if (!isSubset) {
#ifdef DEBUG
                cerr << "Clique[" << ++c << "]:";
                cerr << clique.size() << endl;
#endif
                /*    for (set<int>::iterator si = cliques[i].begin();
                      si != cliques[i].end(); si++) {
                      cout << " " << *si;
                      }
                      cout << endl;
                 */

                out.push_back(clique);
            }
        }
    }
    int compressEdges() {
        int id = 0;
        for (size_t i = 0; i < edges.size(); i++) {
            pair<int, int> e = edges[i];
            if (idMap.find(e.first) == idMap.end()) {

                idMap[e.first] = id++;
            }
            if (idMap.find(e.second) == idMap.end()) {
                idMap[e.second] = id++;
            }
            edges[i].first = idMap[e.first];
            edges[i].second = idMap[e.second];
        }
         for (map<int, int>::const_iterator i = idMap.begin(); i != idMap.end(); i++) {
            invIdMap[i->second] = i->first;
        }
     
        return id -1;
    }

    void primalGraph() {
        set<pair<int, int > > added;
        for (size_t i = 0; i < clauses.size(); i++) {
            vector<int>& c = clauses[i];
            for (size_t j = 0; j < c.size(); j++) {
                int v = abs(c[j]);
                if (varClauses.size() <= v)
                    varClauses.resize(v+1);
                varClauses[v].push_back(i);

                for (size_t k = j+1; k < c.size(); k++) {
                    int c1 = abs(c[j]), c2 = abs(c[k]);
                    if (c1 > c2) 
                        swap(c1,c2);
                    if (c1 != c2 && added.find(make_pair(c1,c2)) == added.end()) {
                        added.insert(make_pair(c1,c2));
                        edges.push_back(make_pair(c1,c2));
                    }
                }
            }
        }

        maxVar = compressEdges();
    }
    void makeTreeDecomposition() {
        igraph_t g;

        int ret = 0;
        if ((ret = igraph_empty(&g, 1+maxVar /*clauses.size()*/, false)) != 0) {
            cerr << "igraph_empty : " << ret << endl;
            exit(-1);
        }
        igraph_vector_t edges_v;
        igraph_vector_init(&edges_v, edges.size() * 2) ; 
        for (size_t i = 0; i < edges.size(); i++) {
            assert(edges[i].first >=0 && edges[i].first <= maxVar); //clauses.size());
            assert(edges[i].second >= 0 && edges[i].second <= maxVar); //clauses.size());
            igraph_vector_set(&edges_v, 2*i, edges[i].first);
            igraph_vector_set(&edges_v, 2*i + 1, edges[i].second);
        }
        igraph_add_edges(&g, &edges_v, NULL);
        igraph_vector_destroy(&edges_v);
        igraph_bool_t chordal = 0;

        igraph_t cg;

        if ((ret = igraph_is_chordal(&g, NULL, NULL,
                        &chordal,
                        NULL,
                        &cg))) {
            cerr << "igraph_is_chordal : " << ret << endl;
            exit(-1);
        }
        if ((ret = igraph_destroy(&g)) != 0) {
            cerr << "igraph_destroy : " << ret << endl;
            exit(-1);
        }
        int newEdges = igraph_ecount(&cg);

        cerr << newEdges - edges.size() << " new edges!" << endl;
        boost::unordered_map< int, vector<int> > edges2;
        for (int e = 0; e < newEdges; e++) {
            int from, to;
            igraph_edge(&cg, e, &from, &to);
            edges2[from].push_back(to);
            edges2[to].push_back(from);
        }

        igraph_destroy(&cg);

        vector<int> ordering;
        cerr << "lexBfs..";
        lexBfs(maxVar+1, edges2, ordering);
        cerr << "done" << endl;

        reverse(ordering.begin(), ordering.end());


        cerr << "maximalCliques.."<< endl;
        maximalCliques(maxVar+1, edges2, ordering, cliques);
        cerr << "maximalCliques done" << endl;
        for (size_t i = 0; i < cliques.size(); i++) {
            // TODO: find all xor-clauses for each node 
            // of the tree decomposition 
        }

        if ((ret = igraph_empty(&cg, cliques.size(), false)) != 0) {
            cerr << "igraph_empty : " << ret << endl;
            exit(-1);
        }

        vector<int> weightsVec;
        vector< vector<int > > varsInCliques;
        vector< vector<int > > cliqueNeighbors;
        boost::unordered_map<pair<int, int>, int> weightMap;

        vector<int> edgesVec;
        map<int, int> cliqueId;

        cerr << cliques.size() << " cliques" << endl;
        for (size_t i = 0; i < cliques.size(); i++) {

            cliqueId[i] = nextCliqueId++;

#ifdef DEBUG
            cerr << "DOT: c" << cliqueId[i] << " [ label=\"" ;

            for (set<int>::iterator c = cliques[i].begin();
                    c != cliques[i].end(); c++) {
                cerr << " " << invIdMap[*c];   
            }
            cerr 

                << "\" ];" << endl;
#endif

            if (cliques[i].size() == 1)
                continue;
            for (size_t i2 = i+1; i2 < cliques.size(); i2++) {

                size_t w = set_intersection_size(cliques[i].begin(),
                        cliques[i].end(),
                        cliques[i2].begin(), cliques[i2].end());
                if (w > 0) {
                    weightMap[make_pair(i,i2)] = w;
                    weightsVec.push_back(-w);
                    edgesVec.push_back(i);
                    edgesVec.push_back(i2);
                }
            }
        }
        igraph_vector_init(&edges_v, edgesVec.size());
        for (size_t i = 0; i < edgesVec.size(); i++) {
            igraph_vector_set(&edges_v, i, edgesVec[i]);
        }
        igraph_add_edges(&cg, &edges_v, NULL);
        igraph_vector_destroy(&edges_v);
        edgesVec.clear();



        igraph_vector_t weights;
        igraph_vector_init(&weights, weightsVec.size());
        for (size_t i = 0; i < weightsVec.size(); i++) {
            igraph_vector_set(&weights, i, weightsVec[i]);
        }
        weightsVec.clear();

        igraph_t mst;
        if ((ret = igraph_minimum_spanning_tree_prim(&cg, &mst, &weights)) != 0)   {
            cerr << "igraph_minimum_spanning_tree_prim : " << ret << endl;
            exit(-1);
        }
        igraph_destroy(&cg);
#ifdef DEBUG
        for (int e = 0; e < igraph_ecount(&mst); e++) {
            int from, to;
            igraph_edge(&mst, e, &from, &to);
            cerr << "DOT: c" <<  cliqueId[from] << " -> c" <<  cliqueId[to] << " [ arrowhead=none label="
                "\"" << weightMap[make_pair(from, to)] << "\" ];" << endl;
        }
#endif

        for (int e = 0; e < igraph_ecount(&mst); e++) {
            int from, to;
            igraph_edge(&mst, e, &from, &to);
            mstEdges.push_back(make_pair(from, to));
            neighbors[from].push_back(to);
            neighbors[to].push_back(from);
        }
    }
    int findLeaf() {
        for (map<int, vector<int> >::iterator i = neighbors.begin();
                i != neighbors.end(); i++) {
            if (i->second.size() == 1)
                return i->first;
        }
        cerr << "Did not find a vertex with degree 1!" << endl;
        return -1;
    }
    public:
    struct Visitor {
        virtual ~Visitor() {}
        virtual void operator()(const set<int>& clauses,
                        const set<int>& vars,
                        const vector<int>& ivars) =0;
    };
    pair<int, int> dimensions() const {
        return make_pair(maxVar, clauses.size());
    }
 

    private:
    public:
    TreeDecomposition(const vector< vector<int> >& clauses_,
                      const vector<int>& clauseIds_) 
        : clauses(clauses_), clauseIds(clauseIds_) {
            for (size_t i = 0; i < clauseIds.size(); i++) {
                D("clauseIdMap[" << clauseIds[i] << "] = " << i << endl);
                clauseIdMap[clauseIds[i]] = i;
                D("clauseInvIdMap[" << i << "] = " << clauseIds[i] << endl);
                clauseInvIdMap[i] = clauseIds[i];
            }

            primalGraph();
            makeTreeDecomposition();      


        }


   void candidates(set< vector<int> >& candidates) {
       for (size_t i = 0; i < mstEdges.size(); i++) {
           const pair<int, int>& e = mstEdges[i];
           int c1 = e.first, c2 = e.second;
           vector<int> ivars;
           set_intersection(cliques[c1].begin(), cliques[c1].end(),
                   cliques[c2].begin(), cliques[c2].end(),
                   back_inserter(ivars));
           for (size_t i2 = 0; i2 < ivars.size(); i2++) {
               ivars[i2] = invIdMap[ivars[i2]];
           }
           if (ivars.size() >= 2 && ivars.size() <= 8)
               candidates.insert(ivars);

       }
   }
   long long getBestCut(set<vector<int> >& candidates,
                        set<int>& restricted,
                        set<int>& oldIvars,
                        vector< vector<int> > oldIvarSets,
                        vector<int>& bestIvars,
                        vector<vector<int> >& bestClauses) {


        long long orig = getVarNum() * getClauseNum();
        long long bestSaving = -1; 
        bestIvars.clear();
        bestClauses.clear();
        for (set<vector<int> >::const_iterator c = candidates.begin();
                c != candidates.end();) {


            const vector<int>& ivars = *c;
#ifdef DEBUG
            cerr << "Test-cutting with";
            for (size_t i = 0; i < ivars.size(); i++) {
                cerr << " " << ivars[i];
            }
            cerr << endl;
#endif

            bool isOldIvar = false;
            for (size_t i = 0; i < ivars.size(); i++) {
                if (oldIvars.find(ivars[i]) != oldIvars.end()) {
                    isOldIvar = true;
                    D(ivars[i] << " is already used" << endl);
                    break;
                }
                if (restricted.find(ivars[i]) != restricted.end()) {
                    isOldIvar = true;
                    D(ivars[i] << " is restricted" << endl);
                    break;
                }

            }

            if (isOldIvar) {
                c++;
                continue;
            }
            vector< pair<int, int> > cEdges;
            for (size_t i = 0; i < clauses.size(); i++) {
                vector<int>&c = clauses[i];

                cEdges.push_back(make_pair(i,i));
                for (size_t i2 = 0; i2 < c.size(); i2++) {
                    int v = abs(c[i2]);
                    bool isIvar = false;
                    if (oldIvars.find(v) != oldIvars.end()) {
                        isIvar = true;
                    }
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
#ifdef DEBUG
            vector<set<int> > varGroups;
#endif
            vector< vector<int> > allIvarSets = oldIvarSets;
            allIvarSets.push_back(ivars);
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

                cerr << "ClauseGroup " << i->first << " " << vars.size() << "x" << cg.size();
                int tw = vars.size();
                int th = cg.size();
                for (size_t i2 = 0; i2 < allIvarSets.size(); i2++) {
                    vector<int>& ivarSet = allIvarSets[i2];
                    bool found = false;
                    for (size_t i3 = 0; i3 < ivarSet.size(); i3++) {
                        if (vars.find(ivarSet[i3]) != vars.end()) {
                            found = true;
                            break;
                        }
                    }
                    if (!found)
                        continue;

                    int w = ivarSet.size();
                    int extraVars = pow((double) 2, (double) w) - (w + 1);
                    cerr << " + " << extraVars << "x" << extraVars;
                    tw += extraVars;
                    th += extraVars;
                }

                cerr << endl;
                decomposedSize += tw * th;
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
                        if (oldIvars.find(vint[i3]) != oldIvars.end()) {
                            found = true;
                        } else {
                            for (size_t i4 = 0; i4 < ivars.size(); i4++) {
                                if (ivars[i4] == vint[i3]) {
                                    found = true;
                                    break;
                                }
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
            cerr << " would save " << orig - decomposedSize << " elements" <<  endl;
            
            
            long long saving = orig - decomposedSize;
            if (saving > minSaving && saving > bestSaving) {
                bestSaving = saving;

                bestIvars = ivars;
                bestClauses.clear();
                for (map<int, vector<int> >::iterator i = clauseGroups.begin();
                        i != clauseGroups.end(); i++) {
                    bestClauses.push_back(i->second);
                }
                for (size_t i = 0; i < bestClauses.size(); i++) {
                    vector<int>& bc = bestClauses[i];
                    for (size_t i2 = 0; i2 < bc.size(); i2++) {
//                        cerr << "best clause from " << bc[i2];
                        bc[i2] = clauseInvIdMap[bc[i2]];
//                        cerr << " to " << bc[i2] << endl;
                    }
                }
            }
            if (orig-decomposedSize < 0) {
                set<vector<int> >::iterator next = c;
                next++;
                candidates.erase(c);
                c = next;
                cerr << "Not considering anymore" << endl;
            } else
                c++;

        }
        return bestSaving;

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
struct DecomposeVisitor : public TreeDecomposition::Visitor {

    TreeDecomposition& tree;
    pair<int, int> dim;
    vector<int> bestIvars;
    long long bestSize;
    set<int> bestClauses;
    DecomposeVisitor(TreeDecomposition& tree_) 
        : tree(tree_), dim(tree.dimensions()), bestSize(-1) {}

    virtual void operator()(const set<int>& clauses,
                        const set<int>& vars,
                        const vector<int>& ivars) {
#ifdef DEBUG
        cerr << "Visitor clauses:";
        for (set<int>::const_iterator ci = clauses.begin(); ci != clauses.end();
                ci++) {
            cerr << " " << *ci;
        }
        cerr << endl;
        cerr << "Visitor vars:";
        for (set<int>::const_iterator vi = vars.begin(); vi != vars.end();
                vi++) {
            cerr << " " << *vi;
        }
        cerr << endl;
#endif
        cerr << "Visitor ivars:";
        for (size_t i = 0; i < ivars.size(); i++) {
            cerr << " " << ivars[i];
        }
        cerr << endl;

        set<int> seenC = clauses;
        for (size_t i = 0; i < ivars.size(); i++) {
            vector<int> cids;
            tree.getClauses(ivars[i], cids);

            for (size_t i2 = 0; i2 < cids.size(); i2++) {
                vector<int> clause;

                tree.getClause(cids[i2], clause);
                for (size_t i3 = 0; i3 < clause.size(); i3++) {
                    if (vars.find(clause[i3]) == vars.end()) {
//                        D("not seen var " << clause[i3] << " in seen clause " << cids[i2] << endl);
                        seenC.erase(cids[i2]);
                        break;
                    }
                }
            }
        }
        int w = ivars.size();
        int extraVars = pow((double) 2, (double) w) - (w + 1);
        pair<int, int> dim1 = make_pair(vars.size(), seenC.size()),
                       dim2 = make_pair(tree.getVarNum() - vars.size() +
                                        ivars.size(), tree.getClauseNum()
                                                       - seenC.size());


        cerr << "Cutting here would give :" << endl;
        cerr << "- dim[0] : " << dim1.first << " x " << dim1.second << " + " 
            << extraVars << "x" << extraVars << endl;
        cerr << "- dim[1] : " << dim2.first
                              << " x " << dim2.second
                              << " + " << extraVars << "x" << extraVars << endl;
        long long orig = tree.getVarNum() * tree.getClauseNum();
        long long decomposed = (dim1.first + extraVars) * (dim1.second + extraVars)
            + (dim2.first + extraVars) * (dim2.second + extraVars);

        if (decomposed < orig && (bestSize == -1 || decomposed < bestSize)
                && orig - decomposed >= minSaving) {

            bestSize = decomposed;
            bestIvars.clear();
            copy(ivars.begin(), ivars.end(), back_inserter(bestIvars));
            bestClauses = seenC;
        }
            
    
    };


};

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
               const vector<int> & clauseIds) {
    TreeDecomposition tree(clauses, clauseIds);
    set<vector<int> > candidates;
    tree.candidates(candidates);
    vector<int> bestIvars;

    vector< vector<int> > clauseGroups;
    vector< vector<int> > bestClauseGroups;
    set<int> oldIvars;
    set<int> restricted;
    vector< vector<int> > ivarSets;
    long long prevBestSaving = -1;

    static int cycleComponent = 1;
    while(true) {
        cerr << "Candidate cuts remaining: " << candidates.size() << endl;

        long long bestSaving = tree.getBestCut(candidates, restricted, oldIvars,
                ivarSets, bestIvars, clauseGroups);

        
        if (bestSaving != -1) {
            if (prevBestSaving != -1 && prevBestSaving > bestSaving) 
               break; 
            prevBestSaving = bestSaving;
            for (size_t i = 0; i < bestIvars.size(); i++) {

                vector<int> cIds;
                tree.getClauses(bestIvars[i], cIds);

                oldIvars.insert(bestIvars[i]);
                for (size_t i2 = 0; i2 < cIds.size(); i2++) {
                    vector<int> c;
                    tree.getClause(cIds[i2], c);
                    for (size_t i3 = 0; i3 < c.size(); i3++) {
                        restricted.insert(abs(c[i3]));
                    }
                }
            }

            ivarSets.push_back(bestIvars);
            bestClauseGroups = clauseGroups;

            long long orig = tree.getVarNum() * tree.getClauseNum();
            cerr << "Best cut :";
            for (size_t i = 0; i < bestIvars.size(); i++) {
                cerr << " "<< bestIvars[i];
            }
            cerr << endl;

            cerr << "Reducing size by " << bestSaving << " from " << orig << " (" << bestSaving / float(orig) * 100.0 << "%)" << endl;


        } else
            break;
    }
    if (ivarSets.empty() == false) {
        cerr << "Found " << ivarSets.size() << " cut sets" << endl;
        vector< vector<vector<int> > > extraRowSets;
        extraRowSets.resize(ivarSets.size());
        for (size_t i = 0; i < ivarSets.size(); i++) {
            getExtraRows(ivarSets[i], extraRowSets[i]);
        }

        clauseGroups = bestClauseGroups;

        for (size_t cg = 0; cg < clauseGroups.size(); cg++) {
            vector<int>& bestClauses = clauseGroups[cg];
            cout << "c xor-cycle-component " << cycleComponent++ << endl;
            set<int> seenVars;

            for (vector<int>::iterator i = bestClauses.begin(); 
                    i != bestClauses.end(); i++) {
                vector<int> clause;

                tree.getClause(*i, clause);
                for (size_t i2 = 0; i2 < clause.size(); i2++) {
                    seenVars.insert(abs(clause[i2]));
                }
                printClause(clause);
            }
            for (size_t i = 0; i < ivarSets.size(); i++) {
                bool found = false;
                for (size_t i2 = 0; i2 < ivarSets[i].size(); i2++) {
                    if (seenVars.find(ivarSets[i][i2]) != seenVars.end()) {
                        found = true;
                        break;
                    }
                }
                if (found) {
                    cout << "c interface";
                    for (size_t i2 = 0; i2 < ivarSets[i].size(); i2++) {
                        cout << " " << ivarSets[i][i2];
                    }
                    cout << endl;
                    for (size_t i2 = 0; i2 < extraRowSets[i].size(); i2++) {
                        printClause(extraRowSets[i][i2]);
                    }
                }
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

    for (size_t i = 0; i < clauses.size(); i++) {
        clauseComponents[ccomponent[i]].push_back(clauses[i]);
        clauseId[ccomponent[i]].push_back(i);
    }
    

    for (map<int, vector< vector<int> > >::const_iterator cci = 
            clauseComponents.begin(); cci != clauseComponents.end(); cci++) {

        cerr << "Component[" << cci->first << "] : " << 
            cci->second.size() << " clauses"
            << endl;
        decompose(cci->second, clauseId[cci->first]);

    }    
    gettimeofday(&tv2, NULL);
    double msecs = (tv2.tv_sec - tv1.tv_sec) *1000.0 
                  + (tv2.tv_usec / 1000.0 - tv1.tv_usec / 1000.0);
    cerr << "xcnf-decompose took " <<  msecs << " ms" << endl;
    D("DOT: }" << endl);       
    return 0;
}

