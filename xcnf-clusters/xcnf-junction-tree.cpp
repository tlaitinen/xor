

#include <assert.h>
#include <algorithm>
#include <boost/config.hpp>
#include <set>
#include <deque>
#include <map>
#include <vector>
#include <list>
#include <iterator>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <boost/tokenizer.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/unordered_map.hpp>
#include "igraph.h"
using namespace std;
void printClause(const vector<int>& c) {
    cout << "x";
    for (size_t i = 0; i < c.size(); i++) {
        cout << " " << c[i];
    }
    cout << " 0" << endl;
}
int readClauses(vector<vector<int> >& clauses,
                vector< pair<int, int> >& edges_) {
    string line;
    int maxVar = 0;
    vector< vector<int > > var2clauses;

    while (getline(cin, line)) {

        if (line.empty())
            continue;
        if (line[0] != 'x') {
            //cout << line << endl;
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
                if (abs(num) > maxVar)
                    maxVar = abs(num);
            }

        }
        if (line[0] == 'x')
            clauses.push_back(nums);
    }
    var2clauses.resize(maxVar + 1);

    for (size_t i = 0; i < clauses.size(); i++) {
        vector<int>& c = clauses[i];
        for (size_t j = 0; j < c.size(); j++) {
            var2clauses[abs(c[j])].push_back(i);
//            edges_.push_back(make_pair(nId, abs(c[j])));
        }
    } 
    set<pair<int, int > > added;
    for (size_t i = 0; i < clauses.size(); i++) {
        vector<int>& c = clauses[i];
        for (size_t j = 0; j < c.size(); j++) {
            for (size_t k = j+1; k < c.size(); k++) {
                int c1 = abs(c[j]), c2 = abs(c[k]);
                if (c1 > c2) 
                    swap(c1,c2);
                if (c1 != c2 && added.find(make_pair(c1,c2)) == added.end()) {
                    added.insert(make_pair(c1,c2));
                    edges_.push_back(make_pair(c1-1,c2-1));
                }
            }
        }
    }
 /*
    for (size_t i = 0; i < var2clauses.size(); i++) {
        vector<int>& c = var2clauses[i];
        for (size_t j = 0; j < c.size(); j++) {
            for (size_t k = j+1; k < c.size(); k++) {
                int c1 = c[j], c2 = c[k];
                if (c1 > c2) 
                    swap(c1,c2);
                if (c1 != c2 && added.find(make_pair(c1,c2)) == added.end()) {
                    added.insert(make_pair(c1,c2));
                    edges_.push_back(make_pair(c1,c2));
                }
            }
        }
    }
   */ 


    return maxVar;
}
int getConnectedComponents(int maxVar, 
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


struct NodeLabel {
    int node;
    int label;
    NodeLabel() : node(0), label(0) {}
    NodeLabel(int n, int l) : node(n), label(l) {}
};
struct Comparator {
    bool operator()(const NodeLabel& nl1, const NodeLabel& nl2) {
        return nl1.label > nl2.label;
    }
};
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
            if (numbered[w])
                continue;
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
int compressEdges(vector< pair<int, int> >& edges, map<int, int>& idMap) {
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
    return id;
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
int main(int argc, char** argv) {
    int onlyCliques = (argc > 2 && strcmp(argv[1], "--only-cliques") == 0) ? atoi(argv[2]) : 0;
    if (onlyCliques)
        cerr << "printing only cliques smaller than " << onlyCliques << " variables" << endl;

    vector< vector<int> > clauses;
    vector< pair<int, int > > edges;
    int maxVar = readClauses(clauses, edges);
    clauses.clear();
    vector<int> component;
    int nextCliqueId = 1;
   
     int components = getConnectedComponents(maxVar, edges, component);

    cout << "digraph d {" << endl;
    map<int, vector< pair<int, int > > > componentEdges;
    for (size_t i = 0; i < edges.size(); i++) {
        componentEdges[component[edges[i].first]].push_back(edges[i]);
    }
    
    for (int componentId = 0; componentId < components; componentId++) {
        if (componentEdges.find(componentId) == componentEdges.end())
            continue;
        cerr << "Component[" << componentId << "] : " << 
            componentEdges[componentId].size() << " edges"
            << endl;

        map<int, int> idMap;
        map<int, int> invIdMap;
        int maxVar = compressEdges(componentEdges[componentId], idMap);
        for (map<int, int>::const_iterator i = idMap.begin(); i != idMap.end(); i++) {
            invIdMap[i->second] = i->first;
        }
      //  int maxVar = 1000;
        const vector<pair<int, int> >& edges = componentEdges[componentId];
        igraph_t g;

        int ret = 0;
        if ((ret = igraph_empty(&g, maxVar /*clauses.size()*/, false)) != 0) {
            cerr << "igraph_empty : " << ret << endl;
            return -1;
        }
        igraph_vector_t edges_v;
        igraph_vector_init(&edges_v, edges.size() * 2) ; 
        for (size_t i = 0; i < edges.size(); i++) {
          
            assert(edges[i].first >=0 && edges[i].first < maxVar); //clauses.size());
            assert(edges[i].second >= 0 && edges[i].second < maxVar); //clauses.size());
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
            return -1;
        }
        if ((ret = igraph_destroy(&g)) != 0) {
            cerr << "igraph_destroy : " << ret << endl;
            return -1;
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
        lexBfs(maxVar, edges2, ordering);
        cerr << "done" << endl;

        reverse(ordering.begin(), ordering.end());

        vector< set<int> > cliques;

        cerr << "maximalCliques.."<< endl;
        maximalCliques(maxVar, edges2, ordering, cliques);
        cerr << "maximalCliques done" << endl;

        if ((ret = igraph_empty(&cg, cliques.size(), false)) != 0) {
            cerr << "igraph_empty : " << ret << endl;
            return -1;
        }

        vector<int> weightsVec;
        vector< vector<int > > varsInCliques;
        vector< vector<int > > cliqueNeighbors;
//        varsInCliques.resize(maxVar+1);
//        cliqueNeighbors.resize(cliques.size());
/*        for (size_t i = 0; i < cliques.size(); i++) {
            for (set<int>::iterator c = cliques[i].begin();
                    c != cliques[i].end(); c++) {
                varsInCliques[*c].push_back(i);
            }
        }
        for (size_t i = 0; i < varsInCliques.size(); i++) {
            vector<int>& cliqueIds = varsInCliques[i];
            for (size_t j = 0; j < cliqueIds.size(); j++) {
                for (size_t k = j+1; k < cliqueIds.size(); k++) {
                    int c1 = cliqueIds[j], c2 = cliqueIds[k];
                    pair<int, int> cp = make_pair(c1,c2);
                    if (weightMap.find(cp) == weightMap.end()) {
                        cliqueNeighbors[c1].push_back(c2);
                    }

                    weightMap[cp]++;
                }
            }
        }
        cerr << "done" << endl;
*/

        boost::unordered_map<pair<int, int>, int> weightMap;

        vector<int> edgesVec;
        map<int, int> cliqueId;
           
        cerr << cliques.size() << " cliques" << endl;
        for (size_t i = 0; i < cliques.size(); i++) {

            if (onlyCliques && cliques[i].size() > onlyCliques)
                continue;
             cliqueId[i] = nextCliqueId++;
            cout << "c" << cliqueId[i] << " [ label=\"" ;

            // cout  << cliques[i].size();
            for (set<int>::iterator c = cliques[i].begin();
                    c != cliques[i].end(); c++) {
                cout << " " << invIdMap[*c] + 1;   
            }
            cout 

                << "\" ];" << endl;
            if (cliques[i].size() == 1 || onlyCliques)
                continue;
            for (size_t i2 = i+1; i2 < cliques.size(); i2++) {

            //for (size_t ji = 0; ji < cliqueNeighbors[i].size(); ji++) {
              //  int j = cliqueNeighbors[i][ji];
            //    weightsVec.push_back(-weightMap[make_pair(i,j)]);

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
        if (onlyCliques)
            continue;
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
        cliques.clear();

        igraph_t mst;
        if ((ret = igraph_minimum_spanning_tree_prim(&cg, &mst, &weights)) != 0)   {
            cerr << "igraph_minimum_spanning_tree_prim : " << ret << endl;
            return -1;
        }
        // cout << "}" << endl;
        igraph_destroy(&cg);
        int mstEdges = igraph_ecount(&mst);

        for (int e = 0; e < mstEdges; e++) {
            int from, to;
            igraph_edge(&mst, e, &from, &to);
            cout << "c" <<  cliqueId[from] << " -> c" <<  cliqueId[to] << " [ arrowhead=none label="
                "\"" << weightMap[make_pair(from, to)] << "\" ];" << endl;
        }
        //
        componentEdges.erase(componentId);
    }
    cout << "}" << endl;
    return 0;
}

