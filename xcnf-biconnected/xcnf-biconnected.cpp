//=======================================================================
// Copyright 2001 Jeremy G. Siek, Andrew Lumsdaine, Lie-Quan Lee, 
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//=======================================================================
#include <boost/config.hpp>
#include <vector>
#include <list>
#include <boost/graph/biconnected_components.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <iterator>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <boost/tokenizer.hpp>
using namespace std;
namespace boost {
  struct edge_component_t {
    enum  { num = 555 };
    typedef edge_property_tag kind;
  }
  edge_component;
}

void printClause(const vector<int>& c) {
    cout << "x";
    for (size_t i = 0; i < c.size(); i++) {
        cout << " " << c[i];
    }
    cout << " 0" << endl;
}
int readClauses(vector<vector<int> >& clauses,
                vector<pair<int, int> >& edges_) {
    string line;
    int maxVar = 0;
    while (getline(cin, line)) {

        if (line.empty())
            continue;
        if (line[0] != 'x') {
            cout << line << endl;
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

    for (size_t i = 0; i < clauses.size(); i++) {
        int nId = maxVar + 1 + i;
        vector<int>& c = clauses[i];
        for (size_t j = 0; j < c.size(); j++) {
            edges_.push_back(make_pair(nId, abs(c[j])));
        }
    }  


    return maxVar;
}
int main() {
    vector< vector<int> > clauses;
    vector< pair<int, int> > edges_;
    int maxVar = readClauses(clauses, edges_);

    using namespace boost;
    typedef adjacency_list < vecS, vecS, undirectedS,
            no_property, property < edge_component_t, std::size_t > >graph_t;
    typedef graph_traits < graph_t >::vertex_descriptor vertex_t;

    graph_t g(1 + maxVar + clauses.size());

    for (size_t i = 0; i < edges_.size(); i++) {
        add_edge(edges_[i].first, edges_[i].second, g);
    }

    property_map < graph_t, edge_component_t >::type
        component = get(edge_component, g);

    std::size_t num_comps = biconnected_components(g, component);
    std::cerr << "Found " << num_comps << " biconnected components.\n";

    std::vector<vertex_t> art_points;
    articulation_points(g, std::back_inserter(art_points));
    std::cerr << "Found " << art_points.size() << " articulation points.\n";

    vector< set<int> > ccomp;
    graph_traits < graph_t >::edge_iterator ei, ei_end;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        int c = component[*ei];
        if (ccomp.size() <= c)
            ccomp.resize(c+1);
        // source is always clause
        ccomp[c].insert(source(*ei, g));
//        cout << " edge " << source(*ei, g) << " " << target(*ei,g) << " in component" << c << endl;
    }

    for (std::size_t i = 0; i < art_points.size(); ++i) {
        int n = art_points[i];
        if (n <= maxVar)
            continue;

//        cerr << "checking clause articulation point c" << n - maxVar - 1 << endl;
        vector<int> sets;
        for (int c = 0; c < ccomp.size(); c++) {
            if (ccomp[c].find(n) != ccomp[c].end()) {
                sets.push_back(c);
//                cerr << " in component " << c << endl;
            }
        }

        for (size_t i2 = 1; i2 < sets.size(); i2 ++) {
            // articulation point present in two biconnected components
            // and is a clause => join components

            int s1 = sets[0];
            int s2 = sets[i2];
            if (s1 != s2) {

//                cerr << "Joining two biconnected components of sizes " << ccomp[s1].size() 
//                    << " and " << ccomp[s2].size() << " due to shared clause node" << endl;

                ccomp[s1].insert(ccomp[s2].begin(), ccomp[s2].end());
                ccomp[s2].clear();
            }
        }
    }


    int cmpntId = 1;
    size_t numPrinted = 0;
    for (size_t i = 0; i < ccomp.size(); i++) {
        set<int>& s = ccomp[i];

        size_t numClauses = 0;

        for (set<int>::iterator c = s.begin(); c != s.end(); c++) {
            if (*c > maxVar) {
                numClauses++;
                if (numClauses > 1)
                    break;
            }

        }

        if (numClauses <= 1)
            continue;

        cout << "c xor-cycle-component " << cmpntId++ << endl;
        for (set<int>::iterator c = s.begin(); c != s.end(); c++) {
            int id = *c;
            if (id > maxVar)  {
                int cId = id - maxVar - 1;
                printClause(clauses[cId]);
                numPrinted++;
            }
        }
        cerr << "xor-cycle-component of " << s.size() << " xor-clauses" << endl;
    }
    if (numPrinted < clauses.size()) {
        cout << "c xor-tree-like-component" << endl;
        numPrinted = 0;
        for (size_t i = 0; i < ccomp.size(); i++) {
            set<int>& s = ccomp[i];
            size_t numClauses = 0;

            for (set<int>::iterator c = s.begin(); c != s.end(); c++) {
//                cout << *c << endl;
                if (*c > maxVar) {
                    numClauses++;
                    if (numClauses > 1)
                        break;
                }
            }
            if (numClauses != 1)
                continue;
            int id = *s.begin();
            if (id > maxVar)  {
                int cId = id - maxVar - 1;
                printClause(clauses[cId]);
                numPrinted++;
            }
        }

        cerr << "xor-tree-like-component of " << numPrinted << " xor-clauses" << endl;

    }
    

    return 0;
}

