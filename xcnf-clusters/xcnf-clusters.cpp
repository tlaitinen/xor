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
#include <iterator>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <boost/tokenizer.hpp>
using namespace std;
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/connected_components.hpp>

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

    for (size_t i = 0; i < clauses.size(); i++) {
        int nId = maxVar  + i;
        vector<int>& c = clauses[i];
        for (size_t j = 0; j < c.size(); j++) {
            edges_.push_back(make_pair(nId, abs(c[j])-1));
        }
    }  


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


int main() {
    vector< vector<int> > clauses;
    vector< pair<int, int> > edges_;
    int maxVar = readClauses(clauses, edges_);
    map<int, int> idMap;
    compressEdges(edges_, idMap);
    vector<int> component;

    cout << getConnectedComponents(maxVar, edges_, component) << " components "
       << clauses.size() << " xor-clauses" << endl;
    return 0;
}

