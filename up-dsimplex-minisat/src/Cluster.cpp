#include "Cluster.hpp"
#include <cstdlib>
#include <set>
#include <cstdio>
#include <iostream>
#include <map>
#include <boost/graph/connected_components.hpp>
#include <boost/graph/adjacency_list.hpp>

using namespace std;
Cluster::Cluster(int n) {
    nodes.resize(n);
    for (size_t i = 0; i < nodes.size(); i++) {
        nodes[i].cluster = i;
    }

}
void Cluster::incDeg(int n1, int n2) {
//    cout << "inc deg " << n1 << " " << n2 << endl;
    for (size_t i = 0; i < nodes[n1].links.size(); i++) {
        Link& l = nodes[n1].links[i];
        if (l.node == n2) {
            l.deg++;
  //          cout << "l.deg " << l.deg << endl;
            for (size_t i2 = 0; i2 < nodes[n2].links.size(); i2++) {
                Link& l2 = nodes[n2].links[i2];
                if (l2.node == n1) {
                    l2.deg++;
                }
            }
            return;

        }
    }
    nodes[n1].links.push_back(Link(n2,1));
    nodes[n2].links.push_back(Link(n1,1));

}

void Cluster::cluster(vector< vector<int> >& result, bool doClustering) {

    if (doClustering) {
        vector<int> check;
        int stuck =0 ;
        set<int> clusters;
        int changes = 1;
        while (stuck < 100 && changes > 0) {
            changes = 0;

            for (size_t i = 0; i < nodes.size(); i++) {
                check.push_back(i);
                clusters.insert(nodes[i].cluster);

            }
            size_t prevSize = clusters.size();
            while (!check.empty()) {
                int idx = rand() % check.size();
                int p = check[idx];
                check[idx] = check.back();
                check.pop_back();
                Node& n = nodes[p];
                for (size_t i = 0; i < n.links.size(); i++) {
                    int cid = nodes[n.links[i].node].cluster;
                    nodes[cid].influence = 0;
                }
                int maxInfluence = 0;
                for (size_t i = 0; i < n.links.size(); i++) {
                    Node& n2 = nodes[n.links[i].node];
                    int cid = n2.cluster;
                    nodes[cid].influence += n.links[i].deg;
                    if (nodes[cid].influence > maxInfluence) {
                        maxInfluence = nodes[cid].influence;
                    }
                }
                vector<int> possible;
                for (size_t i = 0; i < n.links.size(); i++) {
                    int cid = nodes[n.links[i].node].cluster;
                    if (nodes[cid].influence == maxInfluence) 
                        possible.push_back(cid);
                }
                int prev = n.cluster;
                if (possible.size() == 1) {
                    n.cluster = possible.front();
                } else if (possible.size() > 0) {
                    n.cluster = possible[rand()%possible.size()];                
                }
                if (prev != n.cluster)
                    changes++;

            }
            cout << "Changes " << changes << endl;
            clusters.clear();
            for (size_t i = 0; i < nodes.size(); i++) {
                clusters.insert(nodes[i].cluster);
            }
            if (clusters.size() == prevSize)
                stuck++;
        }
        cout << clusters.size() << " clusters" << endl;
        if (stuck == 100)
            cout << "got stuck" << endl;
        result.resize(clusters.size());
        map<int, int> clusterDest;
        int dst = 0;
        for (set<int>::iterator i = clusters.begin(); i != clusters.end(); i++)
            clusterDest[*i] = dst++;
        for (size_t i = 0; i < nodes.size(); i++) {
            result[clusterDest[nodes[i].cluster]].push_back(i);
        }
    } else {
/*        result.resize(1);
        for (size_t i = 0; i < nodes.size(); i++) {
            result[0].push_back(i);
        }*/


        using namespace boost;

        typedef adjacency_list <vecS, vecS, undirectedS> Graph;
        Graph g(nodes.size());

        for (size_t i = 0; i < nodes.size(); i++) {
            Node& n = nodes[i];
            for (size_t i2 = 0; i2 < n.links.size(); i2++) {
                if (i < n.links[i2].node)
                    add_edge(i, n.links[i2].node, g);
            }
        }
        std::vector<int> component(num_vertices(g));
        int num = connected_components(g, &component[0]);

        cerr << num << " xor-clusters" << endl;
//        vector< vector<int> > components;
        result.resize(num);
        for (std::vector<int>::size_type i = 0;
                 i != component.size(); ++i) {
            result[component[i]].push_back(i);
        }
    }
    /*
    FILE* f = fopen("cluster.dot", "w");
    fprintf(f, "digraph d {\n");
    for (size_t i = 0; i < nodes.size(); i++) {
        fprintf(f, "n%d [ label = \"%d\" ];\n", i, nodes[i].cluster);
        for (size_t j = 0; j < nodes[i].links.size(); j++) {
            int dst = nodes[i].links[j].node;
            if (i < dst)
                fprintf(f, "n%d -> n%d [ arrowhead=none label=\"%d\" ];\n",
                        i, dst, nodes[i].links[j].deg);
        }

    }
    fprintf(f, "}\n");
    fclose(f);
*/
}
