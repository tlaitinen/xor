#ifndef _cluster_hpp_
#define _cluster_hpp_
#include <vector>
class Cluster {
    struct Link {
        int node;
        int deg;
        Link(int n, int d) 
            : node(n), deg(d) {}
    };
    struct Node {
        std::vector<Link> links;        
        int cluster;
        int influence;
    };
    std::vector<Node> nodes;

public:
    Cluster(int nodes);
    void incDeg(int n1, int n2);

    void cluster(std::vector< std::vector<int> >& result, bool doClustering);
};
#endif
