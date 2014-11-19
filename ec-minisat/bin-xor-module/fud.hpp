#ifndef _fud_hpp_
#define _fud_hpp_
#include <vector>
#include <utility>
#include <cstdio>
#include <iostream>
#include <cassert>
#include <limits>
#include <map>
#include "xorsat.hpp"
#include "timestamp.hpp"
#include "util.hpp"
#include "erg.hpp"
#include "Settings.hpp"
// data structure for tracking equivalence classes of variables
// Fud = find-union-deunion
namespace bx {
class Fud {

    

    // an edge in the find-union forest
    struct Link {
        // index number of the parent node
        int node;

        // timestamp when the link was made
        int timestamp;

        // pointer to the corresponding union operation's timestamp
        int u;

        // parity of the link
        int parity;

        Link() : timestamp(0) {}
        Link(int n, int ts, int u_, int e)
            : node(n), timestamp(ts), u(u_), parity(e) {} 
    };

    // size of the subree
    struct Size {
        // number of nodes in the subtree
        int size;

        // timestamp when the size was recorded
        int timestamp;

        // pointer to the corresponding union operation's timestamp
        int u;
        
        Size() : timestamp(0) {}
        Size(int s, int ts, int u_) 
            : size(s), timestamp(ts), u(u_) {}
    };

    // node in the find-union forest
    struct Node {  
        // stack of links to parent nodes (grows due to path compression)
        std::vector<Link> parents;

        // stack of sizes of subtree (grows due to multiple union operations)
        std::vector<Size> size;
        Node() {}


     };

    // returns the current size of the subtree,
    // may remove invalid size records
    int getNodeSize(Node& n) {
        while (!n.size.empty()) {
            Size& s = n.size.back();
            if (unions[s.u] != s.timestamp) {
                D(dbg::fud,"popping stale size record");
                n.size.pop_back();
            } else {
                return s.size;
            }
        }
        // if there are no size records, then
        // the size of the subtree is 1
        return 1;
    }


    // nodes of the find-union forest
    std::vector<Node> nodes;

    // timestamps of union operations
    std::vector<int> unions;

    // current timestamp
    int timestamp;

    // number of union operations used in 'unions'
    int numUnions;

public:

    Erg erg;
    Fud(const Settings& settings_) : 
        timestamp(0),
        numUnions(0), erg(settings_) {}

    // result of the find-operation    
    struct Result {
        // root variable node
        int var;

        // parity w.r.t the root variable node
        int parity;

        // size of the subtree (equivalence class)
        int size;

        Result() {}

        Result(int v, int p, int s)
            : var(v), parity(p), size(s) {}             
    };


    // allocates memory for the nodes and
    // the maximum number of union-operations
    void setup(size_t vars) {
        // variables + top
        nodes.resize(vars);

        // not more than (vars + 1) links needed
        unions.resize(vars);

        //erg.setup(vars);
    }


    

    // joins the equivalence classes of 'v1' and 'v2'
    // with parity 'parity',
    // if 'parity' == 1, then 'v1' != 'v2',
    // if 'parity' == 0, then 'v1' == 'v2'.
    void union_(int v1, int v2, int parity, Lit reason);
        
    // cancels a number of 'union_' operations
    // so that the remaining number of unions is 'prevUnions'
    void deunion(int prevUnions);

    // returns the number of used union-timestamps (same as calls to 'union_')
    int unionCount() const {
//        assert(numUnions == erg.getNumLinks());
        return numUnions;
    }

    // returns the root of the node 'v', the size of the subtree (equivalence
    // class), and the parity between the root variable and 'v',
    // does path compression (a -> b and b -> c then a new link a -> c is made)
    void find(int v, Result& r )
    {
        assert(v >= 0 && v < nodes.size());
        // 'parity' holds the sum of the parities of the traversed edges 
        // from the node 'v' towards the root 
        int parity = 0;

        // node index of the node preceding the node 'v' 
        // (not known in the beginning)
        int prev1 = -1;

        // node index of the node preceding the node 'prev1'
        int prev2 = -1;

        // 'parity1' holds the previous value of 'parity' 
        // (the sum of the parities of the edges from the starting node 'v'
        // to the node 'prev1')
        int parity1 = 0;

        // 'parity2' holds the previous value of 'parity1' 
        // (the sum of the parities of the edges from the starting node 'v'
        // to the node 'prev2')
        int parity2 = 0;

        while (1) {
            D(dbg::fud,"@node " << v );
            Node& n = nodes[v];

            // remove dead links
            while (!n.parents.empty()) {
                Link& l = n.parents.back();
                // a link is considered dead if the corresponding
                // union timestamp differs from the timestamp
                // stored in the link
                if (unions[l.u] != l.timestamp) {
                    D(dbg::fud,"link " << l.timestamp << " dead" );
                    n.parents.pop_back();
                }
                else {
                    D(dbg::fud,"traversing live link"
                            << v << (l.parity % 2 == 0 ? " ==> " : " !=> ")
                            << l.node );
                    // rotate preceding node indices and parities
                    prev2 = prev1;
                    parity2 = parity1;
                    prev1 = v;
                    parity1 = l.parity;
                    v = l.node; 

                    // sum the parity of the traversed edge
                    parity += l.parity;

                    // if there is a node 'prev2' s.t. 'prev2' -> 'prev1' and
                    // 'prev1' -> 'v', then we make a new link
                    // 'prev2' -> 'v' (with the correct parity).
                    if (prev2 != -1) {
                        Node& n2 = nodes[prev2];
                        n2.parents.push_back(Link(v, unions[l.u], l.u, 
                                    (parity1 + parity2) % 2));
                        D(dbg::fud,"splitting path.  "
                                << prev2
                                << (parity2%2 ==0 ? "==> " : "!=> ")
                                << prev1 
                                << (parity1%2 ==0 ? "==> " : "!=> ")
                                << v << " ~~~> "
                                << prev2 
                                << ((parity1 + parity2) % 2 == 0 ? "==> " : "!=> ")
                                << v
                                );
                    }
                    break;
                }
            }
            // if there are no parents then we've reached the root
            if (n.parents.empty()) {
                D(dbg::fud,"found root " << v << " parity " << parity );
                // found the root
                r.var = v;
                r.parity = parity & 1;
                r.size = getNodeSize(nodes[v]);
                return;
            } 
        }
    }

    void explain(std::vector<Lit>& exp, int v1, int v2, long long & evenElim) {
       erg.explain(exp, v1, v2, evenElim);
    }


    // stores a graphviz graph of fud-forest to the file 'path'
    void toGraphviz(const std::string& path);


    // returns a string representation of the fud-forest
    std::string toString();

    void checkTimestamps();


};
}
#endif
