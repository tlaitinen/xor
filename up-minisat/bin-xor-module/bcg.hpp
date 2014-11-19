#ifndef _bcg_hpp_
#define _bcg_hpp_
#include <vector>
#include <deque>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <utility>

//#define DEBUG
#include <limits>
#include <map>
#include <set>
#include "xorsat.hpp"
#include "timestamp.hpp"
#include "util.hpp"
namespace bx {

// data structure for binary constraint graph
class Bcg {
public:

    typedef bx::Lit Lit;

    // data structure for one edge in the binary constraint graph
    struct Edge {
        // the index number of the destination variable
        int dest;

        // 1=odd parity, 0=even parity
        int parity;

        // reason literal
        Lit reason;

        // timestamp when the edge was added
        int ts;

        int dl;


        Edge(int d, int p, Lit r, int ts_, int dl_) : dest(d), parity(p), reason(r), ts(ts_), dl(dl_) {
        }
    };

//    typedef std::vector<int> Values;
//    typedef std::vector<Edge> Edges;
    typedef std::vector<int> Values;
    typedef std::vector<Edge> Edges;


    // data structure for a variable (node) in the binary constraint graph
    struct Node {
        Edges edges;

        // timestamps for both parities
        int visited[2];

        int prev;
        int prevParity;
        Lit prevReason;


        Node() : prev(-1){
            visited[0] = visited[1] = 0;

        }
        
    };

    // data structure for a node in a breadth-first search
    struct BfsNode {
        // index number of the previous bfs-node
        int prev;

        // reason literal of the traversed edge
        Lit reason;

        // pointer to the variable (node)
        Node* node;


        // index of the node
        int nodeId;

        // parity w.r.t the start node of the search
        int parity;



        BfsNode();
        BfsNode(int prev_, Lit r_, Node* n_, int id_,  int p_)
            : prev(prev_), reason(r_), node(n_), nodeId(id_), parity(p_) {}
    };
private:
    // timestamp for breadth-first search traversal ( Node::visited )
    int timestamp;

    // nodes in the binary constraint graph
    //std::vector<Node> nodes;
    std::vector<Node> nodes;

    
    // an array of pointers to edge-stacks (Node::edges) for backtracking
    //std::vector<Edges*> btStack;
    std::vector<int> btStack;

    // increments the timestamp used in the bfs-search
    void incTimestamp() {
        timestamp++;

        if (timestamp == MAX_TIMESTAMP) {
            // if the timestamp reaches its maximum value,
            // we reset it back to 1 and clear all the
            // visited counters in the nodes to 0
            timestamp = 1;
            for (int i = 0; i < nodes.size(); i++) {
                nodes[i].visited[0] = nodes[i].visited[1] = 0;
            }
        }
    }

    void setRoute(int from, int to, int parity, Lit reason, bool enable);

    int insertEdgeToNode(int btPos, int x, int y, int p, Lit r, int ts, int dl);
    void check();
public:
    // initializes the breadth-first search timestamp to 0
    Bcg() : timestamp(0) {
    } 

    // must be called before other methods,
    // allocates memory for nodes in the binary constraint graph,
    // cannot be called after 'pushEdge' has been called
    
    void setup(size_t numVars) {
        nodes.resize(numVars);
        nodes[0].prev = 0;
    }

    /// adds an edge between two nodes 'x' and 'y' with parity 'p'.
    /// the edge is labeled with the reason literal 'r'
    /// and has the timestamp 'ts'
    void pushEdge(int x, int y, int p, Lit r, int ts, int dl);

    std::pair<int, int> getInfo(int x, int y, int maxTs) const;



    void insertEdge(int pos, int x, int y, int p, Lit r, int ts, int dl);
   
    // returns the numbers of edges added in the graph
    int edgeCount() const {
        return btStack.size();
    }




    // removes most recently added edges until the number of edges is
    // 'prevSize'
    void popEdges(int prevSize);
   

    // finds a path from the node 'x' to the node 'y' using only
    // edges whose timestamp is smaller or equal to 'maxTimestamp',
    // stores the reason literals found in the edges to 'reason',
    // if 'x' and 'y' are the same, then a path whose edge parities
    // sum to an odd number is sought,
    // if the path cannot be found, the 'reason' will be an empty set
    // Note: this method does not clear the reason set
    void explainPath(int x, int y, int maxTimestamp, 
                     std::vector<Lit>& reason,
                     std::vector<int>& path);
    void explainPathNoConflict(int x, int y, int maxTimestamp, 
                     std::vector<Lit>& reason,
                     std::vector<int>& path);

   
    void fastExplain(Lit p,// int maxLits,
                     std::vector<Lit>& reason,
                     std::vector<int>& path);





    // this method computes the subgraph that is reachable
    // from the node 'x' (not including the node 'x')
    // and also computes the parities of the variable nodes
    // w.r.t to the node 'x',
    // the first element of the pair is the node
    // and the second element is the parity
    // Note: 'sg' is not cleared
    void subgraph(int x, std::vector< std::pair<int, int> >& sg);
   
    void addTimestamps(TimestampRemapper& tsRemap) {
        for (size_t i = 0; i < nodes.size(); i++) {
            for (Edges::iterator e = nodes[i].edges.begin();
                    e != nodes[i].edges.end(); e++) {
                tsRemap.add(e->ts);
            }
        }
    }
    void remapTimestamps(TimestampRemapper& tsRemap) {
        for (size_t i = 0; i < nodes.size(); i++) {
            for (Edges::iterator e = nodes[i].edges.begin();
                    e != nodes[i].edges.end(); e++) {
                e->ts = tsRemap.remap(e->ts);
            }
        }
    }


    // returns a string representation of the graph
    std::string toString(); 

    // stores a graphviz-version of the graph to 'path',
    // highlights nodes 'x' and 'y',
    // shows only edges whose timestamp is smaller or equal to 'maxTimestamp'
    // if 'onlyVisited' is true, shows only edges and nodes
    // that were visited by the last 'explainPath' search
    void toGraphviz(const std::string& path, int x, int y, 
                    int maxTimestamp, 
                    bool onlyVisited,
                    const std::string& comment=""
                    );

    void checkTimestamps(int maxEdgeTimestamp);

};
}

#endif
