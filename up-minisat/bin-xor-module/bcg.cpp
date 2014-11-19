#include "bcg.hpp"
#include "util.hpp"
#include "xormodule.hpp"
using namespace std;
#include <set>
namespace bx {
    void Bcg::setRoute(int from, int to, int parity, Lit reason, bool enable) {
        Node& n = nodes[to];

        bool hasPrev = n.prev != -1;

        if (hasPrev == enable)
            return;

        if (enable) {
            n.prev = from;
            n.prevReason = reason;
            n.prevParity = parity;
        } else {
            n.prev = -1;
        }
        if (enable) {
            std::deque<int> bfs;
            bfs.push_back(to);
            while (!bfs.empty()) {
                int i = bfs.front();
                bfs.pop_front();
                Node& n = nodes[i];
                for (Edges::iterator e = n.edges.begin(); e != n.edges.end(); e++) {
                    if (nodes[e->dest].prev == -1) {
                        bfs.push_back(e->dest);
                        nodes[e->dest].prev = i;
                        nodes[e->dest].prevReason = e->reason;
                        nodes[e->dest].prevParity = e->parity;
                    }
                }

            }

        } else {

            for (Edges::iterator e = n.edges.begin(); e != n.edges.end(); e++) {

                if (nodes[e->dest].prev == to)
                    setRoute(to, e->dest, e->parity, e->reason, false);
            }
        }
    }
    std::pair<int, int> Bcg::getInfo(int x, int y, int maxTs) const {
        const Node& n = nodes[x];
        const Edges& edges = n.edges;
        for (int i = edges.size() - 1; i >= 0; i--) {
            const Edge& e = edges[i];
            if (e.ts > maxTs)
                continue;
            if (e.dest == y)
                return make_pair(e.ts, e.dl);
        }
        assert(false);
    }

     void Bcg::pushEdge(int x, int y, int p, Lit r, int ts, int dl) {
        // both nodes have an edge to the other node

        D(dbg::bcg, "adding edge " << nodes[x].edges.size() << " to node " << x << " btStack " << btStack.size());
        nodes[x].edges.push_back(Edge(y, p, r, ts, dl));

        D(dbg::bcg, "adding edge " << nodes[y].edges.size() << " to node " << y << " btStack " << btStack.size() + 1);
        nodes[y].edges.push_back(Edge(x, p, r, ts, dl));

        btStack.push_back(x);//.edges);
        btStack.push_back(y);//.edges);

        if (nodes[x].prev != -1)
            setRoute(x, y, p, r, true);
        if (nodes[y].prev != -1)
            setRoute(y, x, p, r, true);

    }

     int Bcg::insertEdgeToNode(int btPos, int x, int y, int p, Lit r, int ts, int dl) {
         int count= 0;

         for (int i = 0; i < btPos; i++)
             if (btStack[i] == x) {
                 D(dbg::bcg, "node[" << x << "].edge[" << count << "] (ts=" << 
                         nodes[count].edges[p].ts << ") = btStack[" << i << "]");
                 count++;
             }
         btStack.push_back(btStack.back());
         for (int i = btStack.size() - 1; i > btPos; i--)  {
             btStack[i] = btStack[i-1];
         }
         btStack[btPos] = x;

         Edges& edges = nodes[x].edges;
         edges.push_back(edges.back());
         for (int i = edges.size() - 1; i > count; i--) {
             edges[i] = edges[i-1];
         }
         edges[count] = Edge(y, p, r, ts, dl);

         return 0;


     }

     void Bcg::check() {
//#ifndef DEBUG
//         return;
//#endif
         set< pair<int, int> > rel;
         for (size_t i = 0; i < nodes.size(); i++) {
             Node&n = nodes[i];
             Edges& edges = n.edges;
             int prev = 0;
             for (size_t i2 = 0; i2 < edges.size(); i2++) {
                 Edge& e = edges[i2];
                 rel.insert(make_pair(i, e.dest));

                 if (prev > e.ts)
                     D(dbg::bcg, "node " << i << " edge " << i2 << " ts=" << e.ts);
//                assert(prev <= e.ts);
                 prev = e.ts;
             }
         }
         for (set< pair<int, int> >::iterator i = rel.begin();
                 i != rel.end(); i++) {
             int from = i->first, to = i->second;
             if (rel.find(make_pair(to, from)) == rel.end()) {
                 D(dbg::bcg, "missing link " << to << " -> " << from);
                 D(dbg::bcg, toString());

             }
             assert(rel.find(make_pair(to, from)) != rel.end());
         }
     }
     void Bcg::insertEdge(int pos, int x, int y, int p, Lit r, int ts, int dl) {

        int p1 = insertEdgeToNode(pos, x, y, p, r, ts, dl);
        D(dbg::bcg, "Insert edge position: " << p1);
        int p2 = insertEdgeToNode(pos, y, x, p, r, ts, dl);
        D(dbg::bcg, "Insert edge position: " << p2);
        if (nodes[x].prev != -1)
            setRoute(x, y, p, r, true);
        if (nodes[y].prev != -1)
            setRoute(y, x, p, r, true);
        check();

     }

 
    void Bcg::popEdges(int prevSize) {
        // pushEdge-operations are canceled in the reverse order
        while (btStack.size() > prevSize) {

            int nid = btStack.back();
            Node& n = nodes[nid];

            assert(n.edges.size() > 0);
            if (n.prev == n.edges.back().dest)
                setRoute(0, nid, 0, Lit(0, false), false);

            D(dbg::bcg, "popping edge " << n.edges.size() - 1 << " from node " << nid);            
            n.edges.pop_back();
            btStack.pop_back();
        }
    }
    void Bcg::explainPath(int x, int y, int maxTimestamp, 
                     std::vector<Lit>& reason,
                     std::vector<int>& path) {
        // TODO: meet-in-the-middle strategy for loop search


        // set the goal to point the node 'y'
        Node* goal = &nodes[y];

        // this double-ended queue holds bfs-nodes indices that 
        // need to be expanded
        std::deque<int> bfsOpen;

        // this array contains all bfs-nodes 
        std::vector<BfsNode> bfs;

        // add the initial bfs node starting from the node 'x'        
        bfs.push_back(BfsNode(0, Lit(0, false), &nodes[x], x, 0));

        // mark it as "open", that is, it needs to be expanded
        bfsOpen.push_back(0);

        // timestamp is incremented to recognize nodes 
        // that have been visited already
        incTimestamp();
        D(dbg::bcg, "explain " << x << " -> " << y << " maxTs=" << maxTimestamp);

        // the loop is executed while there are 
        // nodes that can be expanded,
        // but can also be stopped in case the goal node
        // is found
        while (!bfsOpen.empty()) {
            // pop a bfs-node index from the double-ended queue
            int current = bfsOpen.front();
            bfsOpen.pop_front();
            assert(current >= 0 && current < bfs.size());

            // access the bfs-node contents
            BfsNode bn = bfs[current];

            // 'n' is the variable (node) being visited
            Node* n = bn.node;

            // iterator through all the edges of the current nodes
            for (Edges::iterator e = n->edges.begin();
                    e != n->edges.end(); e++) {

                // we cannot traverse the edges whose timestamp is bigger
                // than 'maxTimestamp' so skip those
                if (e->ts > maxTimestamp)
                    continue;                               
                assert(e->dest >= 0 && e->dest < nodes.size());
                // 'next' is the variable (node) at the other end of the
                // current edge
                Node* next = &nodes[e->dest];

                // 'parity' is the parity w.r.t starting node (parity of the
                // sum of parities of traversed edges)
                int parity = (bn.parity + e->parity) & 1;

                // in case we are searching a path between two different nodes
                // 'x' and 'y', the parity of the resulting path does not
                // matter, but in case we are searching for a loop ('x' == 'y'),
                // we want to have an odd parity. it is possible to reach the same
                // node with two different parities, so each node maintains two 
                // visited-timestamps to keep track of two possible ways of
                // reaching a node 
                int slot = (x != y) ? 0 : parity;

                if (next->visited[parity] < timestamp) {
//                    D(dbg::bcg, "traversing edge " << nn << " -> " << e->dest << 
//                           " parity " << e->parity << " reason " << e->reason <<
//                           " timestamp " << e->ts );

                    // update the visited-timestamp of the node 
                    // (with the correct parity)
                    next->visited[parity] = timestamp;

                    // add a bfs-node and schedule it for expanding
                    bfsOpen.push_back(bfs.size());
                    bfs.push_back(BfsNode(current, e->reason, next, e->dest, parity));

                    // in case we've reached the goal and we are searching for
                    // a loop, we have to make sure that the sum of parities
                    // of the traversed edges is odd, 
                    // if we are searching a path between two distinct nodes,
                    // the parity of the path does not matter
                    if (y == e->dest && (parity & 1 == 1 || x != y)) {
                        // increment the timestamp so we can
                        // reuse the visited-timestamp of the nodes
                        // to track whether a reason literal is already
                        // in the result set or not                        
                        incTimestamp();
                        //path.clear();

                        // start with the last node (which was just added)
                        int pos = bfs.size() - 1;


                        // the node 'bfs[0]' is not processed because
                        // it does not have a reason literal
                        // (it was added artificially in the beginning)
                        while (pos > 0) {
                            BfsNode& bn = bfs[pos];
                            // use the visited timestamp of the variable (node)
                            // corresponding to the reason literal
                            Lit r = bn.reason;

                            if (nodes[r.get_var()].visited[0] < timestamp) {
                                // add the reason literal to the result set

                                if (r.get_var()) {


                                        reason.push_back(Lit(r.get_var(), !r.get_sign()));
                                        D(dbg::bcg,"bfs node id : " << bn.nodeId);
                                        if (bn.nodeId > 0)
                                            path.push_back(bn.nodeId);
                                        Lit l = reason.back();
                                        D(dbg::bcg,"adding literal " << (!l.get_sign() ? "-x" : "x") << l.get_var());
                                }


                                // mark the variable as present in the result set
                    //            nodes[r.get_var()].visited[0] = timestamp;
                            } 
                            // process the preceding node in the path
                            pos = bn.prev;
                        }
                        if (x != y) {
                            D(dbg::bcg,"bfs node id : " << bfs[0].nodeId);

                            path.push_back(bfs[0].nodeId);
                        }

                        assert(!reason.empty());
                        return;
                    }

                } 
            }
        }
    }
    void Bcg::explainPathNoConflict(int x, int y, int maxTimestamp, 
                     std::vector<Lit>& reason,
                     std::vector<int>& path) {
        // TODO: meet-in-the-middle strategy for loop search



        // this double-ended queue holds bfs-nodes indices that 
        // need to be expanded
        std::deque<int> bfsOpen;

        // this array contains all bfs-nodes 
        std::vector<BfsNode> bfs;

        // add the initial bfs node starting from the node 'x'        
        bfs.push_back(BfsNode(0, Lit(0, false), &nodes[x], x,  0));

        // mark it as "open", that is, it needs to be expanded
        bfsOpen.push_back(0);

        // timestamp is incremented to recognize nodes 
        // that have been visited already
        incTimestamp();
        D(dbg::bcg, "explain " << x << " -> " << y << " maxTs=" << maxTimestamp);

        // the loop is executed while there are 
        // nodes that can be expanded,
        // but can also be stopped in case the goal node
        // is found
        while (!bfsOpen.empty()) {
            // pop a bfs-node index from the double-ended queue
            int current = bfsOpen.front();
            bfsOpen.pop_front();
            assert(current >= 0 && current < bfs.size());

            // access the bfs-node contents
            BfsNode bn = bfs[current];

            // 'n' is the variable (node) being visited
            Node* n = bn.node;

            // iterator through all the edges of the current nodes
            for (Edges::iterator e = n->edges.begin();
                    e != n->edges.end(); e++) {

                // we cannot traverse the edges whose timestamp is bigger
                // than 'maxTimestamp' so skip those
                if (e->ts > maxTimestamp)
                    continue;                               
                assert(e->dest >= 0 && e->dest < nodes.size());
                // 'next' is the variable (node) at the other end of the
                // current edge
                Node* next = &nodes[e->dest];

                // 'parity' is the parity w.r.t starting node (parity of the
                // sum of parities of traversed edges)
                int parity = (bn.parity ^ e->parity) & 1;


                if (next->visited[0] < timestamp) {
                    // update the visited-timestamp of the node 
                    // (with the correct parity)
                    next->visited[0] = timestamp;

                    // add a bfs-node and schedule it for expanding
                    bfsOpen.push_back(bfs.size());
                    bfs.push_back(BfsNode(current, e->reason, next, e->dest, parity));

                    if (e->dest == y) {
                        // increment the timestamp so we can
                        // reuse the visited-timestamp of the nodes
                        // to track whether a reason literal is already
                        // in the result set or not                        
                        incTimestamp();
                        //path.clear();

                        // start with the last node (which was just added)
                        int pos = bfs.size() - 1;


                        // the node 'bfs[0]' is not processed because
                        // it does not have a reason literal
                        // (it was added artificially in the beginning)

                        while (pos > 0) {
                            BfsNode& bn = bfs[pos];
                            // use the visited timestamp of the variable (node)
                            // corresponding to the reason literal
                            Lit r = bn.reason;



                            if (nodes[r.get_var()].visited[0] < timestamp) {
                                // add the reason literal to the result set


                                if (r.get_var()) {


                                    reason.push_back(Lit(r.get_var(), !r.get_sign()));
                                    D(dbg::bcg,"bfs node id : " << bn.nodeId);
                                    if (bn.nodeId > 0)
                                        path.push_back(bn.nodeId);
                                    Lit l = reason.back();
                                    D(dbg::bcg,"adding literal " << (!l.get_sign() ? "-x" : "x") << l.get_var());

                                    // mark the variable as present in the result set
                                    //                                nodes[r.get_var()].visited[0] = timestamp;

                                }
                            } 
                            // process the preceding node in the path
                            pos = bn.prev;
                        }
                        if (x != y) {
                            D(dbg::bcg,"bfs node id : " << bfs[0].nodeId);

                            path.push_back(bfs[0].nodeId);
                        }

                        //assert(!reason.empty());
                        return;
                    }

                } 
            }
        }
        toGraphviz("bcg.dot", x,y,maxTimestamp,false);

        assert(false);

    }

    void Bcg::fastExplain(Lit p, //int maxLits,
                     std::vector<Lit>& reason,
                     std::vector<int>& path) {
//        int lits = maxLits - 1;
        int n = p.get_var();
        int parity = int(p.get_sign() == true);
//       path.clear();

        while (/*lits > 0 && */nodes[n].prev != 0) {

            path.push_back(n);
            Node& node = nodes[n];

            Lit& r = node.prevReason;

            if (r.get_var()) {
                D(dbg::bcg,"fastExplain adding literal " << (!r.get_sign() ? "-x" : "x") << r.get_var());

                reason.push_back(Lit(r.get_var(), !r.get_sign()));
            }
            n = node.prev;
            parity = (parity + node.prevParity) & 1;
//            lits--;
        }
        if (n != 0) 
            reason.push_back(Lit(n, parity==0));

    }
    void Bcg::subgraph(int x, std::vector< std::pair<int, int> >& sg) {
        // increment visited-timestamp
        incTimestamp();

        // indices of bfs-node that need to be expanded
        std::deque<int> bfsOpen;

        // all bfs-nodes
        std::vector<BfsNode> bfs;

        // starts computing the subgraph from the node 'x'
        bfs.push_back(BfsNode(0, Lit(0,false), &nodes[x], x, 0));
        bfsOpen.push_back(0);

        // the node 'x' is not included in the subgraph
        nodes[x].visited[0] = timestamp;

        // the loop continues until all reachable
        // nodes have been found
        while (!bfsOpen.empty()) {
            // pop an element from the "open" queue
            int current = bfsOpen.front();
            bfsOpen.pop_front();
            assert(current >= 0 && current < bfs.size());
            BfsNode bn = bfs[current];

            // 'n' is a pointer to the current node
            Node* n = bn.node;


            // iterate through the edges of the current node
            for (Edges::iterator e = n->edges.begin();
                    e != n->edges.end(); e++) {
                // 'next' is the pointer to the node at the
                // other end of the edge
                Node* next = &nodes[e->dest];

                // compute the parity w.r.t 'x'
                int parity = (bn.parity + e->parity) % 2;

                // if the node has not been visited yet,
                // add it to the result set,
                // and also schedule it for expanding
                if (next->visited[0] < timestamp) {
                    next->visited[0] = timestamp;

                        
                    sg.push_back(std::make_pair(e->dest, parity));
                    bfsOpen.push_back(bfs.size());
                    bfs.push_back(BfsNode(0, Lit(0, false), next, e->dest,  parity));
                }
            }
        }
    }

std::string Bcg::toString() {
    std::string res;
    for (int i = 0; i < nodes.size(); i++) {
        Node& n = nodes[i];

        for (size_t i2 = 0; i2 < n.edges.size(); i2++) {
            char buf[512];
            Edge& e = n.edges[i2];
            snprintf(buf, 512, "%d -> %d [ parity=%d reason=%s%d timestamp=%d ]\n",
                     i, e.dest, e.parity, e.reason.get_sign() ? "-" : "", e.reason.get_var(), e.ts);
            res += std::string(buf);
          

        }
    }
    return res;
}

void Bcg::toGraphviz(const std::string& path, int x, int y, int maxTimestamp, bool onlyVisited,
                     const std::string& comment) 
{
    FILE* f = fopen(path.c_str(), "w");
    fprintf(f, "digraph d {");
    for (int i = 0; i < nodes.size(); i++) {
        Node& n= nodes[i];
        if (onlyVisited && n.visited[0] < timestamp - 1
                && n.visited[1] < timestamp - 1)
            continue;
        fprintf(f, "n%d [label=\"%d\"];\n",
                  i,   i);
        for (Edges::iterator e = n.edges.begin(); e != n.edges.end(); e++) {
            if (i > e->dest || e->ts > maxTimestamp)
                continue;
            if (onlyVisited && nodes[e->dest].visited[0] < timestamp - 1
                            && nodes[e->dest].visited[1] < timestamp - 1)
                continue;



            const char* arrow = NULL;
            bool prev = false;
            int from = i;
            int to = e->dest;
            if (i == nodes[e->dest].prev) {
                from = e->dest;
                to = i;

                prev = true;
            } else if (n.prev == e->dest) {
                prev = true;

            }
            if (prev) {
                arrow =  (e->parity == 0) ? "normal" : "dot";
            } else
                arrow =  (e->parity == 0) ? "none" : "odot";


             fprintf(f, "n%d -> n%d [ label=\"%s%d (ts=%d)\" arrowhead=%s ];  \n",
                        from, to, (e->reason.get_sign()) ? "-" : "", e->reason.get_var(), e->ts, arrow);

/*
            fprintf(f, "n%d -> n%d [ label=\"%s%d (%d)\" arrowhead=%s ];  %d  \n",
                    i, e->dest, (e->reason.get_sign()) ? "-" : "", e->reason.get_var(), e->ts,
                    (e->parity == 0) ? "none" : "odot",n.prev);                */
        }
    }
    fprintf(f, "n%d [ style=filled fillcolor=blue ]; ", x);
    if (x != y) 
        fprintf(f, "n%d [ style=filled fillcolor=darkgreen ]; ", y);

    if (comment.empty() == false)
       fprintf(f, "comment [ label=\"%s\" shape=rectangle ];", comment.c_str());
    fprintf(f, "}");
    fclose(f);
//    char buf[80];
//    snprintf(buf, 80, "dot tmp.dot -Tpng > 2tmp%d.png", maxTimestamp);
//    system(buf);

}
void Bcg::checkTimestamps(int maxEdgeTimestamp) {
    for (size_t i = 0; i < nodes.size(); i++) {
        Node&n = nodes[i];
        assert(n.visited[0] <= timestamp);
        assert(n.visited[1] <= timestamp);
        assert(n.visited[0] >= 0);
        assert(n.visited[1] >= 0);
        for (size_t i2 = 0; i2 < n.edges.size(); i2++) {
            Edge& e = n.edges[i2];
            assert(e.ts <= maxEdgeTimestamp);
            assert(e.ts >= 0);
        }
    }
}
}
