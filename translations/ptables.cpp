#include <assert.h>

#include <iostream>
#include <set>
#include <sys/time.h>
#include <stdint.h>
#include <boost/tokenizer.hpp>
#include <map>
#include <sstream>
#include <vector>
#include <boost/program_options.hpp>
#include <algorithm>
#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
#include <boost/graph/undirected_dfs.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/smart_ptr.hpp>
#ifdef DEBUG 
#define D(x) if (verbose) { cerr << x << endl; }
#else
#define D(x)
#endif
namespace cyclep {
    using namespace std;
    struct Edge {
        int edgeId;
        int nodeId;
        Edge(int eId, int nId) : edgeId(eId), nodeId(nId){}
    };
    struct DfsNode {
        vector<Edge> path;
        DfsNode(const DfsNode& prev, Edge edge) {
            path = prev.path;
            path.push_back(edge);
        }
        DfsNode(int nodeId) {
            path.push_back(Edge(0, nodeId));
        }
        DfsNode() {
        }
    };

    struct Node {
        int id;
        bool var;
        bool rhs;
        int color;
        bool traversed;
        DfsNode reachedBy;
        vector<Edge> edges;
        Node() : id(0), var(false), rhs(true), color(0), traversed(false) {}
    };


    bool verbose = false;
    
    class Xcnf2Colorable {

        vector<Node> nodes;
        vector<bool> edgeTraversed;
        vector<Edge> edges;



        int maxVar;
        int newVars;
        int edgeIdSeq;

        public:
        Xcnf2Colorable();

        void addEdge(int n1, int n2) {
            int edgeId = edgeIdSeq++;

            nodes[n1].edges.push_back(Edge(edgeId, n2));
            nodes[n2].edges.push_back(Edge(edgeId, n1));


        }
        void read(vector< vector<int > >& clauses) {
            int maxVar = -1;
            for (size_t i = 0; i < clauses.size(); i++) {
                for (size_t i2 = 0; i2 < clauses[i].size(); i2++) {
                    if (abs(clauses[i][i2]) > maxVar)
                        maxVar = abs(clauses[i][i2]);
                }
            }

            nodes.resize(maxVar + clauses.size() + 1);
            for (size_t i = 1; i <= maxVar && i < nodes.size(); i++) {
                nodes[i].var = true;
                nodes[i].id = i;
                nodes[i].color = 0;
            }
            for (size_t i = 0; i < clauses.size(); i++) {
                int nId = maxVar + 1 + i;
                nodes[nId].var = false;
                nodes[nId].id = i;
                vector<int>& c = clauses[i];
                int parity = 1;
                for (size_t j = 0; j < c.size(); j++) {
                    if (c[j] < 0)
                        parity = 1 - parity;
                    addEdge(nId, abs(c[j]));
                }

                nodes[nId].rhs = parity;
            } 

        }
        int getUntraversedNode() {
            for (size_t i = 1; i < nodes.size(); i++) {
                if (nodes[i].var && !nodes[i].traversed && nodes[i].edges.size() > 0)
                    return i;
            }
            return 0;
        }
        void getVars(int clauseNodeId, set<int>& vars) {

            Node& c = nodes[clauseNodeId];
            assert(c.var == false);
            for (size_t i = 0; i < c.edges.size(); i++) {
                Node& v = nodes[c.edges[i].nodeId];
                assert(v.var == true);
                vars.insert(v.id);
            }
        }
        bool cycle(const DfsNode& dfsNode) {
            D("Partial cycle :");
            vector<int> innerVars;
            vector<int> outerVars;

            set<int> allVars;
            for (size_t i = 0; i < dfsNode.path.size(); i++) {
                const Edge& e = dfsNode.path[i];
                const Node& n = nodes[e.nodeId];
                if (n.var == false) {
                    getVars(e.nodeId, allVars);
                }
                else {

                    D(" " << n.id);
                    innerVars.push_back(n.id);
                }
            }

            sort(innerVars.begin(), innerVars.end());

            set_difference (allVars.begin(), allVars.end(), 
                    innerVars.begin(), innerVars.end(),
                    back_inserter(outerVars));

            for (size_t i = 0; i < innerVars.size(); i++) {
                int id = innerVars[i];
                if (nodes[id].color == 2) {
                    D("Variable " << id << " previously outer. Now inner");
                    return true;
                } else if (nodes[id].color == 0) {
                    nodes[id].color = 1;
                }
            }

            for (size_t i = 0; i < outerVars.size(); i++) {
                int id = outerVars[i];
                if (nodes[id].color == 1) {
                    D("Variable " << id << " previously inner. Now outer");
                    return true;
                } else if (nodes[id].color == 0) {
                    nodes[id].color = 2;
                }
            }

            D(" (outer variables :");
            for (size_t i = 0; i < outerVars.size(); i++) {
                cerr << " " << outerVars[i];
            }
            D(")" << endl);



            return false;
        }
        bool check() {
            vector<DfsNode> dfs;

            edgeTraversed.resize(edgeIdSeq);
            while (1) {

                int nodeId = getUntraversedNode();
                if (!nodeId)
                    break;

                nodes[nodeId].traversed = true;
                dfs.push_back(DfsNode(nodeId));
                while (!dfs.empty()) {
                    DfsNode dfsNode = dfs.back();
                    dfs.pop_back();

                    Node& node = nodes[dfsNode.path.back().nodeId];
                    for (size_t i = 0; i < node.edges.size(); i++) {
                        Edge& edge = node.edges[i];
                        if (edgeTraversed[edge.edgeId])
                            continue;
                        edgeTraversed[edge.edgeId] = true;
                        Node& neighbor = nodes[edge.nodeId];
                        DfsNode next(dfsNode, edge);
                        if (neighbor.traversed) {
                            if (cycle(next))
                                return true;
                        } else {
                            neighbor.traversed = true;
                            neighbor.reachedBy = dfsNode;
                            dfs.push_back(next);
                        }
                    }
                }
            }

            return false;
        }
    };


    Xcnf2Colorable::Xcnf2Colorable() : maxVar(0), newVars(0), edgeIdSeq(1) {
    }

}
namespace po = boost::program_options;

size_t k2Limit, k3Limit, kvLimit;
using namespace std;
using boost::tuple;
using boost::make_tuple;
  template <class T> std::string toString(const T& t) {
        std::ostringstream ost;
        ost << t;
        return ost.str();
    }

 template <> std::string toString(const set<int32_t>& s) {
     std::ostringstream ost;
     for (set<int32_t>::const_iterator si = s.begin(); si != s.end(); si++) {
         if (si != s.begin())
             ost << " ";
         ost << toString(*si);
     }
     return ost.str();
 }
 template <> std::string toString(const vector<int32_t>& s) {
     std::ostringstream ost;
     for (vector<int32_t>::const_iterator si = s.begin(); si != s.end(); si++) {
         if (si != s.begin())
             ost << " ";
         ost << toString(*si);
     }
     return ost.str();
 }



bool verbose,  force, stopFlag;

struct Var {
    int32_t id;
    bool eliminated;
    bool scheduled;
    int component;
    vector<int32_t> friends;

     vector< boost::weak_ptr< set<int32_t> > > ptables;

        
    Var(int32_t i) : id(i),
      eliminated(false), scheduled(false), component(i)
    {}

    void addFriend(int v) {
        for (size_t i = 0; i < friends.size(); i++) {
            if (friends[i] == v)
                return;
        }
        friends.push_back(v);
    }
    void removeFriend(int v) {
        for (size_t i = 0; i < friends.size(); i++) {
            if (friends[i] == v) {
                friends[i] = friends.back();
                friends.pop_back();
                break;
            }
        }
    }
};

struct Component {
    bool treelike;
    bool cyclePartitionable;
    int numVars;
    Component() : treelike(false), cyclePartitionable(false), numVars(0) {}
};
class XorGraph {

    int32_t clauseIdSeq;
    typedef vector<Var> Vars;

    Vars vars;

    typedef vector< vector<int32_t> > Clauses;
    Clauses clauses;
    int  remainingVars;

    bool started;
    vector<Component> components;
    vector<bool> varFlag;

    int numComponents;
    size_t maxClauses;

    public:    
    XorGraph(size_t maxClauses_) : clauseIdSeq(1),  remainingVars(0), started(false),  numComponents(0), maxClauses(maxClauses_) {
        vars.push_back(Var(0));
    }
    int32_t addVar() {
        int32_t id = vars.size();
        vars.push_back(Var(vars.size()));
        return id;
    }
    
    int32_t addClause(const vector<int32_t>& vs, bool rhs) {
        int32_t maxVar = 0;
        for (vector<int32_t>::const_iterator vsi = vs.begin();
                vsi != vs.end(); vsi++) {
            if (*vsi > maxVar)
                maxVar = *vsi;
        }
        size_t needVars = maxVar;
        while (vars.size() <= needVars) {
            addVar();
        }
        D("föö");
       D("Adding clause " << toString(vs) << " = " << rhs );
        size_t cId = clauses.size();
        clauses.push_back(vs);
        for (size_t i1 = 0; i1 < vs.size(); i1++) {
            for (size_t i2 = 0; i2 < vs.size(); i2++) {
                D("vars[" << vs[i1] << "].addFriend(" << vs[i2] << ")");
                vars[vs[i1]].addFriend(vs[i2]);
            }
        }

        return cId;
    }

    struct detect_loops : public boost::dfs_visitor<> 
    { 
        bool& loop;
        detect_loops(bool& loop_ ) : loop(loop_) {}
        template <class Edge, class Graph>
            void back_edge(Edge e, const Graph& g) { 
                loop = true;
            } 
    }; 

    bool isTreeLike(int c) {
        using namespace boost;
        typedef adjacency_list< vecS, vecS, undirectedS,
                no_property,
                property<edge_color_t, default_color_type> > Graph;
        typedef graph_traits<Graph>::vertex_descriptor Vertex;


        int cid = 1;
        Graph g;
        //cerr << "isTreeLike(" << c << ")" << endl;
        int rootNode = 0;
        for (Clauses::iterator i = clauses.begin(); i != clauses.end(); i++) {
            const vector<int32_t>& s = *i;
            int firstVar = *s.begin();
            if (vars[firstVar].component != c)
                continue;
            if (!rootNode)
                rootNode = firstVar;

            for (vector<int32_t>::const_iterator si = s.begin(); si != s.end(); si++) {
                add_edge(*si, vars.size() + cid, g); 

                //cerr << "adding edge " << *si << " -> " << vars.size() + cid << endl;
            }

            cid ++;
        }

        bool loop;
        detect_loops vis(loop); 
        undirected_dfs(g, root_vertex(Vertex(rootNode)).visitor(vis)
                .edge_color_map(get(edge_color, g)));

        return loop == false;


    }

    bool isCyclePartitionable(int c) {
        cyclep::Xcnf2Colorable cyclePartitionable;
        
        cyclePartitionable.read(clauses);
        return cyclePartitionable.check() == false;
    }

    void initConnectedComponents() {
        using namespace boost;
        typedef adjacency_list <vecS, vecS, undirectedS> Graph;
        Graph g;
        int cid = 1;
        for (Clauses::iterator i = clauses.begin(); i != clauses.end(); i++) {
            const vector<int32_t>& s = *i;
            for (vector<int32_t>::const_iterator si = s.begin(); si != s.end(); si++) {
                add_edge(*si, vars.size() + cid, g); 
            }
            cid ++;
        }
        std::vector<int> component(num_vertices(g));
        numComponents = connected_components(g, &component[0]);

        std::vector<int>::size_type i;

        cerr << "Connected components: " << numComponents << endl;

        components.resize(numComponents);
        for (i = 1; i < vars.size(); ++i) {
            //cerr << "var " << i << " is in " << component[i] << endl;
            vars[i].component = component[i];
            components[vars[i].component].numVars++;
        }
        for (i = 0; i < numComponents; i++) {
            if (force)
                continue;

            if (components[i].numVars <= 1) {
                components[i].treelike = true;
                continue;
            }
            components[i].treelike = isTreeLike(i);
            if (!components[i].treelike) {

                components[i].cyclePartitionable = isCyclePartitionable(i);
            } else
                components[i].cyclePartitionable = true;
            cerr << "component[" << i << "]: vars=" << components[i].numVars << " treelike="
                << components[i].treelike
                << " cycle-partitionable=" << components[i].cyclePartitionable << endl;

        }
    }

    void read() {
        string line;
        while (!cin.eof()) {
            getline(cin, line);

            cout << line << endl;
            if (line.empty())
                continue;
            if (line[0] != 'x') {
                continue;
            }

            typedef boost::tokenizer<boost::char_separator<char> > 
                tokenizer;
            boost::char_separator<char> sep(" ");
            tokenizer tok(line, sep);
            vector<int32_t> vs;
            bool rhs = true;
            bool more = false;
            for (tokenizer::iterator i = tok.begin();
                    i != tok.end(); i++) {
                int32_t num = atoi((*i).c_str());
                if (num) {
                    if (num < 0) {
                        rhs = !rhs;
                        num = abs(num);
                    }
                    vs.push_back(abs(num));
                }
            }
            addClause(vs, rhs);
        }
        initConnectedComponents();
        started = true;
        remainingVars = vars.size();
        for (size_t i = 1; i < vars.size(); i++) {
            Component& c = components[vars[i].component];
            if (c.treelike) {
                vars[i].eliminated = true;
                remainingVars --;
            }
        }
       
        // cout << "c xupify" << endl;

    }

    Var& getVar(int32_t id)  {
        assert(id >= 0 && id <(int32_t) vars.size());
        return vars[id];
    }
     
    void eliminate(int32_t varId) {
        D( "eliminate(" << varId << ")");

        vector<int32_t>& s = vars[varId].friends;;
        cerr << "Eliminating x" << varId 
            << " (" << remainingVars << " left). Xor-friends " 
            << s.size() << endl;
        assert(varId >= 0 && varId < vars.size());
        Var& n = vars[varId];
        assert(n.eliminated == false);
        remainingVars--;
        bool skip = false;
        size_t kLimit = 0;
        if (k2Limit) {
            if (s.size() > k2Limit) 
                skip = true;
            else
                kLimit = 2;
        }
        if (k3Limit) {
            if (s.size() <= k3Limit)
                kLimit = 3;
        }
        if (kvLimit) {
            if (s.size() <= kvLimit)
                kLimit = s.size();
        }
        if (components[n.component].cyclePartitionable)
            kLimit = 2;

        if (!skip)
            cout << "c ptable(" << kLimit << "," << toString(s) << ")" << endl;

        vars[varId].eliminated = true;
        vector<int32_t> friends = vars[varId].friends;
        for (size_t i = 0; i < friends.size(); i++) {
            int f = friends[i];
            D("vars[" << f << "].removeFriend(" << varId << ")");
            vars[f].removeFriend(varId);
            for (size_t i2 = 0; i2 < friends.size(); i2++) {
                if (friends[i2] != varId) {
                    D("vars[" << f << "].addFriend(" << friends[i2] << ")");
                    vars[f].addFriend(friends[i2]);
                }
            }
        }
    }

    
    void getLeastPopularVars(vector<int32_t>& toEliminate) {
        size_t minFriends = vars.size();

        toEliminate.clear();
        for (size_t i = 1; i < vars.size(); i++) {
            Var& n = vars[i];
            if (n.eliminated)
                continue;
            n.scheduled = false;
            if (n.friends.size() <  minFriends) {
                minFriends = n.friends.size();
            }
        }
        for (size_t i = 0; i < vars.size(); i++) {
            Var& n = vars[i];

            if (n.eliminated || n.friends.size() != minFriends)
                continue;
            bool friendScheduled = false;

            for (size_t i2 = 0; i2 < n.friends.size(); i2++) {
                int v = n.friends[i2];
                Var& f = vars[v];
                assert(f.eliminated == false);
                if (f.scheduled) {
                    friendScheduled = true;
                    break;
                }
            }
            if (!friendScheduled) {
                toEliminate.push_back(i);
                for (size_t i2 = 0; i2 < n.friends.size(); i2++) {
                    int v= n.friends[i2];
                    vars[v].scheduled = true;
                }
            }
        }
    }
};
int main(int argc, char** argv) {
    struct timeval start, stop;
    gettimeofday(&start, NULL);

    po::options_description desc("Allowed options");

    size_t maxFriends;
    size_t maxClauses;
    desc.add_options()
         ("help,h", "produce help message")
         ("verbose,v", "be verbose")
         ("max-friends,m",po::value<size_t>(&maxFriends)->default_value(0), "xupify variables with at most (arg) xor-friends")
         ("k2-limit",po::value<size_t>(&k2Limit)->default_value(0), "use k=2 when |V| is smaller than the param")
         ("k3-limit",po::value<size_t>(&k3Limit)->default_value(0), "use k=3 when |V| is smaller than the param")
         ("kv-limit",po::value<size_t>(&kvLimit)->default_value(0), "use k=|V| when |V| is smaller than the param")
         ("force,f","no special treatment for tree-like and cycle-partitionable components")
        ;

    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);    

    if (vm.count("help")) {
            cerr << desc << "\n";
                return 1;
    }
    verbose = vm.count("verbose");
    force = vm.count("force");
    stopFlag = false;
    XorGraph xg(maxClauses);
    xg.read();
    vector<int32_t> toEliminate;
    while (!stopFlag) {
        xg.getLeastPopularVars(toEliminate);
        if (toEliminate.empty())
            break;
        Var& n = xg.getVar(toEliminate[0]);
        vector<int32_t>& s = n.friends;
        cerr << "Found " << toEliminate.size() << " independent variables "
            << " " << s.size() << " xor-friends" << endl;
        if (maxFriends && s.size() > maxFriends) {
            cerr << "Eliminated all vars with at most " << maxFriends << 
                " xor-friends." << endl;
            break;
        }

        for (size_t i = 0; i < toEliminate.size(); i++) {
            int32_t varId = toEliminate[i];
            assert(varId >= 0);
            Var& n = xg.getVar(varId);
            assert(n.eliminated == false);

            xg.eliminate(varId);
        }
    }
    gettimeofday(&stop, NULL);
    long double s = (long double)( stop.tv_sec * 1000000.0)
                  - (long double)(start.tv_sec * 1000000.0)
                  + (long double)(stop.tv_usec - start.tv_usec);

    cerr << "c ptables took " << s / 1000000.0 << " seconds" << endl;
    return 0;
}
