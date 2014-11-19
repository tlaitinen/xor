#include "fud.hpp"
#include <string>
using namespace std;
namespace bx {
    void Fud::union_(int v1, int v2, int parity, Lit reason) {

        assert(numUnions < (int)unions.size());

        // increment timestamp
        timestamp++;
        if (timestamp == MAX_TIMESTAMP) {
            // in case the timestamp reaches its maximum value,
            // remap the timestamps so that invalid
            // references get the timestamp value 0
            // and the valid references > 0 and < unions.size() + 1
            TimestampRemapper remapper;    

            for (size_t i = 0; i < unions.size(); i++) {
                remapper.add(unions[i]);
            }
            // timestamp is set to higher than any used timestamp
            timestamp = remapper.compress();


            for (int i = 0; i < nodes.size(); i++) {
                Node&n = nodes[i];
                while (!n.parents.empty()) {
                    Link& l = n.parents.back();
                    if (unions[l.u] != l.timestamp) {
                        n.parents.pop_back();
                    } else
                        break;
                }
                while (!n.size.empty()) {
                    Size& s = n.size.back();
                    if (unions[s.u] != s.timestamp) {
                        n.size.pop_back();
                    } else
                        break;
                }

                // remap link stack timestamps
                for (size_t i2 = 0; i2 < n.parents.size(); i2++) {
                    Link& l = n.parents[i2];
                    l.timestamp = remapper.remap(l.timestamp);
                }
                // remap size stack timestamps
                for (size_t i2 = 0; i2 < n.size.size(); i2++) {
                    Size& s = n.size[i2];
                    s.timestamp = remapper.remap(s.timestamp);
                }
            }

            for (size_t i = 0; i < unions.size(); i++) {
                unions[i] = remapper.remap(unions[i]);
            }

        }
        D(dbg::fud,"Union(" << v1 << "," << v2 << "," << timestamp << ")");

        // the next unused union-timestamp is set
        unions[numUnions] = timestamp;
        int u = numUnions;
        numUnions++;

        // then find the roots of 'v1' and 'v2'
        Result p1;
        find(v1, p1);
        Result p2;
        find(v2, p2);

        // we will make a link between the roots,
        // so take into account the parity between the root nodes
        parity += p1.parity + p2.parity;

        // 'p2' will be the new root of 'p1'
        // if the subtree of 'p1' is bigger than the subtree of 'p2',
        // then swap 'p1' and 'p2' in order to acquire
        // a tree with smaller depth (approximation)
        bool p1Bigger = getNodeSize(nodes[p1.var]) > getNodeSize(nodes[p2.var]);
        if (p1Bigger) {
            int tmp = p1.var;
            p1.var = p2.var;
            p2.var = tmp;

        }


        D(dbg::fud,"Link(" << p1.var << "," << p2.var << "," << timestamp << "," << parity % 2 << ")");
        Node& p1n = nodes[p1.var];
        Node& p2n = nodes[p2.var];
        // add a new size record to the new root 'p2'
        // which is the sum of sizes of the trees 'p1' and 'p2'
        p2n.size.push_back(Size(getNodeSize(p1n)  + getNodeSize(p2n), timestamp, u));
        // add a link from 'p1' to 'p2'
        p1n.parents.push_back(
                Link(p2.var, timestamp, u, parity));
/*        if (p1Bigger)
            erg.link(v1, v2, reason);
        else
            erg.link(v2,v1, reason);*/
    }

    void Fud::deunion(int prevUnions)
    {
        D(dbg::fud,"deunion()");
//        assert(numUnions == erg.getNumLinks());
        // clears union-operation's timestamps and
        // decrements the number of used union-timestamps
        while (numUnions > prevUnions) {
            assert(numUnions > 0);
            numUnions--;
            unions[numUnions] = 0;
        }
        //erg.backtrack(prevUnions);
    }


void Fud::toGraphviz(const std::string& path)
    {
        FILE* f = std::fopen(path.c_str(), "w");
        std::fprintf(f, "digraph d {\n");
        for (int i = 0; i < nodes.size(); i++) {
            std::fprintf(f, "n%d [ label=\"%d, size=%d\" ];\n", i, i, getNodeSize(nodes[i]));
            if (!nodes[i].parents.empty()) {
                string arrow;
                if (nodes[i].parents.back().parity)
                    arrow = "dot";
                else
                    arrow = "normal";
                std::fprintf(f, "n%d -> n%d [ arrowhead=%s ];\n", i, nodes[i].parents.back().node, arrow.c_str());
                for (size_t i2 = 0; i2 < nodes[i].parents.size() - 1; i2++)
                    std::fprintf(f, "n%d -> n%d [style=dashed];\n", i, nodes[i].parents[i2].node);
            }
        }
        std::fprintf(f, "}\n");
        std::fclose(f);
//        erg.toGraphviz("erg-" + path);
    }

    std::string Fud::toString() {
        std::string res;
        for (int i = 0; i < nodes.size(); i++) {
            char buf[512];
            int parent = -1, parity=-1;
            for (int i2 = nodes[i].parents.size() - 1; i2 >= 0; i2--) {
                Link& l = nodes[i].parents[i2];
                if (unions[l.u] != l.timestamp)
                    continue;
                parent = l.node;
                parity = l.parity;
            }
            std::snprintf(buf, 512, "node id=%d size=%d parent=%d parity=%d\n", i, getNodeSize(nodes[i]), 
                    parent, parity);
            res += std::string(buf);
        }
        return res;
    }

void Fud::checkTimestamps() {
    for (size_t i = 0; i < nodes.size(); i++) {
        Node& n = nodes[i];
        for (size_t i2 = 0; i2 < n.parents.size(); i2++) {
            Link& l = n.parents[i2];
            assert(l.timestamp <= timestamp);            
            assert(l.timestamp >= 0);
        }
        for (size_t i2 = 0; i2 < n.size.size(); i2++) {
            Size& s = n.size[i2];
            assert(s.timestamp <= timestamp);            
            assert(s.timestamp >= 0);
        }
    }
    for (size_t i = 0; i < unions.size(); i++) {
        assert(unions[i] <= timestamp);
        assert(unions[i] >= 0);
    }
    assert(timestamp >= 0);
}
}
