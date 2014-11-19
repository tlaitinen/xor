#ifndef _erg_hpp_
#define _erp_hpp_
#include <vector>
#include <string>
#include <cstdio>
#include <assert.h>
#include <stdlib.h>
#include "util.hpp"
#include "Settings.hpp"
namespace bx {
    class Erg {
        int findCommonRoot(int node1, int node2);
        void propagateStrong(int nodeId);

        void invertLinks(int nodeId, int newParentId, 
                         Lit newReason, bool strong);

           public:

        struct Link {
            int nodeId;
            Lit reason;
            bool strong;
        };
        struct LinkInfo {
            int nodeId;
            Link link;
            LinkInfo(int nId, const Link& l) 
                : nodeId(nId), link(l) {}
            LinkInfo() {}
        };
        struct Node {
            Link parent;
            std::vector<int> children;
            int ts;
        };

        std::vector<Node> nodes;
        std::vector<LinkInfo> links;
        std::vector<int> numLinks;
        std::vector<int> numOcc;
        std::vector<int> toExplain;
        std::vector<std::string> states;

        const Settings& settings;
        int timestamp;
        Erg(const Settings& settings_) : settings(settings_), timestamp(0) {}

        void setup(int variables) {
            nodes.resize(variables);
            for (size_t i = 0; i < nodes.size(); i++) {
                nodes[i].parent.nodeId = i;
                nodes[i].parent.reason = Lit(0,false);
                nodes[i].parent.strong = (i == 0);
                nodes[i].ts = 0;

            }
            numOcc.resize(variables);
        }

        void link(int parentId, int childId, Lit reason);
        void backtrack(size_t numLinks);
        size_t getNumLinks() const  {
            return numLinks.size();
        }

        void explain(std::vector<Lit>& exp, int node1, int node2, long long& evenElim) {
            //        toGraphviz("erg.dot");
/*            if (node2 == 0) {
                while (node1 != 0) {
                    Link& link = nodes[node1].parent;
                    exp.push_back(link.reason.neg());
                    node1 = link.nodeId;
                }
                return;
            }
  */          
            int root = findCommonRoot(node1, node2);

            size_t first = exp.size();
#ifdef DEBUG
            for (size_t i = 0; i < numOcc.size(); i++) {
                assert(numOcc[i] == 0);
            }

#endif
            //        if (root == -1)
            //            return;
            D(dbg::prop, "found root " << root);

            while (1) {
                Link& p1 = nodes[node1].parent;
                Link& p2 = nodes[node2].parent;
                if (node1 != root) {
//                    int var = p1.reason.get_var();

                    //                if (!numOcc[var])
                    exp.push_back(p1.reason.neg());
                    //                numOcc[var]++;                   
                    node1 = p1.nodeId;
                    D(dbg::prop, "moving node1 to " << node1 << " exp " << bx::toString(p1.reason.neg()));
                }
                if (node2 != root) {
  //                  int var = p2.reason.get_var();

                    //                if (!numOcc[var])

                    exp.push_back(p2.reason.neg());
                    //                numOcc[var]++;    
                    node2 = p2.nodeId;
                    D(dbg::prop, "moving node2 to " << node2 << " exp " << bx::toString(p2.reason.neg())                          );

                } else if (node1 == root) 
                    break;
            }
            /*
               int last = exp.size() - 1;
               for (int i = first; i <= last; ) {
               int var = exp[i].get_var();
               if (numOcc[var] % 2 == 0 && settings.evenParityElimination) {
               D(dbg::prop, "even-eliminated " << exp[i].get_var());
               if (last >= 0)
               exp[i] = exp[last--];
               evenElim++;
               } else
               i++;
               numOcc[var] = 0;
               }

               exp.resize(last+1);
             */
        }

        std::string graphvizStr() {
            char buf[8192];
            std::string r;
            std::snprintf(buf, 8192, "digraph d {\n");
            r += buf;
            for (size_t i = 0; i < nodes.size(); i++) {
                std::snprintf(buf, 8192, "n%d [ label=\"%d\" ];\n", (int)i, (int)i);
                r += buf;
                Link& link = nodes[i].parent;
                if (link.nodeId != i) {
                    std::snprintf(buf, 8192, "n%d -> n%d [ label=\"%s%d\" %s];", 
                            (int)i, link.nodeId, link.reason.get_sign() ? "-" : "", link.reason.get_var(),
                            link.strong ? " style=\"bold\" " : "");
                    r += buf;
                }
            }
            std::snprintf(buf, 8192, "}\n");
            r += buf;
            return r;
        }
        void toGraphviz(const std::string& path) {
            D(dbg::prop, "writing " << path);
            FILE* f = std::fopen(path.c_str(), "w");
            fprintf(f, "%s", graphvizStr().c_str());
            std::fclose(f);
        }
    };
}
#endif
