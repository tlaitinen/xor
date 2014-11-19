
#include "erg.hpp"
namespace bx {
    int Erg::findCommonRoot(int node1, int node2) {
        timestamp++;

        nodes[node1].ts = timestamp;
        nodes[node2].ts = timestamp;
        D(dbg::prop, "findCommonRoot(" << node1 << "," << node2 << ")");
        while (1) {
            Link& p1 = nodes[node1].parent;
            Link& p2 = nodes[node2].parent;
#ifdef DEBUG
            if (p1.nodeId == node1 && p2.nodeId == node2) {
                D(dbg::prop, "no common root! node1" << node1
                        << " node2 " << node2);
                toGraphviz("erg.dot");
                exit(1);
                return -1;
            }
#endif

            D(dbg::prop, "node1 " << node1 << " node2 " << node2);
            if (p1.nodeId != node1) {

                node1 = p1.nodeId;
                D(dbg::prop, "node1 to " << p1.nodeId);
                if (nodes[node1].ts == timestamp)
                    return node1;
                nodes[node1].ts = timestamp;

            }
            if (p2.nodeId != node2) {
                node2 = p2.nodeId;
                D(dbg::prop, "node2 to " << p2.nodeId);

                if (nodes[node2].ts == timestamp)
                    return node2;
                nodes[node2].ts = timestamp;
            }
        }
    }

    void Erg::invertLinks(int nodeId, int newParentId, Lit newReason, bool strong) {

        D(dbg::prop, "invertLinks(" << nodeId << ", " << newParentId << ", strong=" << strong <<")");

        Link& link = nodes[nodeId].parent;
        if (link.nodeId != nodeId) {
            invertLinks(link.nodeId, nodeId, link.reason, strong);
        }

        D(dbg::prop, "invertLinks: changing " << nodeId << " -> " 
                << link.nodeId << " to " << nodeId << " -> " << newParentId);
        D(dbg::prop, "Pushing previous link [" << links.size() << "]: " << nodeId << " -> " << link.nodeId );

        links.push_back(LinkInfo(nodeId, link));
        link.nodeId = newParentId;
        link.reason = newReason;
        link.strong = strong;
    }
    void Erg::link(int parentId, int childId, Lit reason) {

        numLinks.push_back(links.size());
#ifdef DEBUG
        states.push_back(graphvizStr());
#endif
        D(dbg::prop, "erg::link(" << parentId << "," << childId
                << "," << (reason.get_sign() ? "-" : "")
                << reason.get_var());

        assert(parentId >= 0 && parentId < nodes.size());

        assert(childId >= 0 && childId < nodes.size());


        Link* link = &nodes[childId].parent;
        if (link->strong) {
            int tmp = childId;
            childId = parentId;
            parentId = tmp;
            link = &nodes[childId].parent;
            D(dbg::prop, "trying to change a strong link. swapping parent and child");
        }

        D(dbg::prop, "parentId " << parentId << " childId " << childId);

        bool strong = nodes[parentId].parent.strong;


        if (link->nodeId != childId) 
            invertLinks(childId, parentId, reason, strong);  
        else {

            D(dbg::prop, "Pushing previous link [" << links.size() << "]: " << childId << " -> " << link->nodeId );

            links.push_back(LinkInfo(childId, *link));
            link->nodeId = parentId;
            link->reason = reason;
            link->strong = nodes[parentId].parent.strong;
        }
        assert(nodes[0].parent.strong);

        //            nodes[parentId].children.push_back(childId);
    }
    void Erg::backtrack(size_t nl) {
        D(dbg::prop, "erg::backtrack(" << nl << ")");
        int lim = numLinks[nl];
        for (int i = links.size() - 1; i >= lim; i--) {
            //    int parentId = nodes[links[i].nodeId].parent.nodeId;
            //    nodes[parentId].children.pop_back();
            D(dbg::prop, "Restoring  previous link [" << i << "]: " << links[i].nodeId << " -> " << links[i].link.nodeId );
            nodes[links[i].nodeId].parent = links[i].link;            
            D(dbg::prop, "node " << links[i].nodeId << " points now to " << nodes[links[i].nodeId].parent.nodeId);

        }
        links.resize(lim);
#ifdef DEBUG
        FILE* f = std::fopen("original.dot", "w");
        fprintf(f, "%s", states[nl].c_str());
        std::fclose(f);
        toGraphviz("current.dot");

        assert(states[nl] == graphvizStr());
        states.resize(nl);
#endif
        numLinks.resize(nl);
        assert(nodes[0].parent.strong);
    }


}

