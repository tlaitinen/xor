/*
 Copyright (C) Tero Laitinen
 
 This program is free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License version 3
 as published by the Free Software Foundation.
 
 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.
 
 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/


#include "ImplicationGraph.hpp"
#include "Split.hpp"
#include <iostream>
#include <cstdlib>
#include <set>
#include <queue>
#include <functional>
#include <limits.h>
using namespace std;


namespace xorsat {

    bool ImplicationGraph::isRedundant(NodePos n) {
        DBG(1, "isRedundant(" << n << ")");
        Node& node = nodes[n];
        node.timeStamp = currentTime;
        node.redundant = false;

        if (n < firstReasonNode) {
            DBG(1, "n=" << n << " < firstReasonNode=" << firstReasonNode
                     <<  " : returning false");
            return false;
        }

        if (node.varId && n != checkingRedundant) {
            if (reason.has(n)) {
                DBG(1, n << " is in reason and not being checked -> return true");
                node.redundant = true;
                return true;
            }
            if (node.parent1 == PremiseNode
                    && node.parent2 == PremiseNode) {
                DBG(1, n << " is a decision literal -> return false");
                node.redundant = false;
                return false;

            }
        }
       
        if (node.parent1 != PremiseNode) {
            Node& p = nodes[node.parent1];
            if (p.timeStamp < currentTime) {
                DBG(1, "checking parent1 " << node.parent1);
                if (!isRedundant(node.parent1)) {
                    DBG(1, "node " << n << " is not redundant");
                    return false;
                }
            } else {
                if (!nodes[node.parent1].redundant)
                    return false;
            }
        }

        if (node.parent2 != PremiseNode) {
            Node& p = nodes[node.parent2];
            if (p.timeStamp < currentTime) {
                DBG(1, "checking parent2 " << node.parent1);

                if (!isRedundant(node.parent2)) {
                    DBG(1, "node " << n << " is not redundant");
                    return false;
                }
            } else {
                if (!nodes[node.parent2].redundant)
                    return false;
            }
        }
        DBG(1, "node " << n << " is redundant");

        node.redundant = true;
        return true;
    }

    void ImplicationGraph::explain(NodePos n) {

        DBG(1, "explain(" << n << ") numToExplain=" << numToExplain);
        reason.remove(n);

        if (n >= firstOnLastLvl)  {
            onLastLevel--;
            DBG(1, "onLastLevel : " << onLastLevel);
        }
        Node& node = nodes[n];

        if (node.parent1 != PremiseNode) {
            if (reason.has(node.parent1) == false) {

                if (node.parent1 >= firstOnLastLvl)
                    onLastLevel++;
                DBG(1, "onLastLevel : " << onLastLevel);

                reason.add(node.parent1);
                if (!toExplain[node.parent1]) {

                    numToExplain++;
                    toExplain[node.parent1] = 1;
                }
            }
        }

        if (node.parent2 != PremiseNode) {
            if (reason.has(node.parent2) == false) {

                if (node.parent2 >= firstOnLastLvl)
                    onLastLevel++;

                DBG(1, "onLastLevel : " << onLastLevel);

                reason.add(node.parent2);
                if (!toExplain[node.parent2]) {
                    numToExplain++;
                    toExplain[node.parent2] = 1;
                }
            }

        }
    }

    void ImplicationGraph::dfsExplain(NodePos n) {
        DBG(1, "explain(" << n << ")");

        Node& node = nodes[n];
        node.timeStamp = currentTime;
        if (node.subVarId) 
            participated.push_back(nodes[n].subVarId);

        if (node.varId) {
            if (!reason.has(n)) {
                if (n < firstReasonNode)
                    firstReasonNode = n;
                reason.add(n);
            }
            return;
        }

        if (node.parent1 != PremiseNode) {
            Node& p = nodes[node.parent1];
            if (p.timeStamp < currentTime) {
                dfsExplain(node.parent1);
            }
        }

        if (node.parent2 != PremiseNode) {
            Node& p = nodes[node.parent2];
            if (p.timeStamp < currentTime) {
                dfsExplain(node.parent2);
            } 
        }
    }                                

    void ImplicationGraph::dfsTag(NodePos n) {

        Node& node = nodes[n];
        node.timeStamp = currentTime;
        node.interesting = true;
        if (node.varId) {
            return;
        }


        if (node.parent1 != PremiseNode) {
            Node& p = nodes[node.parent1];
            if (p.timeStamp < currentTime) {
                dfsTag(node.parent1);
            }
        }
        if (node.parent2 != PremiseNode) {
            Node& p = nodes[node.parent2];
            if (p.timeStamp < currentTime) {
                dfsTag(node.parent2);
            }
        }
    }



    void ImplicationGraph::justify(Disjunction& d, 
                                   NodePos target,
                                   bool firstUIP,
                                   bool minimize) {


        if (dLevels.empty()) {
            DBG(1, "no decision levels. empty reason");
            d.literals.clear();
            return;
        }
        numJustified++;
        currentTime++;
        for (size_t i = 0; i < used; i++)
            nodes[i].interesting = false;
        Node& p = nodes[target];
        dfsTag(target);
        if (p.parent1 != PremiseNode)
            dfsTag(p.parent1);
        if (p.parent2 != PremiseNode)
            dfsTag(p.parent2);


        currentTime++;
        firstReasonNode = used;

        reason.setup(used);
        reason.clear();

        participated.clear();

        if (nodes[target].subVarId) {
            DBG(1, "target node has participated variable x"
                    << nodes[target].subVarId);
            participated.push_back(nodes[target].subVarId);
        }

        //        DBG(1, "visited contents : " << visited.toString());
        NodePos p1 = nodes[target].parent1;
        NodePos p2 = nodes[target].parent2;
        NodePos parent1 = PremiseNode, 
                parent2 = PremiseNode, 
                newer, older;

        bool p1dec = p1 != PremiseNode && (nodes[p1].parent1 == PremiseNode)
            && (nodes[p1].parent2 == PremiseNode);


        bool p2dec = p2 != PremiseNode && (nodes[p2].parent1 == PremiseNode)
            && (nodes[p2].parent2 == PremiseNode);
        DBG(1, "p1 : " << p1 << " p2 : " << p2);

        DBG(1, "p1dec : " << p1dec << " p2dec : " << p2dec);
        bool explainFirst = p1 < p2;
        if (p1dec || p1 == PremiseNode)
            explainFirst = false;
        if (p2dec || p2 == PremiseNode)
            explainFirst = true;
        if (p1 != PremiseNode && p2 != PremiseNode) {
            if (nodes[p1].varId != 0 && nodes[p2].varId == 0) 
                explainFirst = false;
            if (nodes[p1].varId == 0 && nodes[p2].varId != 0)
                explainFirst = true;
        }
       
                

        if (explainFirst) {
            if (p1 != PremiseNode) {
                parent1 = nodes[p1].parent1;
                parent2 = nodes[p1].parent2;
            }
            newer = p2;
            older = p1;
        } else {
            if (p2 != PremiseNode) {
                parent1 = nodes[p2].parent1;
                parent2 = nodes[p2].parent2;
            }
            newer = p1;
            older = p2;
        }
        if (!firstUIP) {
            if (parent1 != PremiseNode) {
                DBG(1, "explaining parent1 : " << parent1);

                dfsExplain(parent1);
            } 
            if (parent2 != PremiseNode) {
                DBG(1, "explaining parent2 : " << parent2);
                dfsExplain(parent2);
            }
            if (parent1 == PremiseNode && parent2 == PremiseNode) {
                DBG(1, "explaining older : " << older);
                dfsExplain(older);
            }
            if (newer != PremiseNode) {
                DBG(1, "explaining newer : " << newer);
                dfsExplain(newer);
            }
        } else {
            int lastLvl = dLevels.size() - 1;
            while (target < dLevels[lastLvl])
                lastLvl--;
            firstOnLastLvl = dLevels[lastLvl];
            DBG(1, "first on last level : " << firstOnLastLvl);
            assert(target >= firstOnLastLvl);


            DBG(1, "reason set before justify : " << reason.toString());
            onLastLevel = 1;
            numToExplain = 0;

            reason.add(target);
            explain(target);

            if (reason.size() == 2) {
                IntSet::const_iterator i = reason.begin();
                NodePos n1 = *i++;
                NodePos n2 = *i;
                if (abs(nodes[n1].varId) == abs(nodes[n2].varId)) {
                    DBG(1, "Reason set is a tautology. expanding\n");
                    if (n1 < n2) {
                        explain(n1);
                        numToExplain--;
                        toExplain[n1] = 0;
                    }
                    else {
                        explain(n2);
                        numToExplain--;
                        toExplain[n2] = 0;

                    }
                } else {
                    if (!toExplain[older]) {
                        numToExplain++;
                        toExplain[older] = 1;                
                    }
                }                                    
            }
                







            DBG(1, "reason set before loop : " << reason.toString());



            NodePos n = target;
            while (numToExplain > 0)
            {
                while (!toExplain[n])
                    n--;
                toExplain[n] = 0;
                numToExplain--;

                DBG(1, "Popped toExplain node " << n);
                Node& node = nodes[n];

#ifdef DEBUG
                if (node.varId == 0) {
                    DBG(1, "Is not a variable node. goin to explain it");
                } else {
                    if (n >= firstOnLastLvl) {
                        if (onLastLevel > 1) {
                            DBG(1, "Reason set has " << onLastLevel
                                    << " on the last level. explaining");
                        }
                    }
                }
#endif

                if (node.varId == 0 
                        || (n >= firstOnLastLvl && onLastLevel > 1)) {
                    if (node.subVarId) {
                        DBG(1, "Variable x" << node.subVarId <<
                                " participated in the derivation");
                        participated.push_back(node.subVarId);
                    }

                    explain(n);
                } else {
                    DBG(1, "Not explaining " << n);
                }

            }
            for (IntSet::const_iterator p = reason.begin();
                    p != reason.end(); p++) {
                if (*p < firstReasonNode)
                    firstReasonNode = *p;
            }

        }


        vector<NodePos> redundant;
        if (currentTime == UINT_MAX - 1) {
            for (size_t i = 0; i < used; i++)
                nodes[i].timeStamp = 0;

            currentTime = 0;
        }

        if (minimize) {
            for (IntSet::const_iterator p = reason.begin();
                    p != reason.end(); p++) {

                currentTime++;
                if (currentTime == UINT_MAX - 1) {
                    for (size_t i = 0; i < used; i++)
                        nodes[i].timeStamp = 0;


                    currentTime = 0;
                }

                const Node& node = nodes[*p];
                checkingRedundant = *p;
                if (*p > firstReasonNode 
                        && (node.parent1 != PremiseNode
                            || node.parent2 != PremiseNode)
                        && isRedundant(*p)) {

                    redundant.push_back(*p);
                }            
            }
            for (size_t i = 0; i < redundant.size(); i++) {

                DBG(1, "eliminated redundant : " << redundant[i]);
                numRedundantLiterals++;
                reason.remove(redundant[i]);
            }
        }

        reasonLits.clear();
        DBG(1, "reason : " << reason.toString());
        for (IntSet::const_iterator p = reason.begin();
                p != reason.end(); p++) {
            const Node& node = nodes[*p];

            DBG(1, "adding varId=" << node.varId << " value="
                    << abs(node.varId) * 2 + ((node.varId < 0) ? 1 : 0));

            reasonLits.add(abs(node.varId) * 2 + ((node.varId < 0) ? 1 : 0));
        }

        Node& targetNode = nodes[target];
        d.literals.clear();
        if (targetNode.varId != 0) {
            // justifying an implied literal
            d.literals.push_back(Literal(abs(targetNode.varId),
                        targetNode.varId < 0));
        }

        DBG(1, "reasonLits : " << reasonLits.toString());
        for (IntSet::const_iterator p = reasonLits.begin();
                p != reasonLits.end(); p++) {
            DBG(1, "reason set item : " << *p);
            VariableId varId = *p / 2;
            bool negative = (*p % 2) > 0;
            DBG(1, "varId="<< varId << " neg=" << negative
                    << " opposite literal value : " << 
                    varId * 2 + ((negative == false) ? 1 : 0));
            if (reasonLits.has(varId * 2 + ((negative == false) ? 1 : 0))) {
                DBG(1, "found tautology");
                d.literals.clear();
                break;
            }
            DBG(1, " adding literal x" << varId << " neg=" << negative);
            d.literals.push_back(Literal(varId, negative == false));
        }
        reasonStr = d.toString();
#ifdef DEBUG        
        DBG(2, toGraphviz());
        DBG(2, toCode());
        DBG(2, "after justify reason set : " << reason.toString());
        DBG(2, "Participated set : ");
        for (size_t i = 0; i < participated.size(); i++)
            DBG(2, " - x" << xorsat::toString(participated[i]));
#endif
    }

    static string n(int node) {
        return "n" + xorsat::toString(node);
    }


#ifdef DEBUG
    string ImplicationGraph::toString() const {
        Split res;
        res.push_back("Nodes:");
        res.push_back("ID\tVarId\tSubVarId\tParent1\tParent2");
        for (size_t i = 0; i < used; i++) {
            Split fields;
            fields.push_back(xorsat::toString(i));
            if (nodes[i].varId != 0)
                fields.push_back(xorsat::toString(nodes[i].varId));
            else
                fields.push_back("");
            if (nodes[i].subVarId != 0)
                fields.push_back(xorsat::toString(nodes[i].subVarId));
            else
                fields.push_back("");


            if (nodes[i].parent1 != -1)
                fields.push_back(xorsat::toString(nodes[i].parent1));
            else
                fields.push_back("");
            if (nodes[i].parent2 != -1)
                fields.push_back(xorsat::toString(nodes[i].parent2));
            else
                fields.push_back("");
            res.push_back(fields.join("\t"));
        }
        res.push_back("");
        res.push_back("Decision levels:");
        for (size_t i = 0; i < dLevels.size(); i++) {
            res.push_back(xorsat::toString(i) + ": " 
                    + xorsat::toString(dLevels[i]));
        }

        return res.join("\n");
    }


    string ImplicationGraph::toCode() const {
        size_t dl = 0;
        Split r;
        static int g =  0;
        g++;
        Split nps;
        for (size_t i = 0; i < used; i++) 
            nps.push_back(n(i));
        r.push_back("ImplicationGraph::NodePos " + nps.join(",") + ";");

        for (size_t i = 0; i < used; i++) {
            while(dl < dLevels.size() && dLevels[dl] <= (int) i) {
                r.push_back("ig.addDecisionLevel();");
                dl++;
            }
            Split params;
            const Node& node = nodes[i];
            params.push_back(xorsat::toString(node.varId));
            params.push_back(xorsat::toString(node.subVarId));
            params.push_back((node.varId > 0) ? "true" : "false");
            params.push_back(xorsat::toString(node.parent1));
            params.push_back(xorsat::toString(node.parent2));
            r.push_back(n(i) 
                    + " = ig.pushNode(ImplicationGraph::Node(" + params.join(", ")
                    + "));");
        }
        return "ig" + xorsat::toString(g) + ":"
            + r.join("\nig" + xorsat::toString(g) + ":");
    }
#endif

    string ImplicationGraph::toGraphviz() const {
        Split r;
        static int g = 0;
        g++;
        r.push_back("digraph g {");
              r.push_back("reason [ label=\"" + reasonStr + "\" shape=rectangle ];");

        int dl = 0;
        for (size_t i = 0; i < used; i++) {
            if (!nodes[i].interesting)
                continue;

            while (dl < (int) dLevels.size() && (int) i >= dLevels[dl])
                dl++;
            string label = xorsat::toString(i);
            if (!nodes[i].content.empty())
                label += " " + nodes[i].content;
            else {
                if (nodes[i].varId != 0) {
                    string m = (nodes[i].varId < 0)  ? "-" : " ";
                    label += " (" + m + "x" 
                        + xorsat::toString(abs(nodes[i].varId)) + ")";
                }
            }
            /*
            if (nodes[i].subVarId != 0) {
                label += " [x" 
                    + xorsat::toString(nodes[i].subVarId) + "]";
            }
            */
            label += " dl=" + xorsat::toString(dl);

            r.push_back(n(i) + " [ label = \"" + label + "\"" + 
                    + (reason.has(i) ? " style=filled fillcolor=darkgreen " : "" )+
                    "];");
        }
       
        for (size_t i = 0; i < used; i++) {
            if (!nodes[i].interesting)
                continue;

            if (nodes[i].parent1 != -1 && nodes[nodes[i].parent1].interesting)
                r.push_back(n(nodes[i].parent1) + " -> " + n(i) + ";");
            if (nodes[i].parent2 != -1 && nodes[nodes[i].parent2].interesting)
                r.push_back(n(nodes[i].parent2) + " -> " + n(i) + ";");


        }
/*        for (size_t i = 0; i <= dLevels.size(); i++) {

            r.push_back("subgraph cluster_dl" + xorsat::toString(i) + " {");
                
            if (i < dLevels.size()) {
                int start = 0;
                if (i > 0)
                    start = dLevels[i-1];
                for (int i2 = start; i2 < dLevels[i]; i2++) {
                    r.push_back(n(i2) + ";");
                }
            } else {
                for (size_t i2 = dLevels[dLevels.size()-1]; i2 < used; i2++) {
                    r.push_back(n(i2) + ";");

                }
            }

            r.push_back(" label=\"dl" + xorsat::toString(i) + "\";");
            r.push_back("}");;
        }*/
        r.push_back("}");
        return /*"gviz" + xorsat::toString(g) + ":"*/
             r.join("\n"/*gvz" + xorsat::toString(g) + ":"*/);
    }

}

