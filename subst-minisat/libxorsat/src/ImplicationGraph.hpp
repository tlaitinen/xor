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


#ifndef _xorsat_implicationgraph_hpp_
#define _xorsat_implicationgraph_hpp_
#include <list>
#include <set>
#include <queue>
#include "xorsat.hpp"
#include "Common.hpp"
#include "IntSet.hpp"
#include <cstdlib>
namespace xorsat {
    /** Implication graph that stores minimal information about the 
     * computation of xor-clauses in order to calculate reasons
     * for conflicts and implied literals */

    class ImplicationGraph {    

    public:
        /** nodes are indexed by integers (see \ref IntSet) */
        typedef int NodePos;

        /** special value for nodes that are premises (not stored in the 
         * graph) */
        enum { PremiseNode = -1 };


        /** node in the implication graph, stores indexes to its
         * parent nodes and possibly a literal if the corresponding
         * xor-clause is simple or the node corresponds to a decision literal */
        struct Node {
            /** if nonzero, encodes a literal. Absolute value references
             * a variable. Sign tells whether the literal is negative
             * or not. */
            VariableId varId;

            /** if nonzero, encodes a variable instance that was substituted
             * by another variable */
            VariableId subVarId;

            /** left-hand side parent */
            NodePos parent1;

            /** right-hand side parent */
            NodePos parent2;

            /** how many times the node has been explained */
            unsigned int timeStamp;

            bool redundant;

            /** constructor for nodes that contain a literal */
            Node(VariableId varId_, 
                 VariableId subVarId_,
                 bool value,
                 NodePos parent1_, 
                 NodePos parent2_)
                : varId(varId_ * (value ? 1 : -1)),
                  subVarId(subVarId_),
                  parent1(parent1_),
                  parent2(parent2_),
                  timeStamp(0) {
                  }

            /** allocates empty node (needed to store nodes in vector) */
            Node() : varId(0), subVarId(0),
                parent1(PremiseNode), parent2(PremiseNode),
                timeStamp(0){}

            /** constructor for nodes that do not contain a literal */
            Node(NodePos parent1_,
                 NodePos parent2_) 
                : varId(0), subVarId(0),
                  parent1(parent1_),
                  parent2(parent2_),
                  timeStamp(0) {}

        };
    private:      
        /** indicates how many elements are in use in vectors
         * 'nodes', and 'toExplain' */
        size_t used;

        /** a non-shrinking vector that stores the nodes of the implication
         * graph */
        std::vector<Node> nodes;

        /** lazy vector that stores decision level boundaries (the indices
         * to the first nodes on the decision levels) */
        std::vector<NodePos> dLevels;

        /** a flag-array for speeding up the calculation of the reason set
         * (see ImplicationGraph::justify) */

        std::vector<NodePos> varNodeMap;

        std::vector<char> toExplain;
        /** a cached value indicating how many non-zero elements
         * there are in 'toExplain' */
        int numToExplain;

        /** current explanation timestamp */
        unsigned int currentTime;

        NodePos checkingRedundant;

        /** stores the active reason set */
        IntSet reason;

        /** literals of the reason set */
        IntSet reasonLits;

        /** stores the variables that participated in the derivation
         * of the justified node */
        std::vector<VariableId> participated;

        /** indicates how many nodes there are in the reason set on the last 
         * decision level level 
         *  (the level of the node being explained) */
        int onLastLevel;

        /** indicates the index of the first node on the last decision level
         * (the level of the node being explained) */
        int firstOnLastLvl;

        /** the index of the first node in the reason set */
        NodePos firstReasonNode;

        /** counter for tracking the number of redundant literals
         * removed */
        long long numRedundantLiterals;

        /** counter for tracking the number of explanations computed */
        long long numJustified;

        long long evenParityEliminated;

        bool deepCut;

        /** does DFS search up to 'firstReasonNode' and returns true
         * if the node can be removed from the reason set */
        bool isRedundant(NodePos n);

        /** expands one node of the reason set */
        void explain(NodePos n);

        /** constructs a reason set for the node (index 'np')
         * and leaves the result in 'reason' */
        void dfsExplain(NodePos n);
        
        

    public:
        /** assigns fields */
        ImplicationGraph() : used(0), numToExplain(0),   
                             currentTime(0),
                             numRedundantLiterals(0),
                             numJustified(0),
        evenParityEliminated(0), deepCut(false) {}

        /** allocates memory for handling the specified number
         * of variables */
        void setup(size_t numVars) {
            size_t size = (1 + numVars) * 2;
            if (reasonLits.size() < size) {

                DBG(1, "reason allocated for " << size);
                reasonLits.setup(size);
            }
            varNodeMap.resize(numVars+1);

        }

        /** adds a new decision level boundary. nodes added after
         * this call will belong to the decision level */
        void addDecisionLevel() {
            dLevels.push_back(used);
        }

        /** adds a node to the implication graph */
        NodePos pushNode(const Node& node) {
            DBG(1, "implGraph.pushNode");

            NodePos p = used;
            if (used < nodes.size()) {
                nodes[used] = node;
                toExplain[used] = false;
            }
            else {
                nodes.push_back(node);
                toExplain.push_back(false);
            }
            if (node.varId != 0) {
                if (varNodeMap[abs(node.varId)] == 0) {
                    varNodeMap[abs(node.varId)] = p;
                    DBG(1, "setting varNodeMap[" << abs(node.varId) << "] = " << p);
                }
                else {
                    NodePos op = varNodeMap[abs(node.varId)];
                    if (nodes[p].varId != nodes[op].varId
                            && (nodes[p].parent1 != PremiseNode
                                || nodes[p].parent2 != PremiseNode)) {
                        nodes[p].varId = 0;
                        DBG(1, "varNodeMap already defined for " << 
                            node.varId << " clearing node " << p);

                    }
                }
                    
            }
            used++;

            return p;
        }


        /** removes 'num' last nodes from the implication graph */
        void popNodes(size_t num) {
            DBG(1, "implGraph.popNodes(" << num << ")");

            assert(num <= used);

            for (NodePos i = (NodePos) used - num; i < (NodePos) used; i++)
                if (nodes[i].varId != 0 && varNodeMap[abs(nodes[i].varId)] == i) {
                    DBG(1, "clearing varNodeMap[" << abs(nodes[i].varId) << "]");
                    varNodeMap[abs(nodes[i].varId)] = 0;
                }
            used -= num;

            while (dLevels.size() > 0
                    && dLevels[dLevels.size() - 1] 
                       >= static_cast<NodePos>(used)) {
                DBG(2, "popping decision level " << dLevels.size());
                dLevels.pop_back();
            }
            DBG(2, "used nodes : " << used);
        }

        /** builds a reason set for the requested node
         * and converts it to a disjunction 
         * \param firstUIP expands the reason set until it contains
         * the first unique implication point (and is cnf-compatible, too)
         * \param minimize if true, the reason set is minimize
         * (redundant literals are eliminated)
         * */
        void justify(Disjunction& d, NodePos target,
                     bool firstUIP, bool minimize,
                     bool evenElim,
                     bool deepCut,
                     int& numEliminated);

        const std::vector<VariableId>& getParticipated() const {
            return participated;
        }


#ifdef DEBUG
        /** \return a textual representation of the implication graph */
        std::string toString() const;


        /** \return C++ source code that reconstructs the graph */
        std::string toCode() const;
#endif        
        /** \return graphviz representation of the implication graph */
        std::string toGraphviz() const;

        /** \return the number of redundant literals removed 
         * from reasons so far */
        long long getNumRedundantLiterals() const {
            return numRedundantLiterals;
        }

        /** \return the number of calls to 'justify' */ 
        long long getNumJustified() const {
            return numJustified;

        }
        long long getEvenParityEliminated() const {
            return evenParityEliminated;
        }

    };
}
#endif
