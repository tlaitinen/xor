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


#include "UndoStack.hpp"
#include "Common.hpp"
#include "SolverImplementation.hpp"
namespace xorsat {
    UndoStack::UndoStack(ImplicationGraph& ig, SolverImplementation& s)
        : implGraph(ig), solver(s) {}

    UndoStack::~UndoStack() {
        }
#ifdef DEBUG
    void UndoStack::store() {
        history.push_back(solver.toString());
    }
#endif

    void UndoStack::backjump(BackjumpId id) {

        DBG(1, "UndoStack.backjump(" << id << ")");
        DBG(2, toString());
        assert(id >= 0);
        assert(backjumps.size() > id);
        assert(ops.size() >= backjumps[id]);
        size_t clauses = 0;
        size_t i = ops.size() - 1;
        DBG(1, "last op : " << backjumps[id]);
#ifdef DEBUG
        int bj = backjumps.size() - 1;
#endif
        if (!ops.empty())
        while (i >= backjumps[id]) {
            Operation& op = ops[i];
            DBG(1, "undo op " << i);

            switch(op.opType) {
                case Operation::ClauseOp: 
                    {
                        DBG(2, " - is clause");
                        Clause* c = op.op.clauseOp.clause;
                        if (op.op.clauseOp.flipTop) {
                            DBG(2, " - flipping top");
                            c->flipTop();
                        }

                        if (op.op.clauseOp.oldVarPos1 > -1) {
                            DBG(2, " - unhiding to position " 
                                    << op.op.clauseOp.oldVarPos1);
                            c->unhide(op.op.clauseOp.oldVarPos1);
                            if (op.op.clauseOp.oldClausePos > -1) {
                                DBG(2, " - unhiding corresponding variable "
                                        "-> clause ref to position " 
                                        << op.op.clauseOp.oldClausePos)
                                    (*(c->beginVariables() + op.op.clauseOp.oldVarPos1))
                                    ->unhideInstance(op.op.clauseOp.oldClausePos);
                            }

                        }
                        if (op.op.clauseOp.oldVarPos2 > -1) {
                            DBG(2, " - unhiding to position " 
                                    << op.op.clauseOp.oldVarPos2);
                            c->unhide(op.op.clauseOp.oldVarPos2);
                        }

                        if (op.op.clauseOp.popInstance) {
                            DBG(2, " - popping last variable instance ");
                            DBG(2, " - removing corresponding variable -> clause"
                                    " ref");
                            (*(c->endVariables() - 1))->popInstance();
                            c->popVariable();
                        }

                        c->popImplGraphNode();
                        c->setPropagated(false);
                        clauses++;

                    }
                    break;
                case Operation::HideInstances:
                    DBG(2, " - is variable");
                    DBG(2, "before op " << op.op.hideInstances.variable->toString());
                    DBG(2, " - popping instance");
                    op.op.hideInstances.variable->popInstance();
                    DBG(2, " - unhiding " << op.op.hideInstances.howMany
                            << " instances");
                    op.op.hideInstances.variable->unhideMany(op.op.hideInstances.howMany);
                    DBG(2, "after op " << op.op.hideInstances.variable->toString());
                    break;
                case Operation::PushValue:    
                    DBG(2, " - popping value");
                    op.op.pushValue.variable->popValue();
                    break;
                case Operation::PushNode:
                    DBG(2, " - popping node from implication graph");
                    implGraph.popNodes(1);
                    break;
                case Operation::PropQueue:
                    if (op.op.propQueue.push) {
                        DBG(2, " - returning a clause to a propagation queue");
                        op.op.propQueue.queue->push_front(op.op.propQueue.clause);
                    } else {
                        DBG(2, " - popping a clause from a propagation queue");
                        op.op.propQueue.queue->pop_back();
                    }
                    break;
                case Operation::AssignQueue:    
                    if (op.op.assignQueue.push) {
                        DBG(2, " - returning a clause to the assignment queue");
                        op.op.assignQueue.queue->push_front(
                                Literal(op.op.assignQueue.id,
                                        op.op.assignQueue.negative));
                    } else {
                        DBG(2, " - popping a clause from the assignment queue");
                        op.op.assignQueue.queue->pop_back();
                    }
                    break;
                case Operation::ResetImplied:
//                    op.op.resetImplied.variable->resetImplied();
                    break;


            };


#ifdef DEBUG
            while (backjumps[bj] > i && bj > 0)
                bj--;
            if (i == backjumps[bj]) {
                if (solver.toString() != history[bj]) {
                    DBG(2, "AFTER UNDO : ");
                    DBG(2, solver.toString());
                    DBG(2, "----------------------------");
                    DBG(2, "ORIGINAL : ");
                    DBG(2, history[bj]);
                }
                assert(solver.toString() == history[bj]);

            }
#endif
            
            if (i == backjumps[id])
                break;
            assert(i > 0);
            i--;
            

        }

        implGraph.popNodes(clauses);
        ops.resize(backjumps[id]);
        backjumps.resize(id);        
#ifdef DEBUG
        history.resize(id);
#endif

    }

#ifdef DEBUG
    std::string UndoStack::toString() const {
        Split r;
        size_t bj = 0;
        for (size_t i = 0; i < ops.size(); i++) {
            while (bj < backjumps.size() && backjumps[bj] == i) {
                    r.push_back("Backjump " + xorsat::toString(bj));
                    bj++;
            }
            Split f;
            const Operation& op = ops[i];
            f.push_back(xorsat::toString(i));
            if (op.opType == Operation::ClauseOp) {
                f.push_back("c:"+op.op.clauseOp.clause->toString(true));
                if (op.op.clauseOp.flipTop)
                    f.push_back("flipTop");


                f.push_back(xorsat::toString(op.op.clauseOp.oldVarPos1));
                f.push_back(xorsat::toString(op.op.clauseOp.oldVarPos2));


                if (op.op.clauseOp.popInstance)
                    f.push_back("popVariable");
                if (op.op.clauseOp.oldClausePos > -1)
                    f.push_back("updateVar");

            }
            else if (op.opType == Operation::HideInstances) {
                f.push_back("x" + xorsat::toString(op.op.hideInstances.variable->getId()));
                f.push_back("popInstances + unhideMany");
            }
            else if (op.opType == Operation::PushValue) {
                f.push_back("x" + xorsat::toString(op.op.pushValue.variable->getId()));
                f.push_back("popValue");
            }
            else if (op.opType == Operation::PushNode) {
                f.push_back("");
                f.push_back("popNode");
            } else if (op.opType == Operation::AssignQueue) {
                f.push_back("");
                f.push_back("assignQueue");
                f.push_back("push=" + xorsat::toString(op.op.assignQueue.push));
                f.push_back(std::string(op.op.assignQueue.negative ? "~" : "") + 
                         "x" + xorsat::toString(op.op.assignQueue.id));
            } else if (op.opType == Operation::PropQueue) {
                f.push_back("");
                f.push_back("propQueue");
                f.push_back("push=" +  xorsat::toString(op.op.propQueue.push));
                f.push_back(op.op.propQueue.clause ? op.op.propQueue.clause->toString(true) : "");
            }

            r.push_back(f.join("\t"));            
        }
        if (bj < backjumps.size() && backjumps[bj] == ops.size())
            r.push_back("Backjump " + xorsat::toString(bj));

        return r.join("\n");
    }
#endif


}

