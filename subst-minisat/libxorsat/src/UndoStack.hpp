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


#ifndef _xorsat_undostack_hpp_
#define _xorsat_undostack_hpp_
#include <list>
#include "xorsat.hpp"
#include "ImplicationGraph.hpp"
#include "Split.hpp"
namespace xorsat {
    class Clause;
    class Variable;
    class SolverImplementation;

    /** Operation stack for recording modifications to the data
     * structures of the solver. The class undoes the modifications
     * when requested. */
    class UndoStack {
#ifdef DEBUG        
    public:
#endif

    private:
        /**
         * Atomic operation to be undone. */

        struct Operation {
            enum { ClauseOp,
                   PushValue,
                   HideInstances,
                   PushNode,
                   PropQueue,
                   AssignQueue
            };
                  
            /** operation type field */
            unsigned char opType;


            Operation() : opType(0) {}

            Operation(unsigned char ot) 
                : opType(ot) {}

            union {
                struct {
                    /** this field points to a  xor-clause */
                    Clause* clause;

                    /** for clause operations, if set, the top symbol will be
                     * flipped */
                    unsigned char flipTop:1;
        
                    /** if this field is set, then a variable
                     * reference from the clause will be popped. Also, the
                     * corresponding variable -> clause reference will be
                     * popped.  Otherwise, this field does nothing */
                    unsigned char popInstance:1;

                    /** when hiding a variable reference from a clause, the old
                     * position of the variable reference in the hiding stack
                     * is stored to this field */
                    int oldVarPos1;

                    /** for substitute operations, two variables can be hidden
                     * so this field corresponds to the old position of the
                     * second hidden variable reference */
                    int oldVarPos2;

                    /** when hiding a clause reference from a variable,
                     * the old position of the clause reference in the hiding
                     * stack is stored to this field */
                    int oldClausePos;
                } clauseOp;

                struct {
                    /** the variables whose instances were hidden */
                    Variable* variable;

                    /** how many instances were hidden */
                    int howMany;
                } hideInstances;

                struct {
                    /** the variable that got a new value */
                    Variable* variable;
                } pushValue;

                struct {
                    /** the assignment queue */
                    std::deque<Literal>* queue;

                    /** if true, then a literal was pushed to the queue,
                     * otherwse a literal was popped from the queue */
                    bool push;

                    /** the variable of the literal */
                    VariableId id;

                    /** the sign of the literal */
                    bool negative;
                } assignQueue;

                struct {
                    /** the propagation queue */
                    std::deque<Clause*>* queue;

                    /** if true, a xor-clause was pushed to the queue,
                     * otherwise if was popped from the queue */
                    bool push;

                    /** the xor-clause */
                    Clause* clause;
                } propQueue;
            } op;
        };


        /** the operations are stored in a vector */
        typedef std::vector<Operation> Operations;

        /** the backjump points are stored in a vector */
        typedef std::vector<size_t> BackjumpPoints;

        /** reference to the implication graph (to pop nodes) */
        ImplicationGraph& implGraph;

        /** reference to the solver (for debugging purposes) */
        SolverImplementation& solver; 

        /** recorded operations to undo */
        Operations ops;
        
        /** backjump points point to positions in 'ops' vector */
        BackjumpPoints backjumps;

#ifdef DEBUG        
        /** the solver state after each operation is stored in debug-mode */
        Split history;
#endif

        /** pushes an operation to the operation stack */
        void pushOp(const Operation& op) {
            ops.push_back(op);
        }

    public:        
        /** assigns fields */
        UndoStack(ImplicationGraph& ig,
                SolverImplementation& s);

        /** frees operation objects */
        ~UndoStack();
#ifdef DEBUG
        void store();
#endif

       
        /** The method stores information to undo a variable assignment.
         * When a variable is assigned, references from xor-clauses
         * to the variable are hidden (in clauses' HidingStacks, \ref HidingStack)
         * and possibly the symbol Top is flipped. One record for
         * each clause is stored in UndoStack. 'oldVarPos' is used to
         * restore the hidden variable to its original place in HidingStack. */
        void recordAssign(Clause* clause, 
                          bool flipTop, 
                          int oldVarPos) {
            DBG(1, "recordAssign(" 
                    << ", flipTop=" << flipTop
                    << ", oldVarPos=" << oldVarPos << ")");
            Operation op(Operation::ClauseOp);
            op.op.clauseOp.clause = clause;
            op.op.clauseOp.flipTop = int(flipTop);
            op.op.clauseOp.oldVarPos1 = oldVarPos;
            op.op.clauseOp.oldVarPos2 = -1;
            op.op.clauseOp.oldClausePos = -1;
            op.op.clauseOp.popInstance = 0;
            pushOp(op);

        }

        /** The method stores information to undo a variable substitution.
         * When a variable is substituted with another variable,
         * references from xor-clauses to the variable are hidden
         * and references to the other variable are either
         * added or removed depending on the presence of the first
         * variable in the xor-clause. Also, the symbol Top may
         * be flipped. This method is for substitutions
         * that hide both variable instances from the xor-clause. */
        void recordSubstitute(Clause* clause,
                              bool flipTop,
                              int oldVarPos1,
                              int oldVarPos2,
                              int oldClausePos) {
            Operation op(Operation::ClauseOp);
            op.op.clauseOp.clause = clause;
            op.op.clauseOp.flipTop = int(flipTop);
            op.op.clauseOp.oldVarPos1 = oldVarPos1;
            op.op.clauseOp.oldVarPos2 = oldVarPos2;
            op.op.clauseOp.oldClausePos = oldClausePos;
            op.op.clauseOp.popInstance = 0;
            pushOp(op);
        }

        /** Like above, this method stores information to undo 
         * a variable substitution but for cases when a new
         * instance of the other variable is added */
        void recordSubstitute(Clause* clause,
                              bool flipTop,
                              int oldVarPos) {
            Operation op(Operation::ClauseOp);
            op.op.clauseOp.clause = clause;
            op.op.clauseOp.flipTop = int(flipTop);
            op.op.clauseOp.oldVarPos1 = oldVarPos;
            op.op.clauseOp.oldVarPos2 = -1;
            op.op.clauseOp.oldClausePos = -1;
            op.op.clauseOp.popInstance = 1;
            pushOp(op);
        }                                  

        /** The method stores information to undo a pushValue-operation
         * which stores the value of a variable*/
        void recordPushValue(Variable* variable) {

            DBG(1, "recordPushValue()");
            Operation op(Operation::PushValue);
            op.op.pushValue.variable = variable;
            pushOp(op);
        }

        /** The method stores information to undo hiding of all instances
         * of a variable and then adding one instance */
        void recordHideInstances(Variable* variable, int howMany) {
            DBG(1, "recordHideMany()");
            Operation op(Operation::HideInstances);
            op.op.hideInstances.variable = variable;
            op.op.hideInstances.howMany = howMany;
            pushOp(op);
        }

        /** This method stores information to remove nodes from the implication
         * graph (inverse of pushNode) */
        void recordPushNode() {
            DBG(1, "UndoStack.recordPopNode()");
            pushOp(Operation(Operation::PushNode));

        }

        /** This method stores information to pop an element from a propagation 
         * queue */
        void recordPushQueue(std::deque<Clause*>* queue) {
            Operation op(Operation::PropQueue);
            op.op.propQueue.queue = queue;
            op.op.propQueue.push = false;
            op.op.propQueue.clause = NULL;
            pushOp(op);

        }

        /** This method stores information to return an element to a propagation 
         * queue */
        void recordPopQueue(std::deque<Clause*>* queue, Clause* clause) {
            Operation op(Operation::PropQueue);
            op.op.propQueue.queue = queue;
            op.op.propQueue.push = true;
            op.op.propQueue.clause = clause;
            pushOp(op);

        }

        /** This method stores information to pop an element from the assignment
         * queue */
        void recordPushQueue(std::deque<Literal>* queue) {
            Operation op(Operation::AssignQueue);
            op.op.assignQueue.queue = queue;
            op.op.assignQueue.push = false;
            op.op.assignQueue.id = 0;
            op.op.assignQueue.negative = false;
            pushOp(op);

        }

        /** This method stores information to return an element to the assignment
         * queue */
        void recordPopQueue(std::deque<Literal>* queue, Literal lit) {
            Operation op(Operation::AssignQueue);
            op.op.assignQueue.queue = queue;
            op.op.assignQueue.push = true;
            op.op.assignQueue.id = lit.variable;
            op.op.assignQueue.negative = lit.negative;
            pushOp(op);
        }


        /** This method adds a backjump point that records a consistent
         * state of the solver which can be restored later on */
        BackjumpId addBackjump() {
#ifdef DEBUG
            store();
#endif

            backjumps.push_back(ops.size());
            return backjumps.size() - 1;
        }

        /** The method undoes all the operations done after the specified
         * backjump point and restores the state of the solver */
        void backjump(BackjumpId id);

        /** \return the number of operations in the undo stack */
        size_t size() const {
            return ops.size();
        }
#ifdef DEBUG
        std::string toString() const;
#endif
    };
}
#endif
