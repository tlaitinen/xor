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


#ifndef _xorsat_solverimplementation_hpp_
#define _xorsat_solverimplementation_hpp_
#include <vector>
#include <map>
#include <list>
#include <queue>
#include <deque>
#include "xorsat.hpp"
#include "Variable.hpp"
#include "Clause.hpp"
#include "UndoStack.hpp"
#include "Split.hpp"
#include "ImplicationGraph.hpp"
#include "LazyQueue.hpp"
namespace xorsat {
    /** The implementation of the Xor-solver. The class implements
     * the methods declared by the abstract library interface. */
    class SolverImplementation : public Solver {
        typedef std::list<Variable> Variables;
        typedef std::list<Clause> Clauses;
        typedef std::vector<Variable*> VariableRefs;
        typedef std::deque<Clause*> PropagationQueue;
        typedef std::deque<Literal> AssignQueue;

        /** The list of propositional variables */
        Variables variables;

        /** Array of variable references for constant-time access to the
         * variables by a numeric identifier */
        VariableRefs variableRefs;

        /** The xor-clauses known by the solver */
        Clauses clauses;

        /** The operation stack records all the operations on the 
         * data structures of the solver. The operations can be
         * inspected for conflict analysis and undone when returning
         * to a previously recorded backjump point. */
        UndoStack undoStack;

        /** Propagation queue for external assignments */
        AssignQueue toAssign;

        /** Propagation queues, the xor-clauses that might be used to
         * derive new xor-clauses */
        PropagationQueue toUnitPropagate, toEqvPropagate;

        /** The first unused variable identifier */
        VariableId variableSeq;

        /** The conflicting xor-clause. It is
         * null if there is no conflict. */
        Clause* conflictClause;

        /** If not empty, the Gauss elimination deemed the
         * instance unsatisfiable */
        Disjunction trivialConflict;

        /** Implied literals only */
        LazyVector<Literal> impliedLiterals;

        /** When the conflict clause is being built, the intermediate
         * version is stored in a conflict set */
        ImplicationGraph implGraph;

        /** the current decision level, corresponds to the number
         * of assigned variables */
        DecisionLevel decisionLevel;

        /** size of the undo stack before any operation has been made */
        size_t initialUndoStackSize;

        /** first user set backjump point */
        BackjumpId firstBackjumpId;

        /** true when the solver has done pre-propagation*/
        bool prePropagated;

        /** true when the solver is doing propagation before any assignments */
        bool prePropagation;

        /** total number of propagation steps done */
        long long numUnitPropagationSteps, numEqvPropagationSteps,
            numAssigns;



#ifdef DEBUG        
        /** prefix of the graphviz implication graph */
        static int graphNumber;

        /** checks the consistency of all data structures (slow) and
         * terminates if the data structures are not consistent */
        void checkConsistency();
#endif

        /** checks whether an inference rule (unit propagation, equivalence) 
         *  can be applied and applies one or more if possible
         *  starting with the xor-clause 'clause' and records
         *  operations to UndoStack.
         *  \return a pointer to a conflicting xor-clause
         *  or NULL if there is no conflict */
        Clause* propagate(Clause* clause);

        /** empties unit and equivalence propagation queues
         * or returns a conflicting xor-clause */
        Clause* doPropagation();
    
        /** extracts a reason for an implied literal and adds
         * it to the list of implications. works in the same way
         * as SolverImplementation::buildConflictSet */
        void extractImplication(Clause* clause);


        /** performs initial propagation for all clauses with one or
         * two variable instances
         * \return a conflicting xor-clause or NULL if none exists */
        Clause* prePropagate();

        /** checks if a xor-clause can be added to the propagation
         * queue, that is the number of visible variables is one or two
         * and the xor-clause has not been propagated yet. */
        void checkPropagation(Clause* clause);


        void buildTrivialConflictClause(Disjunction& d);

        void modifyClause(Clause* clause, ImplicationGraph::NodePos reason,
                          VariableId subVarId);

        /** hides the instances of the variable and
         * flips the Top-symbols according to the value 
         * \param undo if true, then the operation is undone
         * \return a conflicting xor-clause or NULL */
        Clause* doAssign(Clause* reason, 
                         ImplicationGraph::NodePos reasonNode,
                         Variable* variable, 
                         bool value);

        /** substitutes all instances of the Variable 'what'
         * by the other Variable 'with'. 
         * \param negation if true, then the Top symbol is flipped
         * in all clauses where the substitution is done
         * \param undo if true, then the operation is undone
         * \return a pointer to a conflicting xor-clause or NULL
         * if there is no conflict */
         Clause* substitute(Clause* reason, 
                            ImplicationGraph::NodePos reasonNode,
                            Variable* what, 
                            Variable* with,
                            bool negation);


        /** picks a queued assignment from the assignment queue
         * and propagates it */
        Clause* assign();
    public:
#ifdef DEBUG
        /** \return a textual representation of the state of the solver */
        virtual std::string toString() const;

#endif  
        bool is_sat() const {
            return conflictClause != NULL;
        }

        /** assigns default values */
        SolverImplementation();

        /** prints debug information */
        ~SolverImplementation();

        /** See Solver::addVariable */
        VariableId addVariable();

        /** See Solver::setInternal */
        void setInternal(VariableId varId);

        /** See Solver::addClause */
        void addClause(const std::vector<VariableId>& clause);

        /** See Solver::setBackjump */
        BackjumpId setBackjump();

        /** See Solver::backjump */
        void backjump(BackjumpId id);

        /** See Solver::reset */
        void reset();

        /** See Solver::assign */
        void assign(VariableId id, bool value);

        /** See Solver::propagate */
        AssignResult propagate();

        /** See Solver::solve */
        bool solve();

        /** See Solver::explain */
        void explain(Disjunction& d);

        /** See Solver::getImplications */
        const LazyVector<Literal>& getImplications() const;

        /** See Solver::justify */
        void justify(Disjunction& impl, Literal lit);

        const LazyVector<VariableId>& getParticipated() const {
            return implGraph.getParticipated();
        }
        /** \return the number of propagation steps */
        long long getNumPropagationSteps() const;

        /** \return the number of unit propagation steps */
        long long  getNumUnitPropagationSteps() const;

        /** \return the number of equivalence propagations steps */
        long long getNumEqvPropagationSteps() const;

        /** \return the number of assignments */
        long long getNumAssigns() const;

        /** \return the number of eliminated literals */
        long long getNumRedundantLiterals() const {
            return implGraph.getNumRedundantLiterals();
        }

        /** \return the number of justifications computed */
        long long getNumJustified() const {
            return implGraph.getNumJustified();
        }

        /** \return the implication graph as a graphviz input string */
        std::string getGraphviz() {
            return implGraph.toGraphviz();
        }


    };
}
#endif
