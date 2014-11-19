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


#ifndef _xorsat_variable_hpp_
#define _xorsat_variable_hpp_
#include <list>
#include <cassert>
#include "xorsat.hpp"
#include "ImplicationGraph.hpp"
#include "HidingStack.hpp"

namespace xorsat {
    /** Forward reference */
    class Clause;

    /** Variable in a xor-clause. The class maintains references to
     * instances of the variables.  */
    class Variable {
    public:        
        typedef HidingStack<Clause*> Instances;
        typedef Instances::Iterator InstanceIterator;

    private:

        /** unique identifier of the variable */
        VariableId id;

        /** The occurences of the variable 
         * (the clauses where the variable is present) */
        Instances instances;

        /** Truth assignments of the variable (valid, if assigned) */
        std::vector< std::pair<bool, DecisionLevel> > values;

        /** the decision level of the solver when the variable was
         * assigned */
        DecisionLevel decisionLevel;

        /** flag indicating whether the truth assignments of the variable
         * are conflicting */
        size_t conflictPos;

        /** boolean flags in a bit-field structure to save memory */
        struct {
            /** if true, then the variable is a decision variable
             * (see Variable::markDecisionVariable) */
            unsigned char decisionVariable:1;

            /** if true, then the variable is implied, i.e. its value
             * was inferred from other xor-clauses */
            unsigned char implied:1;

            /** if true, the variable has occurrences only in xor-clauses */
            unsigned char internal:1;
        } flags;

        ImplicationGraph::NodePos igNode;

        /** the xor-clause that inferred the value of the variable
         * (or NULL) */
        Clause* implyingClause;

        /** declared but not defined to prevent assignment */
        const Variable& operator=(const Variable&);
    public:    

        /** assigns default values */
        Variable(VariableId id);

        /** adds an instance of the variable meaning that the
         * variable occurs in a xor-clause. */
        void pushInstance(Clause* clause) {
            instances.push(clause);
        }

        /** pops a previously added instance of the variable. */
        void popInstance() {
            instances.pop();
        }

        /** hides all occurrences of the variable,
         *  returns the number of instances hidden */
        int hideInstances() {
            return instances.hideAll();
        }

        /** restores the specified number of hidden occurrences */
        void unhideMany(int howMany) {
            instances.unhideMany(howMany);
        }

        /** hides an occurrence of the variable at the specified location,
         * returns the original position */
        int hideInstance(InstanceIterator i) {
            return instances.hide(i);
        }

        /** \return the number of active instances */
        size_t numInstances() const {
            return instances.size(); 
        }

        /** restores a hidden occurrence to the specified original position */
        void unhideInstance(int origPos) {
            instances.unhide(origPos);
        }

        /** \return an iterator pointing to the first instance
         * of the variable (in the xor-clauses) */
        InstanceIterator beginInstances() {
            return instances.begin();
        }

        /** \return an iterator pointing to the end()-element of
         * the container of the instances of the variable */
        InstanceIterator endInstances() {
            return instances.end();
        }

        /** \return true, if the variable has been assigned at least once*/
        bool isAssigned() const {
            return !values.empty();
        }

        /** \return true, if the variable has conflicting assignments */
        bool isConflicting() const {
            return conflictPos > 0;
        }

        /** sets the corresponding node of the implication graph */
        void setImplGraphNode(ImplicationGraph::NodePos np) {
            igNode = np;
        }

        /** \return the corresponding node of the implication graph */
        ImplicationGraph::NodePos getImplGraphNode() {
            return igNode;
        }

        /** adds a truth value assignment for the variable */
        void pushValue(bool value_, DecisionLevel level) {
            if (!values.empty() && value_ != getValue())
                conflictPos = values.size();

            values.push_back(std::make_pair(value_, level));
        }

        /** \return the value of the last truth assignment */
        bool getValue() const {
            assert(!values.empty());
            return values.back().first;
        }

        /** labels the variable as decision variable, that is,
         * a variable whose value has been assigned outside
         * the xor solver */
        void markDecisionVariable() {
            flags.decisionVariable = 1;
        }

        /** \return true, if the variable is a decision variable */
        bool isDecisionVariable() const {
            return flags.decisionVariable;
        }

        /** tags the variable as implied, i.e. it's value was inferred
         * from other xor-clauses, and marks it processed.*/
        void markImplied() {
            flags.implied = 1;
        }

        /** \return true, if the variable is implied */
        bool isImplied() const {
            return flags.implied;
        }

        /** tags the variable as internal, i.e., it has no occurrences
         * outside xor-clauses */
        void markInternal() {
            flags.internal = 1;
        }

        bool isInternal() const {
            return flags.internal;
        }

        /** pops a previously added truth value assignment 
         * and resets the decision variable-status if the 
         * first assignment is popped */
        void popValue() {
            values.pop_back();
            if (conflictPos == values.size())
                conflictPos = 0;
            if (values.empty()) {
                flags.decisionVariable = 0;
                flags.implied = 0;
                implyingClause = NULL;
            }

        }

        /** \return the unique identifier of the variable */
        int getId() const {
            return id;
        }

        void setImplyingClause(Clause* clause) {
            implyingClause = clause;
        }

        Clause* getImplyingClause() const {
            return implyingClause;
        }
#ifdef DEBUG
        /** \return a textual representation of the variable */
        std::string toString() const;
#endif
    };
}
#endif
