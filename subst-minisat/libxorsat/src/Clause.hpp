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


#ifndef _xorsat_clause_hpp_
#define _xorsat_clause_hpp_
#include <list>
#include "xorsat.hpp"
#include "Common.hpp"
#include "ImplicationGraph.hpp"
#include "HidingStack.hpp"

namespace xorsat {
    class Variable;
    class Clause;


    /** Xor-clause. A stack of variables and possibly the symbol Top.  */
    class Clause {
#ifdef DEBUG        
        /** only for checkConsistency */
        friend class SolverImplementation;
#endif 
    public:
        /** The contents of the xor-clause are stored in a  
         * stack where elements can be hidden and restored.
         * The elements are pointer to Variable objects. */
        typedef HidingStack<Variable*> Variables;

        /** for iterating the contents of the xor-clause (const) */
        typedef Variables::Iterator VariableIterator;

    private:
        /** the variable stack in the clause */
        Variables variables;

        /** the presence of the symbol top in the clause */
        bool top;

        std::vector<ImplicationGraph::NodePos> igNodes; 

        /** flag indicating whether the clause has a pending variable
         * substitution */
        bool substitution;

        /** a flag indicating whether the clause has been used as a premise
         * for propagation */
        bool propagated;

        /** declared but not defined to prevent assignment */
        const Clause& operator=(const Clause&);

    public:        
        /** creates an empty clause and assigns default values (id=0,dl=0) */
        Clause();

        /** Adds an variable (propositional variable 'v') to the clause. */
        void pushVariable(Variable* v) {
            variables.push(v);
            DBG(2, "Clause.pushVariable : " << toString());
        }

        /** Removes the variable that was added last */
        void popVariable() {
            variables.pop();
            DBG(2, "Clause.popVariable : " << toString());

        }

        /** Hides the specified variable and
         * returns an identifier the hidden variable can 
         * be unhidden with */
        int hide(Variable* what) {

            DBG(2, "Clause::hide() before : " << toString());
            int p = variables.hide(what);
            DBG(2, "Clause::hide() after  : " << toString());
            return p;
        }

        /** Unhides a variable corresponding to the specified identifier */
        void unhide(int origPos) {
            DBG(2, "Clause.unhide (" << origPos 
                    << ") before : " << toString());

            variables.unhide(origPos);
            DBG(2, "Clause.unhide after  : " << toString());


        }

        /** Associates a node of the implication graph 
         * with the xor-clause */
        void pushImplGraphNode(ImplicationGraph::NodePos np) {
            igNodes.push_back(np);
        }

        /** Returns the last associated node of the implication graph */
        ImplicationGraph::NodePos getImplGraphNode() {
            if (igNodes.empty())
                return ImplicationGraph::PremiseNode;
            return igNodes.back();
        }

        /** Removes the last association with a node of the implication graph */
        void popImplGraphNode() {
            igNodes.pop_back();
        }

        /** \return the number of non-hidden variables */
        size_t numVariables() const {
            return variables.size();
        }

        /** \return an iterator pointing to the first visible variable */
        VariableIterator beginVariables() {
            return variables.begin();
        }

        /** \return an iterator pointing to the last visible variable */
        VariableIterator endVariables() {
            return variables.end();
        }

        /** adds/removes the logical constant Top */
        void flipTop() {
            top = !top;
        }

        /** \return true, if the symbol Top is present in the xor-clause */
        bool getTop() const {
            return top;
        }

        /** \return true, if the clause is conflicting (empty) */
        bool isConflicting() const {
            return (!top && variables.size() == 0);
        }

        /** when a variable in the xor-clause is substituted
         * by another variable, the xor-clause is tagged 
         * (see SolverImplementation::substitute for details) */
        void setSubstitution(bool s) {
            substitution = s;
        }

        /** \return true, if the xor-clause contains
         * a variable that is going to be substituted with another
         * variable */
        bool getSubstitution() const {
            return substitution;
        }
       
        /** sets the flag indicating whether the xor-clause
         * has already been propagated */
        void setPropagated(bool value) {
            propagated = value;
        }

        /** \return true, if the clause has been propagated */
        bool isPropagated() const {
            return propagated;
        }



#ifdef DEBUG
        /** \return a textual representation of the clause */
        std::string toString(bool full=false) const;
#endif        
    };
}
#endif
