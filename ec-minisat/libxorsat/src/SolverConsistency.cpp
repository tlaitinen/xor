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


#include "SolverImplementation.hpp"
#include <list>
using namespace std;
namespace xorsat {
#ifdef DEBUG    
    void SolverImplementation::checkConsistency() {
        DBG(2, "Solver state:");
        DBG(2, toString());
        DBG(2, "Implication graph:");
        DBG(2, implGraph.toString());
        DBG(2, "Undo stack:");
        DBG(2, undoStack.toString());


        // CHECK: variableRefs references point to correct variables
        // excluding deleted variables
        VariableId vid = 0;
        for (vector<Variable*>::iterator i = variableRefs.begin();
                i != variableRefs.end(); i++) {
            if (vid == 0)
                assert((*i) == NULL);
            else if (*i != NULL)
                assert((*i)->getId() == vid);
            vid++;                        
        }



        // CHECK: variables of the clauses are known by the solver
        set<Variable*> knownVariables;
        for (std::list<Variable>::iterator v = variables.begin();
                v != variables.end(); v++) {
            if (undoStack.size() == 0)
                assert(v->isAssigned() == false);
            knownVariables.insert(&(*v));

        }



        // CHECK: clauses referenced by the variables are known by the solver
        set<Clause*> knownClauses;
        for (std::list<Clause>::iterator c = clauses.begin();
                c != clauses.end(); c++) {
            knownClauses.insert(&(*c));

        }

        
        // CHECK: variable -> clause relation ok?
        for (std::list<Variable>::iterator v = variables.begin();
                v != variables.end(); v++) {
            if (v->isAssigned() == false)
            for (Variable::InstanceIterator i = v->beginInstances(); 
                    i != v->endInstances(); i++) {
                Clause* c = *i;
                assert(knownClauses.find(c) != knownClauses.end());
                bool foundVariableInClause = false;
                for (Clause::VariableIterator vi = c->beginVariables();
                        vi != c->endVariables(); vi++) {
                    assert(knownVariables.find(*vi) != knownVariables.end());

                    if (*vi == &(*v)) {
                        foundVariableInClause = true;
                        break;
                    }
                        
                }
                if (!foundVariableInClause) {
                    DBG(1, "Did not find clause " << c->toString()
                            << " in variable " << v->toString());
                }
                assert(foundVariableInClause);
            }


        }

        // CHECK: clause -> variable relation ok?
        for (std::list<Clause>::iterator c = clauses.begin();
                c != clauses.end(); c++) {
            for (Clause::VariableIterator vi = c->beginVariables(); 
                    vi != c->endVariables(); vi++) {
                Variable* v = *vi;
                assert(knownVariables.find(v) != knownVariables.end());
                bool foundClauseInVariable = false;
                for (Variable::InstanceIterator i = v->beginInstances();
                        i != v->endInstances(); i++) {
                    assert(knownClauses.find(*i) != knownClauses.end());

                    if (*i == &(*c)) {
                        foundClauseInVariable = true;
                        break;
                    }
                        
                }
                if (!foundClauseInVariable) {
                    DBG(1, "Could not find a reference from the variable " 
                            << v->toString() << " to clause "
                            << c->toString(true));
                }
                assert(foundClauseInVariable);
            }


        }


        // CHECK: the pending substitution queues in clauses are empty.
        // The queues are used only by SolverImplementation::substitute(...)
        for (std::list<Clause>::iterator c = clauses.begin();
                c != clauses.end(); c++) {

          assert(c->getSubstitution() == false);
        }      
        
        



       
    }
#endif
}
