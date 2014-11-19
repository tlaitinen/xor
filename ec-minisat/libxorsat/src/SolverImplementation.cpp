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


#include "Common.hpp"
#include "SolverImplementation.hpp"
#include "Gauss.hpp"
#include <cassert>
#include <algorithm>
using namespace std;
namespace xorsat {
#ifndef DEBUG
#define checkConsistency() 
#endif
#ifdef DEBUG
    int SolverImplementation::graphNumber = 1;
#endif
    Clause* SolverImplementation::propagate(Clause* clause) {
        if (clause->isPropagated())
            return NULL;
        DBG(2, "propagate(" << clause->toString() << ")");
        size_t numVars = clause->numVariables();
        if (numVars == 0)
            return NULL;
        if (numVars > 2)
            return NULL;
        assert(numVars >= 1 && numVars <= 2);
        if (numVars == 1) {
            clause->setPropagated(true);

            // a unit literal has been inferred -> extract an implication
            // if an implication for the variable has not been extracted
            // yet
            Variable* v = *clause->beginVariables();
            DBG(2, "variable " << v->toString());
            if (clause->getImplGraphNode() != ImplicationGraph::PremiseNode
                    && v->isAssigned() == false 
                    && v->isImplied() == false
                    && v->isInternal() == false) {
                    
                DBG(2, "implied literal : " << clause->toString());
                v->markImplied();
                bool negative = clause->getTop();
                Variable* v = *clause->beginVariables();
                Literal lit(v->getId(), negative);
    
                impliedLiterals.push_back(lit);
                v->setImplyingClause(clause);
                
            }


            // XOR-Unit inference rule
            DBG(2, "Applying XOR-Unit");

            if (v->isAssigned() == false) {
                bool value = !clause->getTop();
                numUnitPropagationSteps++;
                return doAssign(clause, clause->getImplGraphNode(),
                                v, value);
            } else
                return NULL;
        } else {
            clause->setPropagated(true);

            // XOR-Eqv inference rule
            DBG(2, "Applying XOR-Eqv");
            Clause::VariableIterator vi = clause->beginVariables();
            Variable* what = *vi;
            DBG(2, "Got variable what " << what->getId());
            vi++;
            Variable* with = *vi;

            DBG(2, "Got variable with " << with->getId());

            vi++;
            assert(vi == clause->endVariables());
            
            bool negation = !clause->getTop();
            assert(what->isAssigned() == false);
            assert(with->isAssigned() == false);
            if (what->isAssigned() == false) {

                if (what->numInstances() > with->numInstances()) {
                    Variable* tmp = what;
                    what = with;
                    with = tmp;
                }
                numEqvPropagationSteps++;

                return substitute(clause, clause->getImplGraphNode(),
                                  what, with, negation);
            } else
                return NULL;
        }

        return NULL;
    }

    
    void SolverImplementation::buildTrivialConflictClause(Disjunction& d) {
        d.literals.clear();
        for (Variables::iterator v = variables.begin(); 
                v != variables.end(); v++) {
            if (v->isDecisionVariable()) {
                assert(v->isAssigned() == true);
                VariableId vid = v->getId();
                bool negative = v->getValue();
                d.literals.push_back(Literal(vid, negative));
            }

        }
        if (d.literals.empty())
            d.literals.push_back(Literal(0, true));
        
    }

    Clause* SolverImplementation::prePropagate() {
        for (Clauses::iterator c = clauses.begin(); c != clauses.end();
                c++) {
            size_t numVars = c->numVariables();
            if (numVars >= 1 && numVars <= 2) {
                Clause* conflict = propagate(&(*c));
                if (conflict) 
                    return conflict;
            }
        }
        return NULL;
    }

    void SolverImplementation::checkPropagation(Clause* clause) {
        size_t numVars = clause->numVariables();
        if (numVars >= 1 && numVars <= 2) {
            DBG(2, "   checkPropagation, numVariables = " << numVars);

            if (clause->isPropagated() == false) {
                DBG(2, "    adding " << clause->toString()
                        << " to propagation queue");
                if (numVars == 1) {
                    undoStack.recordPushQueue(&toUnitPropagate);
                    toUnitPropagate.push_back(clause);
                }
                else {
                    undoStack.recordPushQueue(&toEqvPropagate);
                    toEqvPropagate.push_back(clause);
                }
            } else {
                DBG(2, "    already propagated : " 
                        << clause->toString());
            }
        }

    }
#ifdef DEBUG
    string SolverImplementation::toString() const {

        Split r;
        r.push_back("  Variables:");
        for (Variables::const_iterator v = variables.begin();
                v != variables.end();
                v++) {
            r.push_back("    " + v->toString());
        }
//        r.push_back("  Decision level: " + xorsat::toString(decisionLevel));
        r.push_back("  Clauses:");
        for (Clauses::const_iterator c = clauses.begin();
                c != clauses.end();
                c++) {
            r.push_back("    " + c->toString(true));
        }
        r.push_back("  Assign queue:");
        for (AssignQueue::const_iterator i = toAssign.begin();
                i != toAssign.end(); i++) {
            r.push_back("    " + string(i->negative ? "-x" : "x") 
                    + xorsat::toString(i->variable));
        }
        r.push_back("  Unit propagation queue:");
        for (PropagationQueue::const_iterator i = toUnitPropagate.begin();
                i != toUnitPropagate.end(); i++) {
            r.push_back("    " + (*i)->toString(true));
        }
        r.push_back("  Eqv propagation queue:");
        for (PropagationQueue::const_iterator i = toEqvPropagate.begin();
                i != toEqvPropagate.end(); i++) {
            r.push_back("    " + (*i)->toString(true));
        }
        return r.join("\n");
    }
#endif
    SolverImplementation::SolverImplementation() 
        : undoStack(implGraph, *this), variableSeq(1), 
          conflictClause(NULL),
          decisionLevel(0),
          firstBackjumpId(0),
          prePropagated(false),
          prePropagation(false),
          numUnitPropagationSteps(0),
          numEqvPropagationSteps(0),
          numAssigns(0)
    {
        // to be able to clear the operation stack (for reset)
        undoStack.addBackjump();

        DBG(1, graphNumber++);

    }
    SolverImplementation::~SolverImplementation() {
    }
        
    VariableId SolverImplementation::addVariable() {
        
        if (undoStack.size() > 0)
            throw Error("Cannot add variables after assignments");


        VariableId id = variableSeq++;
        variables.push_back(Variable(id));
        variableRefs.resize(variableSeq);
        variableRefs[id] = &variables.back();

        return id;
    }

    void SolverImplementation::setInternal(VariableId varId) {
        if (undoStack.size() > 0)
            throw Error("Cannot modify variables after assignments");
        assert(varId >= 0 && varId < (int)variableRefs.size());

        variableRefs[varId]->markInternal();



    }
    void SolverImplementation::addClause(const vector<VariableId>& clause) {
        if (undoStack.size() > 0)
            throw Error("Cannot add clauses after assignments");
        clauses.push_back(Clause());
        Clause& c = clauses.back();

        for (vector<VariableId>::const_iterator vid = clause.begin();
                vid != clause.end(); vid++) {
            VariableId id = *vid;
            if (id == 0)
                c.flipTop();
            else {
                Variable* v = variableRefs[id];
                c.pushVariable(v);
                v->pushInstance(&c);
            }
        }

   
    }
    BackjumpId SolverImplementation::setBackjump() {
        DBG(2, "setBackjump()");
        if (conflictClause)
            throw Error("Cannot set backjump when conflict");
        BackjumpId id = undoStack.addBackjump();
        if (!firstBackjumpId)
            firstBackjumpId = id;
        return id;
    }
    
    void SolverImplementation::backjump(BackjumpId id) {

        DBG(2, "backjump(" << id << ")");

        DBG(1, graphNumber++);

        checkConsistency();
        
        undoStack.backjump(id);
        if (id == firstBackjumpId)
            prePropagated = false;
        conflictClause = NULL;
        if (!trivialConflict.literals.empty())
            trivialConflict.literals.clear();

        DBG(2, "checking consistency after backjump");
        checkConsistency();
    }

    void SolverImplementation::reset() {
        DBG(1, "reset()");
        backjump(0);
        undoStack.addBackjump();
        numUnitPropagationSteps = numEqvPropagationSteps = numAssigns = 0;
        prePropagated = false;
        firstBackjumpId = 0;

    }
    
    void SolverImplementation::assign(VariableId id, 
                                      bool value) {

        DBG(1, "assign(x" << id << ", " << value << ")");
        if (conflictClause != NULL || trivialConflict.literals.empty() == false)
            throw Error("Cannot assign a variable when conflict");
        Variable* v = variableRefs[id];

        assert(v != NULL);

        if (v->isInternal()) {
            throw Error("Cannot assign an internal variable");
        }



        undoStack.recordPushQueue(&toAssign);
        toAssign.push_back(Literal(id, value==false));

        checkConsistency();
    }

    Clause* SolverImplementation::assign() {

        const Literal& lit =  toAssign.front();
        undoStack.recordPopQueue(&toAssign, lit);
        bool value = lit.negative == false;

        Variable* v = variableRefs[lit.variable];

        toAssign.pop_front();
       
        if (!prePropagated) {
            DBG(1, "pre-propagation");

            implGraph.setup(variables.size());
            prePropagated = true;
            prePropagation = true;
            conflictClause = prePropagate();
            prePropagation = false;

            if (conflictClause) {
                DBG(1, "Got conflict during pre-propagation");
                return conflictClause;
            }

        }
        if (v->isAssigned() && v->getValue() == value) {
            DBG(1, "Ignoring assignment to an already assigned variable");
            return NULL;
        } 
        implGraph.addDecisionLevel();
        v->markDecisionVariable();

        undoStack.recordPushNode();
        ImplicationGraph::NodePos node = 
            implGraph.pushNode(
                    ImplicationGraph::Node(v->getId(), 0, value,
                               ImplicationGraph::PremiseNode,
                               ImplicationGraph::PremiseNode));

        numAssigns++;
        return doAssign(NULL, node, v, value);
    }

    Clause* SolverImplementation::doPropagation() {
        Clause* conflict;
        while(!toAssign.empty() || !toEqvPropagate.empty() || !toUnitPropagate.empty()) {
            while (!toAssign.empty()) {
                if ((conflict = assign()))
                    return conflict;
                if (!impliedLiterals.empty())
                    return NULL;

            }
            while (!toUnitPropagate.empty()) {
                Clause* c = toUnitPropagate.front(); 
                undoStack.recordPopQueue(&toUnitPropagate, c);
                toUnitPropagate.pop_front();
                if ((conflict = propagate(c))) {
                    return conflict;
                }
                if (!impliedLiterals.empty())
                    return NULL;

            }
            if (!toEqvPropagate.empty()) {
                Clause* c = toEqvPropagate.front(); 
                undoStack.recordPopQueue(&toEqvPropagate, c);

                toEqvPropagate.pop_front();
                if ((conflict = propagate(c))) {
                    return conflict;
                }
                if (!impliedLiterals.empty())
                    return NULL;
            }
        }
        return NULL;
    }
    Solver::AssignResult SolverImplementation::propagate() {
        DBG(1, "ext propagate()");


        if (conflictClause != NULL || trivialConflict.literals.empty() == false)
            throw Error("Cannot propagate when conflict");

        AssignResult ar;
        ar.conflict = ar.implications = 0;
        impliedLiterals.clear();

        conflictClause = doPropagation();
          
        if (conflictClause) {
            DBG(1, "ar.conflict = 1");
            ar.conflict = 1;
        }

        checkConsistency();
        ar.implications = (impliedLiterals.empty() == false) ? 1 : 0;
        return ar;

    }

    bool SolverImplementation::solve() {
        DBG(1, "solve() ");
        Gauss gauss(variableSeq - 1);
        for (Clauses::iterator c = clauses.begin(); c != clauses.end(); c++) {
            Gauss::Row row;
            Split t;
            for (Clause::VariableIterator vi = c->beginVariables();
                    vi != c->endVariables(); vi++) {
                row.push_back((*vi)->getId());
                t.push_back(xorsat::toString((*vi)->getId()));
            }
            if (c->getTop() == true) {
                row.push_back(0);
                t.push_back("0");

            }
            gauss.addRow(row);
        }
        bool sat = gauss.solve();
        if (!sat)
            buildTrivialConflictClause(trivialConflict);
        return sat;
    }

    
    void SolverImplementation::explain(Disjunction& d){
        DBG(1, "explain()");
        if (conflictClause == NULL && trivialConflict.literals.empty())
            throw Error("No conflict");
        if (!trivialConflict.literals.empty()) {
            d = trivialConflict;
            return;
        }
        ImplicationGraph::NodePos np = conflictClause->getImplGraphNode();
        vector<Disjunction> reasons;
        vector<ImplicationGraph::NodePos> nodes;
        implGraph.justify(d, np, settings.firstUIPCuts, 
                          settings.minimizeReasons);
        if (d.literals.empty()) {
            d.literals.clear();
            d.literals.push_back(Literal(0, true));
        }
        
    }

    const LazyVector<Literal>& SolverImplementation::getImplications() const {
        return impliedLiterals;
    }

    void SolverImplementation::justify(Disjunction& impl,
                                       Literal literal) {

        Variable* v = variableRefs[literal.variable];

        Clause* reason = v->getImplyingClause();
        assert(reason != NULL);

        implGraph.justify(impl, 
                          reason->getImplGraphNode(),
                          settings.firstUIPCuts,
                          settings.minimizeReasons);
    }


    long long SolverImplementation::getNumPropagationSteps() const {
        return numUnitPropagationSteps + numEqvPropagationSteps;
    }
    long long SolverImplementation::getNumUnitPropagationSteps() const {
        return numUnitPropagationSteps;
    }
    long long SolverImplementation::getNumEqvPropagationSteps() const {
        return numEqvPropagationSteps;
    }
    long long SolverImplementation::getNumAssigns() const {
        return numAssigns;
    }


    void SolverImplementation::modifyClause(Clause* clause, 
                                            ImplicationGraph::NodePos reason,
                                            VariableId subVarId) {
        VariableId varId = 0;

        ImplicationGraph::NodePos parent1 = reason,
                                  parent2 = clause->getImplGraphNode();

        if (clause->numVariables() == 1 && !prePropagation) {
            Variable* v = *clause->beginVariables();
            if (v->isInternal() == false)
                varId = v->getId();
        }


        clause->pushImplGraphNode(
                implGraph.pushNode(
                    ImplicationGraph::Node(varId, subVarId, !clause->getTop(), 
                        parent1, parent2, clause->toString())));
        clause->setPropagated(false);

    }

    Clause* SolverImplementation::doAssign(Clause* reason,
                                           ImplicationGraph::NodePos node,
                                           Variable* variable,
                                           bool value) {
//#ifdef DEBUG        
//        undoStack.addBackjump();
//#endif
        checkConsistency();
        DBG(2, "doAssign(" << (reason ? reason->toString() : "var")
                << ", x" << variable->getId()
                << ", "  << value << ")");

        if (reason == NULL)
            decisionLevel++;

        Clause* conflict = NULL;

        bool conflictingValue = 
            variable->isAssigned() && variable->getValue() != value;

        undoStack.recordPushValue(variable);
        variable->pushValue(value, decisionLevel);

        // if the variable is already assigned, find a clause with
        // the remaining instance of the variable and derive a conflicting
        // clause
        if (variable->isAssigned() && conflictingValue) {

            DBG(2, "variable " << variable->toString()
                << " is already assigned and now assignining different value");

            for (Variable::InstanceIterator i = variable->beginInstances();
                 i != variable->endInstances(); i++) {
                Clause* clause = *i;
                for (Clause::VariableIterator vi = clause->beginVariables();
                        vi != clause->endVariables(); vi++) {
                    if (*vi == variable) {

                        int oldPos = clause->hide(variable);
                        if (value)
                            clause->flipTop();

                        undoStack.recordAssign(clause, value, oldPos);
                        modifyClause(clause, node, 0);
                        return clause;
                    }
                }
            }
            assert(false /* the instance of the variable was not found */);
        }

        for (Variable::InstanceIterator i = variable->beginInstances();
                i != variable->endInstances(); i++) {
            Clause* clause = *i;
            // leave the reason clause untouched
            if (clause == reason && reason) {
                DBG(2, "skipping reason clause : " << clause->toString());
                continue;
            }
            
            DBG(1, "Hiding " << variable->toString()
                    << " from " << clause->toString());

            int oldPos = clause->hide(variable);
            if (value)
                clause->flipTop();

            undoStack.recordAssign(clause, value, oldPos);
            modifyClause(clause, node, 0);


            if (clause->isConflicting() && !conflict) {
                DBG(2, "found conflict : " << clause->toString());
                conflict = clause;
            }
            checkPropagation(clause);
        }

        if (conflict) {
            return conflict;
        }

        return NULL;
    }

    Clause* SolverImplementation::substitute(Clause* reason,
                                             ImplicationGraph::NodePos node,
                                             Variable* what,
                                             Variable* with,
                                             bool negation) {

        checkConsistency();

        Clause* conflict = NULL;
    
        assert(what->isAssigned() == false);
        assert(with->isAssigned() == false);

//#ifdef DEBUG
//        undoStack.addBackjump();
//#endif
        for (Variable::InstanceIterator i = what->beginInstances();
                i != what->endInstances(); i++) {
            Clause* clause = *i;
            // skip the clause that caused the substitution
            if (clause == reason) 
                continue;
            if (negation)
                clause->flipTop();

            clause->setSubstitution(true);
        }

        DBG(2, "what : " << what->toString());
        DBG(2, "with : " << with->toString());
        for (Variable::InstanceIterator i = with->beginInstances();
                i != with->endInstances(); i++) {
            Clause* clause = *i;

            if (clause->getSubstitution()) {
                DBG(2, "   hiding both variables from "
                        << clause->toString(true));

                int pos = with->hideInstance(i);
                clause->setSubstitution(false);
                int oldPos1 = clause->hide(what);
                int oldPos2 = clause->hide(with);
                undoStack.recordSubstitute(clause, negation, oldPos2, oldPos1,
                                           pos);
                modifyClause(clause, node, what->getId());
                checkPropagation(clause);
                if (clause->isConflicting()) {
                    conflict = clause;
                }
                
            }
        }

        for (Variable::InstanceIterator i = what->beginInstances();
                i != what->endInstances(); i++) {

            Clause* clause = *i;
            if (clause->getSubstitution()) {
                clause->setSubstitution(false);
                DBG(2, "   hiding what and adding with in "
                        << clause->toString(true));

                clause->pushVariable(with);
                with->pushInstance(clause);

                int oldPos = clause->hide(what);

                undoStack.recordSubstitute(clause, negation, oldPos);

                modifyClause(clause, node, what->getId());
                checkPropagation(clause);
                if (clause->isConflicting() ) {
                    DBG(2, "    found conflict : " << clause->toString())
                    conflict = clause;
                }


            }

        }
        int howMany = what->hideInstances();
        what->pushInstance(reason);
        undoStack.recordHideInstances(what, howMany);


        if (conflict) 
            return conflict;
        

        return NULL;
    }
    auto_ptr<Solver> newSolver() {
        return auto_ptr<Solver>(new SolverImplementation());
    }

}
