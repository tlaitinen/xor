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


#ifndef _xorsat_hpp_
#define _xorsat_hpp_

#include <string>
#include <list>
#include <memory>
#include <vector>
#include <exception>
#include <stdexcept>
#include "xorsat/LazyVector.hpp"

namespace xorsat {
    /** The special value of VariableId for the symbol Top */
    enum { Top = 0 };


    /** Container for exceptions originating from xorsat-namespace*/
    class Error : public std::runtime_error {
    public:
        /** stores the message */
        Error(const std::string& message);
    };

    typedef int VariableId;
    typedef int ClauseId;

    typedef size_t BackjumpId;
    typedef int DecisionLevel;


    /** a literal is a variable and a flag indicating negation */
    struct Literal {
        /** the numeric identifier of the propositional variable */
        VariableId variable;

        /** true, if the literal is a negation */
        bool negative;

        const Literal& operator=(const Literal& l) {
            variable = l.variable;
            negative = l.negative;
            return *this;
        }
    
        bool operator==(const Literal& l) const {
            return variable == l.variable && negative == l.negative;
        }

        /** assigns fields */
        Literal(VariableId v, bool n)
            : variable(v), negative(n) {}
    };



    /** Container for disjunction */
    struct Disjunction {
        /** the literals of the disjunction */
        std::vector<Literal> literals;
        std::string toString() const;
    };
    /** Abstract interface of the XOR Solver. Use the static function 
     * newSolver() to construct an instance of the implementation. */
    class Solver {
    public:        
        /** Container for communicating settings to the xor-module */
        typedef struct Settings {

            /** if true, then reasons calculated by justify and
             * explain are minimized (redundant literals are removed) */
            bool minimizeReasons;

            /** if true, then cuts are expanded
             * until a cnf-compatible 1-UIP cut is found,
             * otherwise the first cnf-compatible cut will do */
            bool firstUIPCuts;

            Settings() 
                : minimizeReasons(false),
                  firstUIPCuts(false) {}
        } Settings;
    private:        
        /** No copies allowed */
        Solver(const Solver&);
        
        /** No assignment allowed */
        const Solver& operator=(const Solver&);

    protected:        
        /** settings every Solver instance should take into account */
        Settings settings;

    public:
        /** Return value of Solver::assign */
        typedef struct {
            /** true, if the set of xor-clauses is no longer satisfiable,
             * false otherwise. */
            unsigned int conflict : 1;

            /** true, if the solver could derive implied literals,
             * false otherwise. */
            unsigned int implications : 1;
        } AssignResult;



        /** Empty constructor */
        Solver() {
            settings.minimizeReasons = false;
            settings.firstUIPCuts = false;
        }

        /** Empty destructor, defined to make it virtual */
        virtual ~Solver() {}

        /** The method declares a new propositional variable to be
         * used in the xor-clauses. It
         * cannot be called when there are active backjump points.  
         * \return the identifier of the new variable 
         * \throws Error  if the variable cannot be added */
        virtual VariableId addVariable()=0;

        /** The method tags a variable to be internal, that is,
         * a variable that occurs only in xor-clauses. Values of internal
         * variables are not of interest outside of xor module. Thus,
         * implied literals will not include any internal variables. */
        virtual void setInternal(VariableId varId)=0;

        /** The method adds a new xor-clause and returns its identifier. All
         * the variables in the xor-clause must have been declared previously
         * using addVariable-method. Note: the symbol top can be added using
         * xorsat::Top.  The method cannot be called when the are active
         * backjump points.
         *
         * \param  clause    the array of variables in the xor-clause
         * \throws Error     if a xor-clause cannot be added */
        virtual void addClause(const std::vector<VariableId>& clause)=0;

        /** The method sets a backjump point labeled with an unique identifier.
         * The backjump point can be used to record the state of the solver.
         * The state of the solver can be restored later with
         * backjump(..)-method. 
         *
         * \returns       the identifier of the backjump point
         * \throws Error  if a backjump point with the same identifier exists 
         *                or a conflict clause exists */
        virtual BackjumpId setBackjump()=0;

        /** The method restores the state of the solver to a previously
         * recorded state identified by a backjump point. 
         *
         * \param  id       the identifier of the backjump point
         * \throws Error    if no such backjump point exists */
        virtual void backjump(BackjumpId id)=0;

        /** The method restores the state of the solver to the initial
         * state (to the implicitly defined first backjump point) */
        virtual void reset()=0;

        /** TODO */
        virtual void assign(VariableId id, bool value)=0;

        /** TODO */
        virtual AssignResult propagate()=0;

        /** The method performs a full Gauss-elimination to find out 
         * whether the set of xor-clauses is satisfiable. 
         *
         * \returns false, if the set of xor-clauses is no longer satisfiable,
         *          and true otherwise */
        virtual bool solve()=0;
        
        /** The method builds a conflict clause which tries to capture
         * a useful reason of the conflict.
         *
         * \throw Error   if the set of xor-clauses is not conflicting */
        virtual void explain(Disjunction& d)=0;

        /** This returns the implied literals deduced by the last 
         *  assignment (Solver::assign) */
        virtual const LazyVector<Literal>& getImplications() const=0;

        /** This returns implied literals (for the requested variables)
         * and their justifications. The implied clauses are added
         * to the vector given as the first parameters. The first literal
         * of each disjunction is the implied literal and the rest of the
         * disjunction is the justifying part. */
        virtual void justify(Disjunction& implication,
                             Literal lit) = 0;

        /** This returns the variables that participated in the 
         * derivation of the explained last conflict or justified literal */
        virtual const LazyVector<VariableId>& getParticipated() const=0;

        /** Method for setting operational settings */
        void setSettings(Settings& s) {
            settings = s;
        }
#ifdef DEBUG
        virtual std::string toString() const=0;
#endif
        virtual std::string getGraphviz()=0;


    };

    /** Returns an implementation of Solver wrapped in a smart pointer */
    std::auto_ptr<Solver> newSolver();    
}
#endif
