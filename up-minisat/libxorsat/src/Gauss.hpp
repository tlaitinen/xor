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


#ifndef _xorsat_gauss_hpp_
#define _xorsat_gauss_hpp_
#include "xorsat.hpp"
#include "Split.hpp"
namespace xorsat {
    /** Gaussian elimination on sparse linear equation matrices modulo 2 
     *  (slow implementation) */
    class Gauss {
    public:
        /** the rows of the matrix are represented as ordered lists 
         * of variable identifiers (0 being the symbol Top). 
         * The matrix is augmented, that is, if there is a special element
         * -1 at the beginning of the list, then the row has to evaluate
         *  to true, otherwise to false. */
        typedef std::list<VariableId> Row;

        typedef std::vector<Row> Rows;
        typedef std::vector< std::pair<VariableId, bool> > Values;
    private:
        /** the rows of the matrix */
        Rows rows;

        /** the variable with the highest identifier 
         * that has occurences in the matrix */
        VariableId lastVariable;

        /** the values of the variables, 
         * valueOf(VariableId) := values[VariableId - 1],
         * valid if assigned[VariableId - 1] is true */
        std::vector<bool> values;

        /** the assigned-status of the variables,
         * isAssigned(VariableId) := assigned[VariableId - 1] == true;
         */
        std::vector<bool> assigned;

#ifdef DEBUG
        /** binary circuit for validating the calculation */
        Split bc;

        /** sequence for binary circuit formula identifiers */
        int formulaSeq;
#endif

        /** \return a row number of the first row (greater or equal to 'start')
         * that has an occurence of the variable 'j' */
        int pivot(size_t start, VariableId j);

        /** swaps the rows 'i' and 'j' */
        void swap(int i, int j);

        /** \return true, if the row given as parameter has the symbol Top */
        bool hasTop(const Row& row) const;

        /** \return true, if the row given as parameter has an occurence
         * of the Variable 'j' */
        bool hasVariable(const Row& row, VariableId j) const;

        /** \return true, if the row is either T = ~T or ~T = T */
        bool isConflicting(const Row& row) const;

        /** \return true, if the constants of the equation characterized 
         * by the row agree on their values T = T or ~T = ~T 
         * (excluding the variables) */
        bool isSatisfied(const Row& row) const;
         
        /** adds the elements of the row 'src' to the row 'dst' and
         * eliminates duplicates */
        void add(Row& dst, Row& src);

        /** simplifies the equations by back substitution 
         * \return false, if one of the rows is conflicting, true otherwise*/
        bool backSubstitute();

        /** tries to satisfy all row equations by assigning values to
         * variables and eliminating the variables from the equations */
        void assignVariables();
    public:        
        /** assigns fields */
        Gauss(VariableId lastVariable);

        /** adds a row (linear equation) to the matrix */
        void addRow(const Row& row);

        /** tries to solve the system of linear equations  
         * \return true, if the system has a solution */
        bool solve();

        /** \return the assignment that solves the system */
        Values getValues() const;
#ifdef DEBUG
        /** \return a textual representation of the matrix */
        std::string toString(int row=-1) const;
        /** \return a bcminisat2core compatible representation
         * of the matrix and the assignments */
        std::string toCircuit();
#endif
    };
}
#endif
