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


#ifndef _xorsat_intset_hpp_
#define _xorsat_intset_hpp_
#include "Split.hpp"
#include "Common.hpp"
#include "xorsat.hpp"
#include <assert.h>
namespace xorsat {

    /** Fast implementation of integer set, 
     * All operations (except setup and clear) run in O(1) time. */
    class IntSet {
    public:
        typedef int Elem;
    private:
        typedef LazyVector<Elem> Set;
    public:

        typedef Set::iterator iterator;
        typedef Set::const_iterator const_iterator;
        typedef Set::size_type size_type;

    private:
        typedef size_t ReasonPos;
        /** contents of the set */
        LazyVector<Elem> reason;

        /** location of nodes in the integer set + 1 (or 0 if they
         * are not in the set */
        LazyVector<ReasonPos> reasonPos;

    public:        

        /** prepares the integer set to be used with the specified number
         * of nodes. this method must be called before the methods
         * 'has', 'add' and 'remove' */
        void setup(size_t nodes) {
            clear();
            reasonPos.resize(nodes);
        }

        /** \return true if the specified node is in the integer set,
         * false otherwise*/
        bool has(Elem np) const {
            assert(np >= 0);
            return reasonPos[np] > 0;
        }

        /** adds the specified node to the integer set 
         * - note: node must not be in the set */
        void add(Elem np) {
            assert(np >= 0);           
            assert (!has(np));

            reasonPos[np] = reason.size() + 1;
            reason.push_back(np);
            
            DBG(2, "IntSet::add(" << np << "):\n" + toString());
        }

        /** removes the specified node from the integer set
         * - note: node must be in the set */
        void remove(Elem np) {
            assert(np >= 0);
            assert(has(np));
            ReasonPos rp = reasonPos[np];
            Elem tmp = reason[reason.size() - 1];

            if (np != tmp) {
                reason[rp - 1] = tmp;
                reasonPos[tmp] = rp;            
            }
            reasonPos[np] = 0;
            reason.pop_back();
            DBG(2, "IntSet::remove(" << np << "):\n" + toString());

        }

        size_type size() const {
            return reason.size();
        }

        /** \return a const iterator pointing to the first element */
        const_iterator begin() const {
            return reason.begin();
        }

        /** \return a const iterator pointing to the end of the integer set */
        const_iterator end() const {
            return reason.end();
        }

        /** clears the integer set */
        void clear() {
            for (const_iterator i = begin(); i != end(); i++)
                reasonPos[*i] = 0;
            reason.clear();
        }
#ifdef DEBUG
        /** \return string representation of the contents of the integer set */
        std::string toString() {
            Split r;
            Split r2;
            for (size_t i = 0; i < reason.size(); i++)
                r2.push_back(xorsat::toString(reason[i]));
            r.push_back("Elems: " + r2.join(", "));
            r2.clear();
            for (size_t i = 0; i < reasonPos.size(); i++)
                r2.push_back(xorsat::toString(reasonPos[i]));
            r.push_back("Elem pos: " + r2.join(", "));
            return r.join("\n");
        }

#endif

    };
}
#endif
