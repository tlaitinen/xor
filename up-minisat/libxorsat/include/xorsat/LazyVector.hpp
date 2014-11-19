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


#ifndef _xorsat_lazyvector_hpp_
#define _xorsat_lazyvector_hpp_
#include <vector>
#include <assert.h>
namespace xorsat {


    /** A vector that does not shrink */
    template <class T>
        class LazyVector {
    public:
        typedef std::vector<T> Container;

        typedef typename Container::iterator iterator;

        typedef typename Container::const_iterator const_iterator;
        
        typedef typename Container::reference reference;

        typedef typename Container::const_reference const_reference;

        typedef typename Container::size_type size_type;
        typedef typename Container::value_type value_type;


    private:
        Container vec;

        size_t used;

    public:        
        LazyVector() 
            :  used(0) {
            }

        void push_back(T e) {
            if (used < vec.size())
                vec[used] = e;
            else
                vec.push_back(e);
            used++;
        }

        void pop_back() {
            assert(vec.size() > 0);
            used--;
        }

        size_t size() const {
            return used;
        }

        void resize(size_type st) {
            while (size() < st)
                push_back(T());
            while (size() > st)
                pop_back();
        }

        /** \return an iterator pointing to the first element */
        iterator begin() {
            return vec.begin();
        }

        /** \return an iterator pointing to the end of the vector */
        iterator end() {
            return vec.begin() + used;
        }

        /** \return a const iterator pointing to the first element */
        const_iterator begin() const {
            return vec.begin();
        }

        /** \return a const iterator pointing to the end of the vector */
        const_iterator end() const {
            return vec.begin() + used;
        }

        /** \return a reference to an element of the vector */
        reference operator[](size_type t) {
            return vec[t];
        }

        /** \return a const reference to an element of the vector */
        const_reference operator[](size_type t) const {
            return vec[t];
        }

        /** clears the contents of the vector */
        void clear() {
            used = 0;
        }

        /** \return true, if the vector is empty */
        bool empty() const {
            return used == 0;
        }

        /** \return reference to the first element */
        reference front() {
            return vec.front();
        }

        /** \return const reference to the first element */
        const_reference front() const {
            return vec.front();
        }

        /** \return reference to the back element */
        reference back() {
            return vec[size()-1];
        }

        /** \return const reference to the first element */
        const_reference back() const {
            return vec[size()-1];
        }
        
    };
}
#endif
