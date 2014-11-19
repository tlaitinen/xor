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


#ifndef _xorsat_lazyqueue_hpp_
#define _xorsat_lazyqueue_hpp_
#include "xorsat.hpp"

namespace xorsat {
    /** Queue implemented on a never shrinking vector reusing elements
     * after the queue has emptied */
    template <class T>
    class LazyQueue {
        LazyVector<T> elems;
        size_t qhead;
    public:
        LazyQueue() 
            : qhead(0) {}
         
        void push_back(T elem) {
            elems.push_back(elem);
        }

        void pop_front() {
            if (qhead + 1 == elems.size()) 
                clear();
            else
                qhead++;
        }

        const T& front() const {
            return elems[qhead];
        }

        const T& back() const {
            return elems.back();
        }



        void pop_back() {
            elems.pop_back();
        }

        void clear() {
            elems.clear();
            qhead = 0;
        }

        bool empty() const {
            return size() == 0;
        }

        size_t size() const {
            return elems.size() - qhead;
        }
                
    };

}
#endif

