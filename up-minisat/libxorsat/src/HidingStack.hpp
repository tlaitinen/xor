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


#ifndef _xorsat_hidingstack_hpp_
#define _xorsat_hidingstack_hpp_
#include <list>
namespace xorsat {


    /** A never-shrinking stack whose elements can be hidden and restored  */
    template <class T>
        class HidingStack {
    public:
        /** implemented as a vector */
        typedef std::vector<T> Container;

        /** for iterating the contents of the container */
        typedef typename Container::iterator Iterator;

        /** for iterating the contents of the container (const) */
        typedef typename Container::const_iterator ConstIterator;


    private:
        /** contains the elements of the stack */
        Container stack;

        /** the number of non-hidden elements */
        size_t activeNum;

        /** number of used elements */
        size_t used;
    public:        
        /** initializes an empty stack */
        HidingStack() 
            : activeNum(0), used(0) {
            }

        /** pushes an element to the top of the stack */
        void push(T e) {
            if (used < stack.size())
                stack[used] = e;
            else
                stack.push_back(e);
            activeNum++;
            used++;
        }

        /** pops an elements from the top of the stack */
        void pop() {
            assert(stack.size() > 0);
            assert(activeNum > 0);
            activeNum--;
            used--;
        }

        /** hides the specified element if it is in the container 
         * and returns the original position of the hidden element */
        int hide(T e) {

            for (Iterator i = begin(); i != end(); i++) {
                if (*i == e) {
                    return hide(i);
                }
            }
            assert(false);
            return -1;
        }

        /** hides the element that the specified iterator points to
         * and returns the original position of the hidden element */
        int hide(Iterator i) {

            assert(activeNum >= 1);

            Iterator first = begin();
            T tmp = *first;
            *first = *i;
            *i = tmp;

            int pos = i - begin();
            activeNum--;
            DBG(2, "hide returning " << (i - stack.begin()));
            return pos;
        }

        /** hides all elements of the stack and returns
         * the number of elements hidden */
        int hideAll() {
            DBG(2, "hideAll, activeNum=" << activeNum);
            int oldActiveNum = activeNum;
            activeNum = 0;
            return oldActiveNum;

        }

        /** restore the specified number of elements */
        void unhideMany(int howMany) {

            DBG(2, "unhideMany, howMany" << howMany);
            activeNum = howMany;

        }

        /** restores a hidden element to the specified original position */
        void unhide(int origPos) {
            activeNum++;
            DBG(2, "unhide(" << origPos << "), active=" << activeNum
                    << ", used=" << used);
            assert(activeNum <= stack.size());
            assert(activeNum <= used);

            if (origPos > 0) {
                Iterator first = begin();
                T tmp = *first;
                *first = *(first + origPos);
                *(first + origPos) = tmp;
            }
        }

        /** \return the number of visible elements in the stack */
        size_t size() const {
            return activeNum;
        }

        /** \return an iterator pointing to the first visible element */
        Iterator begin() {
            size_t first = used - activeNum;
            return stack.begin() + first;
        }

        /** \return an iterator pointing to the last visible element */
        Iterator end() {
            return stack.begin() + used;
        }

        /** \return a const iterator pointing to the first visible element */
        ConstIterator begin() const {
            size_t first = used - activeNum;
            return stack.begin() + first;
        }

        /** \return a const iterator pointing to the last visible element */
        ConstIterator end() const {
            return stack.begin() + used;
        }

        /** \return a const iterator pointing to the first hidden element */
        ConstIterator beginHidden() const {
            return stack.begin();
        }

        /** \return a const iterator pointing to the last hidden element + 1*/
        ConstIterator endHidden() const {
            return begin();
        }


    };
}
#endif
