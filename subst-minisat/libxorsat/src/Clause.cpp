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


#include "Clause.hpp"
#include "Variable.hpp"
#include "Split.hpp"
#include "Common.hpp"
#include <algorithm>
#include <iostream>
using namespace std;

namespace xorsat {

    Clause::Clause() 
        : top(false), substitution(false), propagated(false) {
        DBG(2, "Clause::Clause()");
    }


#ifdef DEBUG


    string Clause::toString(bool full) const {
        
        Split r;
        string h;
        if (full) {

            for (Variables::ConstIterator i = variables.beginHidden(); 
                    i != variables.endHidden(); i++)
            {

                Variable* v = *i;
                r.push_back("x" + xorsat::toString(v->getId()));
            }
            h = "(" + r.join("+") + ") ";
            r.clear();
        }

       
        for (Variables::ConstIterator i = variables.begin(); 
                i != variables.end(); i++)
        {
            
            Variable* v = *i;
            r.push_back("x" + xorsat::toString(v->getId()));
        }
        if (top)
            r.push_back("T");
        return h+r.join("+");
    }
#endif
}
