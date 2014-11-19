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


#include "Variable.hpp"
#include <iostream>
#include "Split.hpp"
#include "Common.hpp"
#include "Clause.hpp"
using namespace std;
namespace xorsat {

    Variable::Variable(int id_) 
        : id(id_), decisionLevel(0), conflictPos(0), implyingClause(NULL) {
        flags.decisionVariable = 0;
        flags.internal = 0;
        flags.implied = 0;
    }

#ifdef DEBUG
    string Variable::toString() const {
        Split ins;
        for (Instances::ConstIterator i = instances.begin();
                i != instances.end(); i++)
            ins.push_back((*i)->toString());
        Split vls;
        for (vector<pair<bool,DecisionLevel> >::const_iterator v = values.begin();
                v != values.end(); v++)
            vls.push_back(xorsat::toString(v->first)
                    +" (dl=" + xorsat::toString(v->second) + ")");
                

       return "x" + xorsat::toString(getId())
               + ": instances:[" + ins.join(",") + "]"
               + ", values:[" + vls.join(",") + "]"
               + ", dl=" + xorsat::toString(decisionLevel)
               + ", conflictPos=" + xorsat::toString(conflictPos);

    }
#endif
}
