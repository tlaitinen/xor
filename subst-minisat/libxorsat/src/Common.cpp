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


#include "xorsat.hpp"
#include "Common.hpp"
#include "Split.hpp"
#include <cstdlib>
using namespace std;
namespace xorsat {
int debugLevel = 1;

string Disjunction::toString() const {
    Split res;
    for (size_t i = 0; i < literals.size(); i++) {
        const Literal& l = literals[i];
        res.push_back(string(l.negative ? "~x" : " x" ) 
                      + xorsat::toString(l.variable));
    }
    return res.join(" v ");
}

int atoi(const string& s) {
    return ::atoi(s.c_str());
}
}
