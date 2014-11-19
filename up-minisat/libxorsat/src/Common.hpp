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


#ifndef _xorsat_common_hpp_
#define _xorsat_common_hpp_
#include <sstream>
#include <string>
#include <iostream>
#include <cassert>
namespace xorsat {
    /** a convenience method for converting values to strings 
     * by using string stream */
    template <class T> std::string toString(T t) {
        std::ostringstream ost;
        ost << t;
        return ost.str();
    }
    /** a convenience method for converting strings to integers */
    int atoi(const std::string& s);

#ifdef DEBUG
    extern int debugLevel;
#endif
}
#ifdef DEBUG
#define DBG(lvl,x) if (debugLevel >= lvl) std::cout << x << std::endl; 
#else
#define DBG(lvl,x)
#endif
#endif
