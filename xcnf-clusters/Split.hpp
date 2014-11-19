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


#include <string>
#include <vector>

#ifndef _split_
#define _split_
/** a parser class used to split strings at certain delimiters */
class Split : public std::vector<std::string> {
private:
    /** the delimiter used when the string was split */
    std::string delim;
public:
    /** the delimiter is set to " " */
    Split() : delim(" ") {}

    /** assigns fields */
    Split(const std::vector<std::string>& data, const std::string& d=" ")
        : std::vector<std::string>(data), delim(d) {}

    /** splits the string with the delimiter */
    Split(const std::string& s, const std::string& delim=" ");

    /** returns a subrange of the elements of the string vector.
     *  indices may be negative and they refer to the end of the
     *  vector in that case. */
    Split slice(int start, int end) const;

    /** combines the strings using the supplied delimeter */ 
    std::string join(const std::string& delim) const;

    /** \return the string combined with the last delimiter used */
    operator std::string() const;

    /** concats the given Split to this Split */
    Split & extend(const Split & s);
};
#endif
