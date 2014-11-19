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
#include <string.h>
#include <cstring>
#include <iostream>
#include <algorithm>
#include "Split.hpp"

using namespace std;
namespace xorsat {

    Split::Split(const string& s, const string& delim_)
        : delim(delim_) {
            string::const_iterator i;
            string::const_iterator m = delim.begin();
            string::const_iterator b = s.begin();

            if (delim_.empty()) {
                push_back(s);
                return;
            }


            for (i = s.begin(); i != s.end(); i++) {
                if (*m == *i) {
                    m++;

                    if (m == delim.end()) {
                        string ne;
                        ne.resize(i - delim.size() - b + 1);
                        copy(b, i - delim.size() + 1, ne.begin());
                        if (!ne.empty())
                            push_back(ne);
                        m = delim.begin();
                        b = i + 1;
                    }

                } else 
                    m = delim.begin();

            }
            string ne;
            ne.resize(s.end() - b);
            copy(b, s.end(), ne.begin());
            push_back(ne);
        }

    Split Split::slice(int start, int end) const {
        vector<string> data;
        if (start < 0)
            start = start+size();
        if (end < 0)
            end = end+size();
        if ((size_t)start >= (size_t)end || (size_t)start >= size())
            return Split(data);
        for (size_t i = (size_t)start; i < (size_t)end; i++)
            if (i >= 0 && i < size())
                data.push_back(this->operator[](i));
        return Split(data);
    }

    string Split::join(const string& delim) const {
        string res;

        for (const_iterator i = begin(); i != end(); i++) {
            if (i != begin())
                res += delim;
            res += *i;
        }
        return res;
    }

    Split::operator string() const {
        return join(delim);
    }

    Split & Split::extend(const Split & s) {
        for (size_t i = 0; i < s.size(); i++)
            push_back(s[i]);
        return *this;
    }
}
