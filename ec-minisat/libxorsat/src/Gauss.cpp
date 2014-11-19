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


#include "Gauss.hpp"
#include "Split.hpp"
#include "Common.hpp"
#include <cassert>
#include <algorithm>
using namespace std;
namespace xorsat {

    int Gauss::pivot(size_t start, VariableId j) {
        for (size_t i = start; i < rows.size(); i++)
            if (hasVariable(rows[i], j))
                return i;
        return -1;
    }

    void Gauss::swap(int i, int j) {
        Row r = rows[i];
        rows[i] = rows[j];
        rows[j] = r;
    }

    bool Gauss::hasTop(const Row& r) const {
        return hasVariable(r, 0);
    }

    bool Gauss::hasVariable(const Row& r, VariableId j) const {
        for (Row::const_iterator ri = r.begin(); ri != r.end(); ri++) {
            if (*ri == j)
                return true;
            else if (*ri > j)
                return false;
        }
        return false;
    }

    bool Gauss::isConflicting(const Row& r) const {
        if (!r.empty() && r.front() == r.back() && r.front() <= 0) {
            // T = ~T or ~T = T
            return true;
        }

        return false;

    }
    bool Gauss::isSatisfied(const Row& row) const {
        if (row.empty())
            return true;
        if (row.front() == 0) {
            // T == ~T

            return false;
        }
        if (row.front() == -1) {
            // ~T == T
            Row::const_iterator next = row.begin();
            next++;
            if (next == row.end())
                return false;
            if (*next != 0)
                return false;
        }
        return true;
    }

    void Gauss::add(Row& dst, Row& src) {

        Row::iterator i1 = dst.begin(),
            i2 = src.begin();

        size_t elems = 0;
        while (i2 != src.end()) {
            if (i1 != dst.end()) {
                while (i1 != dst.end() && *i1 < *i2 ) {
                    i1++;
                }
                if (i1 == dst.end() || *i1 > *i2) {
                    i1 = dst.insert(i1, *i2);
                } else {
                    assert(*i1 == *i2);
                    i1 = dst.erase(i1);
                    elems--;
                }                
            } else {
                i1 = dst.insert(i1, *i2);
                elems++;
            }
            i2++;
        }

    }

    Gauss::Gauss(VariableId last) 
        : lastVariable(last)
#ifdef DEBUG
          , formulaSeq(0)
#endif

    { 
        values.resize(lastVariable);
        assigned.resize(lastVariable);
    }

    void Gauss::addRow(const Row& row) {
        rows.push_back(row);
        Row& r = rows.back();
        r.push_front(-1);
#ifdef DEBUG
        Split c;
        bool top = false;
        for (Row::const_iterator i = row.begin(); i != row.end(); i++) {
            if (*i > 0)
                c.push_back("x" + xorsat::toString(*i));
            else
                top = true;
        }

        string cmd = top ? "EVEN" : "ODD";
        bc.push_back("f" + xorsat::toString(formulaSeq)
                + " := " + cmd + "(" + c.join(",") + ");");
        bc.push_back("ASSIGN f" + xorsat::toString(formulaSeq) + ";");
        formulaSeq++;

#endif
    }
    struct RowSorter {
        bool operator()(const Gauss::Row& r1, const Gauss::Row& r2) const {
            Gauss::Row::const_iterator i1 = r1.begin(),
                i2 = r2.begin();
            while (i1 != r1.end() && *i1 <= 0)
                i1++;
            while (i2 != r2.end() && *i2 <= 0)
                i2++;
            while (1) {


                if (i1 == r1.end())
                    return false;
                else if (i2 == r2.end())
                    return true;

                else if (*i1 < *i2)
                    return true;
                else if (*i2 < *i1)
                    return false;
                i1++;
                i2++;
            }
        }
    } RowSort;

    bool Gauss::backSubstitute() {
        for (Rows::reverse_iterator r = rows.rbegin();
                r != rows.rend(); r++) {
            VariableId j = 0;
            for (Row::iterator i = r->begin(); i != r->end(); i++) {
                if (*i > 0) {
                    j = *i;
                    break;
                }
            }
            if (j == 0)
                continue;
            Rows::reverse_iterator r2 = r;
            r2++;
            for (; r2 != rows.rend(); r2++) {
                if (hasVariable(*r2, j))
                    add(*r2, *r);
            }
            if (isConflicting(*r)) {
                return false;
            }
        }
        return true;
    }
    void Gauss::assignVariables() {

        for (VariableId j = lastVariable; j > 0; j--) {
            DBG(1, "Assigning variable " << j);
            int rowNum = rows.size();
            for (Rows::reverse_iterator r = rows.rbegin(); 
                    r != rows.rend(); r++) {
                rowNum--;
                if (r->empty() || r->back() != j)
                    continue;

                bool value = values[j-1];
                if (assigned[j-1] == false) {

                    value = isSatisfied(*r) == false;
                    for (Row::iterator i = r->begin(); i != r->end(); i++) {
                        if (*i > 0 && assigned[(*i) - 1] && values[(*i)-1])
                            value = !value;
                    }

                    assigned[j-1] = true;


                    values[j-1] = value;

                    DBG(1, "x" << j << " <- " 
                            << string(values[j-1] ? " T" : "~T"));
                }
                r->pop_back();
                if (value) {
                    Row top;
                    top.push_back(0);
                    add(*r, top);

                }


                
            }
            DBG(1, toString());
            DBG(1, "---------------------------");
        }
    }

    bool Gauss::solve() {

        for (Rows::iterator i = rows.begin(); i != rows.end(); i++)
            i->sort();

        DBG(1, "sorted");
        DBG(1, toString());

        VariableId j = 1;
        size_t i = 0;
        while (i < rows.size() && j <= lastVariable) {
            DBG(1, "gauss i=" << i << " j=" << j);
            int p = pivot(i, j);
            DBG(1, "pivot p=" << p);
            if (p == -1) {
                j++;
                // i++;
                continue;
            }
                    
            swap(i, p);
            DBG(2, "swapped " << i << " and " << p);
            DBG(2, toString());
            DBG(2, "-------------");

            for (size_t u = i+1 ; u < rows.size(); u++) {
                if (hasVariable(rows[u], j)) {
                    DBG(2, "row[" << u << "] += row[" << i << "]");
                    DBG(2, toString(u) << " += " << toString(i));
                    add(rows[u], rows[i]);

                    DBG(2, "size: " << rows[u].size());
                    DBG(2, "result: \n" << toString(u));
                    if (isConflicting(rows[u])) {
                        DBG(2, "conflict1 !");
                        return false;
                    }



                    DBG(2, "-------------");
                }
            }
            DBG(2, toString());
            DBG(2, "^^^^^^^^^");

            j++;
            i++;
        }
        // back-substitution
        DBG(1, "back substitution");
        DBG(1, toString());
        DBG(1, "----------------");

        if (backSubstitute() == false)
            return false;
         DBG(1, toString());
        DBG(1, "^^^^^^^^^ before assigning");



        // eliminate free variables
        assignVariables();


        DBG(1, toString());
        DBG(1, "-------------");

        for (Rows::iterator r = rows.begin(); r != rows.end(); r++)
            if (isConflicting(*r)) {
                return false;
            }

        return true;
    }

    Gauss::Values Gauss::getValues() const {
        Values res;
        DBG(1, "getValues");

        for (VariableId j = 1; j <= lastVariable; j++) {
            size_t idx = j-1;
            if (assigned[idx])
                res.push_back(make_pair(j, values[idx]));
        }
        return res;
    }

#ifdef DEBUG
    std::string Gauss::toString(int onlyRow) const {
        Split res;
        int pos = 0;

        for (Rows::const_iterator i = rows.begin(); i != rows.end(); i++) {
        
            Split row;
            bool value = false;
            for (Row::const_iterator i2 = i->begin(); i2 != i->end(); i2++) {
                if (*i2 == -1)
                    value = true;
                else {
                    if (*i2 == 0)
                        row.push_back("T");
                    else
                        row.push_back("x" + xorsat::toString(*i2));
                }
            }
            if (pos == onlyRow || onlyRow == -1) {
                if (row.empty())
                    row.push_back("~T");
                res.push_back(row.join(" + ") + " = " 
                        + string(value ? "T" : "~T"));
            }
            

            pos++;
        }
        return res.join("\n");
    }
    std::string Gauss::toCircuit() {
        Split res = bc;
        Values values = getValues();
        for (Values::iterator i = values.begin(); i != values.end(); i++) {
            res.push_back("ASSIGN " 
                    + string(i->second ? " " : "~")
                    + "x" + xorsat::toString(i->first) + ";");
        }
        return res.join("\n");
    }
#endif
}

