#include <vector>
#include <list>
#include <iterator>
#include <cstdlib>
#include <sstream>
#include <cstdio>
#include <string>
#include <map>
#include <set>
#include <algorithm>
#include <iostream>
#include <boost/tokenizer.hpp>
#include <boost/unordered_set.hpp>
#include "boost/tuple/tuple.hpp"

#ifdef DEBUG
#define D(x) cerr << x << endl;
#else
#define D(x)
#endif

int32_t maxVar = 0;
using namespace std;
  template <class T> std::string toString(const T& t) {
        std::ostringstream ost;
        ost << t;
        return ost.str();
    }

 template <> std::string toString(const vector<int32_t>& s) {
     std::ostringstream ost;
     for (vector<int32_t>::const_iterator si = s.begin(); si != s.end(); si++) {
         if (si != s.begin())
             ost << " ";
         ost << toString(*si);
     }
     return ost.str();
 }

int nextVar;
typedef map<vector<int32_t>, int32_t> Aliases;
Aliases aliases;
set<pair<int32_t, int32_t> > binXors;
boost::unordered_set< pair<vector<int32_t>, bool> > printed;

bool tagPrinted(const vector<int32_t>& lhs, bool rhs) {
    return printed.insert(make_pair(lhs, rhs)).second;
}
bool addClause(const vector<int32_t>& lhs, bool rhs) {
    if (tagPrinted(lhs, rhs)) {
        cout << (rhs ? "x " : "x -") << toString(lhs) << " 0" << endl;
        return true;
    } else
        return false;
}


void addAliases(const vector<int32_t>& lhs, bool rhs) {

    for (size_t i = 0; i < lhs.size(); i++) {
        vector<int32_t> lhsCopy;
        bool fail = false;
        for (size_t i2 = 0; i2 < lhs.size(); i2++) {
            if (i == i2)
                continue;
            if (lhs[i2] > maxVar) {
                fail = true;
                break;
            }

            lhsCopy.push_back(lhs[i2]);
        }

        if (fail || lhsCopy.empty())
            continue;
        int32_t newAlias = rhs ? - lhs[i] : lhs[i];

        // cerr << "adding alias " << newAlias << " := " << toString(lhsCopy) << endl;
        if (aliases.find(lhsCopy) == aliases.end()) {

            aliases[lhsCopy] = newAlias;
        } else {
            int32_t oldAlias = aliases[lhsCopy];
            if (oldAlias == newAlias)
                continue;

            vector<int32_t> lhs2;
            bool rhs2 = false;
            if (oldAlias < 0) 
                rhs2 = !rhs2;
            if (newAlias < 0)
                rhs2 = !rhs2;
            oldAlias = abs(oldAlias);
            newAlias = abs(newAlias);
            lhs2.push_back(oldAlias);
            lhs2.push_back(newAlias);
            sort(lhs2.begin(), lhs2.end());
            if (oldAlias == newAlias) {
                cout << "x 1 0" << endl;
                cout << "x -1 0" << endl;
                exit(1);
            }
            addClause(lhs2, rhs2);
       }

    }
}
void ptable2Add(const vector<int32_t>& lhs1, int32_t a1,
                const vector<int32_t>& lhs2, int32_t a2,
                vector<int32_t>& lhs3) {
    lhs3.clear();
    set_symmetric_difference(lhs1.begin(), lhs1.end(), 
            lhs2.begin(), lhs2.end(),
            back_inserter(lhs3));


    D(toString(lhs1) << " + " << toString(lhs2) <<  " = " << toString(lhs3));
    Aliases::iterator a3i = aliases.find(lhs3);
    if (a3i == aliases.end())
        return;

    int a3 = a3i->second;
    lhs3.clear();
    bool rhs = false;
    if (a1 < 0) {
        rhs = !rhs;
        a1 = -a1;
    }
    if (a2 < 0) {
        rhs = !rhs;
        a2 = -a2;
    }
    if (a3 < 0) {
        rhs = !rhs;
        a3 = -a3;
    }

    lhs3.clear();
    if (a1 == a2)
        lhs3.push_back(a3);
    else if (a1 == a3)
        lhs3.push_back(a2);
    else if (a2 == a3)
        lhs3.push_back(a1);
    else {
        lhs3.push_back(a1);
        lhs3.push_back(a2);
        lhs3.push_back(a3);
    }


    sort(lhs3.begin(), lhs3.end());
    if (addClause(lhs3, rhs)) {
        addAliases(lhs3, rhs);
    }

}

                
void ptable2(const vector<int32_t>& vars) {
    for (size_t i1 = 0; i1 < vars.size(); i1++) {
        for (size_t i2 = i1+1; i2 < vars.size(); i2++) {

            vector<int32_t> lhs;
            lhs.push_back(vars[i1]);
            lhs.push_back(vars[i2]);
            if (aliases.find(lhs) == aliases.end()) {

                aliases[lhs] = nextVar;
                lhs.push_back(nextVar);
                nextVar++;
            }
        }
    }

    vector<int32_t> a, b, ab, bc, cd, tmp;
    int32_t a_, b_, ab_, bc_, cd_;
    for (size_t i1 = 0; i1 < vars.size(); i1++) {
        a.clear();
        a.push_back(vars[i1]);
        a_ = vars[i1];

        for (size_t i2 = i1+1; i2 < vars.size(); i2++) {
            b.clear();
            b.push_back(vars[i2]);
            b_ = vars[i2];
            ptable2Add(a, a_, b, b_, tmp);
            ab.clear();
            ab.push_back(vars[i1]);
            ab.push_back(vars[i2]);
            sort(ab.begin(), ab.end());
            ab_ = aliases[ab];
            assert(ab_ != 0);

            for (size_t i3 = i2+1; i3 < vars.size(); i3++) {
                bc.clear();
                bc.push_back(vars[i2]);
                bc.push_back(vars[i3]);
                sort(bc.begin(), bc.end());
                bc_ = aliases[bc];
                assert(bc_ != 0);
                ptable2Add(ab, ab_, bc, bc_, tmp);
                ptable2Add(a,a_, bc, bc_, tmp);

                for (size_t i4 = i3+1; i4 < vars.size(); i4++) {
                    cd.clear();
                    cd.push_back(vars[i3]);
                    cd.push_back(vars[i4]);
                    cd_ = aliases[cd];
                    assert(cd_ != 0);
                    sort(cd.begin(), cd.end());
                    ptable2Add(ab,ab_, cd, cd_, tmp);

                }
            }
        }
    }
}

string ts(unsigned long long n1, const vector<int32_t>& vars) {
    vector<int32_t> lhs;
    unsigned long long bit;
    unsigned long long tmp;
    for (size_t i = 0; i < vars.size(); i++) {
        bit = i;
        tmp = 1;
        tmp <<= bit;
        if (n1 & tmp) {
            lhs.push_back(vars[i]);
        }
    }
    return toString(lhs);

}
void ptable(int k, vector<int32_t> vars) {
    unsigned long long n1 = 0, n2 = 0, n3 = 0;
    unsigned long long limit = 1;
    unsigned long long bit = vars.size();
    unsigned long long tmp;
    limit <<= bit;
    vector<int32_t> lhs;
    lhs.reserve(vars.size());
    sort(vars.begin(), vars.end());
    cerr << "ptable(" << k << "," << toString(vars) << ")" << endl;
    if (abs(k) == 2) {
        ptable2(vars);
        return;
    }
    if (vars.size() > 63) {
        cerr << "you really do NOT want to print a ptable of " << vars.size()
            << " variables" << endl;
        exit(-1);
    }
    for (n1 = 1; n1 < limit; n1++) {
        lhs.clear();
        for (size_t i = 0; i < vars.size(); i++) {
            bit = i;
            tmp = 1;
            tmp <<= bit;
            if (n1 & tmp) {
                lhs.push_back(vars[i]);
                if (k && lhs.size() > k)
                    break;
            }
        }
        if (k == 0 || lhs.size() <= k) {


            if (aliases.find(lhs) == aliases.end()) {

                aliases[lhs] = nextVar;
                lhs.push_back(nextVar);
                nextVar++;
            }
        }

    }
    for (n1 = 1; n1 < limit; n1++) {
 
                lhs.clear();
                for (size_t i = 0; i < vars.size(); i++) {
                    bit = i;
                    tmp = 1;
                    tmp <<= bit;
                    if (n1 & tmp) {
                        lhs.push_back(vars[i]);
                        if (k && lhs.size() > k)
                            break;
                    }
                }
                if (k && lhs.size() > k)
                    continue;
                assert(aliases.find(lhs) != aliases.end());

                int aa1 = aliases[lhs];
                assert(aa1 != 0);


        for (n2 = n1+1; n2 < limit; n2++) {
            int a1 = aa1;

            n3 = n1 ^ n2;
            if (n3) {
                               lhs.clear();
                for (size_t i = 0; i < vars.size(); i++) {
                    bit = i;
                    tmp = 1;
                    tmp <<= bit;
                    if (n2 & tmp) {
                        lhs.push_back(vars[i]);
                        if (k && lhs.size() > k)
                            break;
                    }
                }
                if (k && lhs.size() > k)
                    continue;
                assert(aliases.find(lhs) != aliases.end());
                int a2 = aliases[lhs];
                assert(a2 != 0);
                lhs.clear();
                for (size_t i = 0; i < vars.size(); i++) {
                    bit = i;
                    tmp = 1;
                    tmp <<= bit;
                    if (n3 & tmp) {
                        lhs.push_back(vars[i]);
                        if (k && lhs.size() > k)
                            break;
                    }
                }
                if (k && lhs.size() > k)
                    continue;
                if (aliases.find(lhs) == aliases.end())
                    continue;
                int a3 = aliases[lhs];
                assert(a3 != 0);
                bool rhs = false;
                if (a1 < 0) {
                    rhs = !rhs;
                    a1 = -a1;
                }
                if (a2 < 0) {
                    rhs = !rhs;
                    a2 = -a2;
                }
                if (a3 < 0) {
                    rhs = !rhs;
                    a3 = -a3;
                }

                D(ts(n1,vars) << " + " << ts(n2,vars) << " = " << ts(n3, vars));
                lhs.clear();
                if (a1 == a2)
                    lhs.push_back(a3);
                else if (a1 == a3)
                    lhs.push_back(a2);
                else if (a2 == a3)
                    lhs.push_back(a1);
                else {
                    lhs.push_back(a1);
                    lhs.push_back(a2);
                    lhs.push_back(a3);
                }


                sort(lhs.begin(), lhs.end());
                if (addClause(lhs, rhs)) {
                    addAliases(lhs, rhs);
                }
            }
        }
    }

}
int32_t readClauses(vector<vector<int32_t> >& lhs,
                vector<bool>& rhs) {
    string line;

    typedef boost::tokenizer<boost::char_separator<char> > tokenizer;

    vector<int32_t> nums;
    bool started = false;
    while (getline(cin, line)) {

        if (line.empty())
            continue;

        boost::char_separator<char> sep(" ");
        if (line[0] != 'x') {
            if (line.substr(0,9) == "c ptable(" && line[line.size() - 1] == ')') {
                if (!started) {
                    for (int32_t i = 1; i <= maxVar; i++) {
                        nums.clear();
                        nums.push_back(i);
                        aliases[nums] = i;

                    }
                    nextVar = maxVar+1;
                }
                started = true;
                boost::char_separator<char> sep2(",");
                string params = line.substr(9, line.size() - 10);
                tokenizer tok(params, sep2);
                int part = 0;
        
                int k=-1;
                nums.clear();
                for (tokenizer::iterator i = tok.begin();
                    i != tok.end(); i++) {
                    string token = *i;
                    switch(++part) {
                        case 1:
                            k = atoi(i->c_str());
                            break;
                        case 2:
                            {
                                
                                tokenizer tok2(token, sep);
                                for (tokenizer::iterator i2 = tok2.begin(); i2 != tok2.end(); i2++) {
                                    nums.push_back(atoi(i2->c_str()));
                                }
                            }
                            break;
                        case 3:
                            cerr << "invalid syntax in line : " << line << endl;
                            exit(1);   
                           break; 
                    }
                }
                if (nums.empty()) {
                    cerr << "empty ptable requested : " << line << endl;
                    exit(1);
                }
                ptable(k, nums);

            } 
            else {
                cout << line << endl;
            }
            continue;
        }
        if (started) {
            cerr << "ptables must be in the end!" << endl;
            exit(1);
        }

        tokenizer tok(line, sep);
        bool r = true;
        nums.clear();
        for (tokenizer::iterator i = tok.begin();
                i != tok.end(); i++) {
            int32_t num = atoi((*i).c_str());
            if (num) {
                if (num < 0)
                    r = !r;

                nums.push_back(abs(num));
                if (abs(num) > maxVar)
                    maxVar = abs(num);
            }

        }
        if (line[0] == 'x') {
            sort(nums.begin(), nums.end());
            bool isNew = addClause(nums, r);
            if (isNew) {
                addAliases(nums, r);
            }
        }

    }

    return maxVar;
}

int main(int argc, char** argv) {
    vector<vector<int32_t> > lhs;
    vector<bool> rhs;
    int32_t maxVar = readClauses(lhs, rhs);
    
    return 0;
}
