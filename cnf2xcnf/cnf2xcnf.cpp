#include <iostream>
#include <set>
#include <boost/tokenizer.hpp>
#include <map>
#include <algorithm>

using namespace std;

class Cnf2Xcnf {
    std::vector< std::vector<int> > cnf;
    size_t pos;

public:
    Cnf2Xcnf();
    void add(const vector<int>& d);
    void prepare();
    void extract(std::vector<int>& xorClause, vector<int>& d);
    void read();
};

struct XorSort {
    bool operator()(const vector<int>& d1, const vector<int>& d2) {
        if (d1.size() < d2.size())
            return true;
        else if (d1.size() > d2.size())
            return false;

        int neg1 = 0, neg2 = 0;
        for (size_t i = 0; i < d1.size(); i++) {
            if (d1[i] < 0)
                neg1++;
            if (d2[i] < 0)
                neg2++;
            if (abs(d1[i]) < abs(d2[i]))
                return true;
            if (abs(d1[i]) > abs(d2[i]))
                return false;
        }
        int par1 = neg1 % 2;
        int par2 = neg2 % 2;
        return par1 < par2;
    }
};

struct LiteralSort {
    bool operator()(const int l1, const int l2) {
        return abs(l1) < abs(l2);
    }
};
Cnf2Xcnf::Cnf2Xcnf() : pos(0) {
}
void Cnf2Xcnf::read() {

    string line;
    while (getline(cin, line)) {

        if (line.empty())
            continue;
        if (line[0] == 'c' || line[0] == 'p') {
            continue;
        }
        if (line[0] == 'x') {
            cout << line << endl;
            continue;
        }

        typedef boost::tokenizer<boost::char_separator<char> > 
            tokenizer;
        boost::char_separator<char> sep(" ");
        tokenizer tok(line, sep);
        vector<int> nums;
        for (tokenizer::iterator i = tok.begin();
                i != tok.end(); i++) {
            int num = atoi((*i).c_str());
            if (num) {
                nums.push_back(num);
            }
        }
        add(nums);
    }
}

void Cnf2Xcnf::add(const vector<int>& d) {

    cnf.push_back(d);
    sort(cnf.back().begin(),
            cnf.back().end(),
            LiteralSort());

}

void Cnf2Xcnf::prepare() {
    sort(cnf.begin(), cnf.end(), XorSort());
    cnf.erase(std::unique(cnf.begin(), cnf.end()), cnf.end());
}

void Cnf2Xcnf::extract(std::vector<int>& xorClause, vector<int>& orClause) {
    
    xorClause.clear();
    orClause.clear();

    while (pos < cnf.size()) {
        size_t start = pos;
        vector<int>& d = cnf[start];
        int parity = 0;
        int vars = d.size();
        if (vars == 1) {
            orClause = d;
            pos++;
            return;
        }
        if (vars > 16) {
            orClause = d;
            pos++;

            return;
        }

        int expect = (1 << (vars-1)) -1;

//        cerr << "Checking clause";


        for (size_t i = 0; i < d.size(); i++) {
//            cerr << " " << d[i];
            if (d[i] < 0)
                parity = 1 - parity;
        }
//        cerr << " and expecting " << expect << " more clauses with parity " << parity << endl;

        pos += expect;
        if (pos >= cnf.size()) {
            pos -= expect;
            orClause = d;
            pos++;
            return;
        }
        int parity2 = 0;
        vector<int>& d2 = cnf[pos++];
        size_t match = 0;
        for (size_t i = 0; i < d2.size(); i++) {
            if (abs(d[i]) != abs(d2[i])) {
                break;
            }
            if (d2[i] < 0)
                parity2 = 1 - parity2;
            match++;
        }
        
        if (match == d.size() && parity2 == parity) {
//            cerr << " found match! xor-clause :";
            for (size_t i = 0; i < d.size(); i++) 
                xorClause.push_back(abs(d[i]));
            if (parity) {
                xorClause[0] = -xorClause[0];
            }
/*            for (size_t i = 0; i < xorClause.size(); i++) {
                cerr << " " << xorClause[i];
            }
            cerr << endl;*/
           

            

            return;
        } else {
            pos -= expect;
            orClause = d;
            return;
        }
    }
}
int main(int argc, char** argv) {
    Cnf2Xcnf cnf2xcnf;
    cnf2xcnf.read();
    cnf2xcnf.prepare();

    vector<int> xorClause, orClause;
    while (1) {

        cnf2xcnf.extract(xorClause, orClause);
        if (!xorClause.empty()) {
            cout << "x";
            for (size_t i = 0; i < xorClause.size(); i++) {
                cout << " " << xorClause[i];
            }
            cout << " 0" << endl;
        } else if (!orClause.empty()) {
            for (size_t i = 0; i < orClause.size(); i++) {
                cout << ((i != 0) ? " " : "") << orClause[i];
            }
            cout << " 0" << endl;
        } else 
            break;
    }

    return 0;
}
