#include <iostream>
#include <set>
#include <boost/tokenizer.hpp>
#include <map>
#include <algorithm>
#include <boost/program_options.hpp>
#include <sys/types.h>
#include <unistd.h>

namespace po = boost::program_options;


using namespace std;

class Xcnf3Xcnf {

    std::vector< std::pair<std::vector<int>, bool> > clauses;
    int maxVar;
    int newVars;

public:
    Xcnf3Xcnf();
    void read();
    void write();
};


bool ugly = false;

Xcnf3Xcnf::Xcnf3Xcnf() : maxVar(0), newVars(0) {
}
void Xcnf3Xcnf::read() {

    string line;
    while (getline(cin, line)) {

        if (line.empty())
            continue;
        if (line[0] == 'c' || line[0] == 'p')
            continue;

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
                if (abs(num) > maxVar)
                    maxVar = abs(num);
            }
            
        }
        if (nums.size() > 3 && line[0] == 'x')
            newVars += nums.size() - 3;
        if (nums.size() == 2 && line[0] == 'x' && ugly)
            newVars++;
        clauses.push_back(make_pair(nums, line[0] == 'x'));
    }
}
void dump(vector<int>& d, bool xorClause) {
    if (xorClause)
        cout << "x ";
    for (size_t i = 0; i < d.size(); i++) {
        cout << ((i != 0) ? " " : "") << d[i];
    }
    cout << " 0" << endl;
}

void Xcnf3Xcnf::write() {
    int nextVar = maxVar + 1;
    cout << "p cnf " << (maxVar + newVars) << " " << clauses.size() + newVars << endl;
    for (size_t i = 0; i < clauses.size(); i++) {
        vector<int>& c = clauses[i].first;
        bool xorClause = clauses[i].second;
        
        if (!xorClause || c.size() <= 3) {
            if (ugly && c.size() == 2) {
                c.push_back(nextVar);
                vector<int> mini;
                mini.push_back(-nextVar);
                dump(mini,false);
                nextVar++;
            }
            dump(c, xorClause);
        } else {

            vector<int> ternary;
            size_t p = 0;
            while (p < c.size()) {
                ternary.push_back(c[p++]);
                if (ternary.size() == 2 && p < c.size() - 1) {
                    ternary.push_back(nextVar);
                    dump(ternary,true);
                    ternary.clear();
                    ternary.push_back(-nextVar);
                    nextVar++;
                }
                if (ternary.size() == 3)  {
                    dump(ternary,true);
                    ternary.clear();
                }
            }
           }
    }

}

int main(int argc, char** argv) {
    if (argc == 2 && string(argv[1]) == "-u")
        ugly = true;

    Xcnf3Xcnf xcnf3xcnf;
    xcnf3xcnf.read();
    xcnf3xcnf.write();
    return 0;
}
