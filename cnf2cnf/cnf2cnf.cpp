#include <iostream>
#include <set>
#include <boost/tokenizer.hpp>
#include <map>
#include <algorithm>
#include <boost/program_options.hpp>

namespace po = boost::program_options;


using namespace std;

class Cnf2Cnf {

    std::vector< std::vector<int> > clauses;
    int maxVar;
public:
    Cnf2Cnf();
    void add(const vector<int>& d);
    void dump();
    void read();
};

Cnf2Cnf::Cnf2Cnf() {
}
void Cnf2Cnf::read() {

    string line;
    while (!cin.eof()) {
        getline(cin, line);

        if (line.empty())
            continue;

        if (line[0] == 'p') {
            continue;
        }
        if (line[0] == 'c')
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
            }
        }
        add(nums);
    }
    
}

void Cnf2Cnf::add(const vector<int>& d) {

    clauses.push_back(d);
    for (size_t i = 0; i < d.size(); i++) {
        if (abs(d[i]) > maxVar)
            maxVar = abs(d[i]);
    }
}


void Cnf2Cnf::dump() {
    cout << "p cnf " << maxVar << " " << clauses.size() << endl;
    for (size_t i = 0; i < clauses.size(); i++) {
        for (size_t i2 = 0; i2 < clauses[i].size(); i2++) {
            cout << clauses[i][i2] << " ";
        }
        cout << 0 << endl;
    }

}
int main(int argc, char** argv) {
    Cnf2Cnf cnf2cnf;
    cnf2cnf.read();
    cnf2cnf.dump();
    return 0;
}
