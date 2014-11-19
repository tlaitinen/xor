#include <iostream>
#include <set>
#include <boost/tokenizer.hpp>
#include <map>
#include <algorithm>
#include <boost/program_options.hpp>

namespace po = boost::program_options;


using namespace std;

class Xcnf2Cnf {

    std::vector< std::vector<int> > clauses;
    std::vector<bool> eliminated;
    std::map<int, int> occ;
    

    size_t pos;

public:
    Xcnf2Cnf();
    void add(const vector<int>& d);
    void dump();
    void read(bool partial, bool treelike);
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
Xcnf2Cnf::Xcnf2Cnf() : pos(0) {
}
void dumpXor(vector<int>& ps) {
    vector<int> cl;
    const size_t p = 1 << ps.size();
    //        fprintf(stderr, "%u ", p);
    for(size_t i = 0; i < (1 << ps.size()); i++) {
        size_t nof_ones = 0;
        cl.clear();
        for (int j = 0; j < ps.size(); j++) {
            bool one = (i & (1 << j)) != 0;
            cl.push_back(one?-ps[j]:ps[j]);
            if(one) nof_ones++;
        }
        if(((nof_ones % 2) == 0)) {
            
            for (size_t j = 0; j < cl.size(); j++) {
                cout << cl[j] << " ";

            }
            cout << "0" << endl;
        }
    }
}
void Xcnf2Cnf::read(bool partial, bool treelike) {

    string line;
    bool treelikeComponent = false;
    while (!cin.eof()) {
        getline(cin, line);

        if (line.empty())
            continue;

        if (line[0] != 'x') {
            if (line[0] == 'p') {
                size_t idx = line.find("p xcnf");
                if (idx != string::npos) {
                    line = line.replace(idx, 6, "p cnf");
                }
            }
            if (line == "c xor-tree-like-component")
                treelikeComponent = true;
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
        if (partial)
            add(nums);
        else {
            if (treelike) {
                if (treelikeComponent)
                    dumpXor(nums);
                else
                    cout << line << endl;
            } else
                dumpXor(nums);
        }
        
    }
}

void Xcnf2Cnf::add(const vector<int>& d) {

    clauses.push_back(d);
    eliminated.push_back(false);
    for (size_t i = 0; i < d.size(); i++) {
        occ[abs(d[i])]++;
    }
}


void Xcnf2Cnf::dump() {

    bool saturated = false;
    size_t elim = 0;
    size_t total = clauses.size();
    while (!saturated) {
        saturated = true;
        for (size_t i = 0; i < clauses.size(); ) {
            if (eliminated[i]) {
                i++;
                continue;

            }

            vector<int>& clause = clauses[i];

            int numOcc = 0;
            for (size_t j = 0; j < clause.size(); j++) {
                
                if (occ[abs(clause[j])] > 1)
                    numOcc++;
            }
            if (numOcc <= 1) {
                elim++;
                for (size_t j = 0; j < clause.size(); j++) {
                    occ[abs(clause[j])]--;
                }
                dumpXor(clause);
                eliminated[i] = true;
                saturated = false;
            } else
                i++;
        }
    }
    for (size_t i = 0; i < clauses.size(); i++) {
        if (eliminated[i])
            continue;
        vector<int>& clause = clauses[i];
        cout << "x";
        for (size_t j = 0; j < clause.size(); j++) {
            cout << " " << clause[j];

        }
        cout << " 0" << endl;

    }
    cerr << elim << "/" << total << " xor-clauses clausified" << endl;
}
int main(int argc, char** argv) {
    po::options_description desc("Allowed options");

    desc.add_options()
         ("help,h", "produce help message")
         ("partial,p","partial treelike xcnf2cnf translation")
         ("treelike,t","translate xor-clauses after 'c xor-tree-like-component'")
            ;

    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);    

    if (vm.count("help")) {
            cout << desc << "\n";
                return 1;
    }
    bool partial = vm.count("partial");
    bool treelike = vm.count("treelike");
    Xcnf2Cnf xcnf2cnf;
    xcnf2cnf.read(partial, treelike);
    if (partial)
        xcnf2cnf.dump();
    return 0;
}
