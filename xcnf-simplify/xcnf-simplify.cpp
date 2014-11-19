#include <iostream>
#include <set>
#include <boost/tokenizer.hpp>
#include <map>
#include <algorithm>
#include <boost/program_options.hpp>
#include <set>
#include <sys/time.h>
using namespace std;
  template <class T> std::string toString(const T& t) {
        std::ostringstream ost;
        ost << t;
        return ost.str();
    }

 template <> std::string toString(const set<int32_t>& s) {
     std::ostringstream ost;
     for (set<int32_t>::const_iterator si = s.begin(); si != s.end(); si++) {
         if (si != s.begin())
             ost << " ";
         ost << toString(*si);
     }
     return ost.str();
 }



namespace po = boost::program_options;


class Subsets {
    int n;
    size_t kLimit;
    bool restart;
    vector<int32_t> elems;
    vector<bool> v;
public:
    Subsets(const set<int32_t>& s, size_t kLimit_ = 0) 
        : n(1), kLimit(kLimit_), restart(true) {
        copy(s.begin(), s.end(), back_inserter(elems));
        v.resize(elems.size());

    }
    bool next(set<int32_t>& sub) {
        if (n > elems.size() || (kLimit > 0 && n > kLimit))
            return false;
        if (restart) {
            fill(v.begin(), v.end(), false);
            fill(v.begin() + n, v.end(), true);
            restart = false;
        }
      
       sub.clear(); 
       for (int i = 0; i < elems.size(); ++i) {
           if (!v[i]) {
               sub.insert(elems[i]);
           }
       }
       if (!next_permutation(v.begin(), v.end())) {
           n++;
           restart = true;
       }
       return true;
    }
};


typedef map< set<int32_t>, pair<int32_t, bool> > AliasMap;

class XcnfSimplify {

    AliasMap aliasMap;
    vector<int> values;
public:
    XcnfSimplify();
    void read();
};

XcnfSimplify::XcnfSimplify()  {
}
void XcnfSimplify::read(){

    string line;
    while (!cin.eof()) {
        getline(cin, line);

        if (line.empty())
            continue;

        if (line[0] != 'x') {
            cout << line << endl;
            continue;
        }

        typedef boost::tokenizer<boost::char_separator<char> > 
            tokenizer;
        boost::char_separator<char> sep(" ");
        tokenizer tok(line, sep);
        set<int32_t> nums;
        bool rhs = true;
        for (tokenizer::iterator i = tok.begin();
                i != tok.end(); i++) {
            int32_t num = atoi((*i).c_str());
            if (num) {
                if (num < 0) {
                    num = abs(num);
                    rhs = !rhs;
                }
                if (values.size() <= num)
                    values.resize(num+1);
                if (nums.find(num) == nums.end())
                    nums.insert(num);
                else
                    nums.erase(num);
            }
        }
        bool done = false;
        while (!done) {
            Subsets s(nums);
            set<int32_t> sub;
            bool found = false;
            while (s.next(sub)) {
                AliasMap::const_iterator a = aliasMap.find(sub);
                if (a != aliasMap.end()) {

                    int32_t aliasVar = a->second.first;
                    bool aliasSign = a->second.second;
#ifdef DEBUG
                    cerr << "    Simplifying " << toString(nums) << " := " 
                        << (rhs ? "T" : "F")
                        << " with "
                        << (aliasSign ? "-" : "") 
                        << aliasVar
                        << " := " 
                        << toString(a->first)
                        << endl;

#endif
                    for (set<int32_t>::const_iterator si = sub.begin();
                            si != sub.end(); si++) {
                        nums.erase(*si);
                    }
                    if (aliasSign)
                        rhs = !rhs;
                    if (nums.find(aliasVar) == nums.end())
                        nums.insert(aliasVar);
                    else 
                        nums.erase(aliasVar);
                    found = true;
                    break;
                }
            }
            if (!found)
                break;
        }
        if (nums.empty() && rhs == false) {
#ifdef DEBUG
            cerr << "    Simplification eliminated the clause!" << endl;
#endif
            continue;
        }
        if (nums.empty() && rhs == true) {
#ifdef DEBUG
            cerr << "    F := T after simplification" << endl;
#endif

            cout << "1 0" << endl;
            cout << "-1 0" << endl;
            return;
        }
        for (set<int32_t>::const_iterator ni = nums.begin();
                ni != nums.end(); ni++) {
            set<int32_t> n = nums;
            n.erase(*ni);

            if (n.empty())
                continue;
            if (n.size() == 1 && *ni > *n.begin()) {
                // do not add equivalences to both directions
                // to prevent loops
                continue;
            }
            if (aliasMap.find(n) != aliasMap.end()) {
                cerr << toString(n) << " already has an alias!" << endl;
            }
            assert(aliasMap.find(n) == aliasMap.end());
#ifdef DEBUG
            cerr << "    " << (rhs ? "-" : "") << *ni << " := " << toString(n) << endl;
#endif

            aliasMap[n] = make_pair(*ni, rhs);
        }
        if (nums.size() == 1) {
            int v = *nums.begin();
            int value = rhs ? 1 : -1;
            if (values[v]) { 
                if (values[v] != value) {
#ifdef DEBUG
                    cerr << "    Both values for variable " << v << endl;
#endif
                    cout << " 1 0" << endl;
                    cout << " -1 0" << endl;

                    return;
                } else {
#ifdef DEBUG
                    cerr << "    Variable " << v << " already has a value" 
                        << endl;
#endif

                    continue;
                }
            }
            values[v] = rhs ? 1 : -1;
        }
        cout << "x " << (!rhs ? "-" : "") << toString(nums) << " 0 " << endl;
    }
}

int main(int argc, char** argv) {
    struct timeval start, stop;
    gettimeofday(&start, NULL);

    po::options_description desc("Allowed options");

    desc.add_options()
         ("help,h", "produce help message")
            ;

    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);    

    if (vm.count("help")) {
            cout << desc << "\n";
                return 1;
    }
    XcnfSimplify xcnfSimplify;
    xcnfSimplify.read();
    gettimeofday(&stop, NULL);
    long double s = (long double)( stop.tv_sec * 1000000.0)
                  - (long double)(start.tv_sec * 1000000.0)
                  + (long double)(stop.tv_usec - start.tv_usec);

    cout << "c xcnf-simplify took " << s / 1000000.0 << " seconds" << endl;



 
    return 0;
}
