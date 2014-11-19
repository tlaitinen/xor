#include "util.hpp"

#include <sstream>
#include <fstream>
using namespace std;
namespace bx {
    namespace dbg {
        int fud = 0;
        int bcg = 0;
        int prop = 0 ;     
        int parexp = 1;
        int state = 0;
    }
    template <> std::string toString<Lit>(Lit l) {
    return (l.get_sign() ? "~x" : " x" ) + toString(l.get_var());
}

template <> std::string toString<std::vector<Lit> > (std::vector<Lit> lits) {
    std::ostringstream ost;
    for (size_t i = 0; i < lits.size(); i++) {
        if (i)
            ost << " ";
        ost << toString(lits[i]);

    }
    return ost.str();

}
template <> std::string toString<std::vector<int> > (std::vector<int> lits) {
    std::ostringstream ost;
    for (size_t i = 0; i < lits.size(); i++) {
        if (i)
            ost << " ";
        ost << toString(lits[i]);
    }
    return ost.str();
}
template <>
std::string toString<std::set<int> > (std::set<int> lits) {
    std::ostringstream ost;
    bool first = true;
    for (set<int>::iterator i = lits.begin(); i != lits.end(); i++) {
        if (!first)
            ost << " ";
        first = false;
        ost << toString(*i);
    }
    return ost.str();
}
template <>
std::string toString<std::set<std::string> > (std::set<std::string> lits) {
    std::ostringstream ost;
    bool first = true;
    for (set<std::string>::iterator i = lits.begin(); i != lits.end(); i++) {
        if (!first)
            ost << " ";
        first = false;
        ost << toString(*i);
    }
    return ost.str();
}
void writeFile(const std::string& path, const std::string& s) {
    std::ofstream f;
    f.open(path.c_str());
    f << s;
    f.close();
}

}
 
