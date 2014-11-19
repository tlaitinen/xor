#ifndef _util_hpp_
#define _util_hpp_
#include <sstream>
#include <vector>
#include <string>
#include <set>
#include <iostream>
#include <map>
#ifdef DEBUG
#define D(lvl,x)  if (lvl) { std::cout << x << std::endl; }
#else
#define D(lvl,x)
#endif


namespace bx {
    namespace dbg {
        extern int fud, bcg, prop, state, parexp;
    }
    template <class T> std::string toString(T t) {
        std::ostringstream ost;
        ost << t;
        return ost.str();
    }
    /** A class for communicating conflict literals (from Simplex) */
    class Lit {
        unsigned int x;
        public:
        Lit() : x (0) {}
        Lit(const Lit& other) {x = other.x; }
        void operator=(const Lit& other) {x = other.x;  }
        Lit(unsigned int v, bool sign) {x = (v + v) + (sign?1:0); }
        /** Return the variable index */
        unsigned int get_var() const {return(x >> 1); }
        /** Returns true if the literal is negated */
        bool get_sign() const {return (x & 1); }

        Lit neg() const {
            Lit l;
            l.x = x ^ 1;
            return l;
        }
    };

    template <> std::string toString<Lit>(Lit l);

    template <> std::string toString<std::vector<Lit> > (std::vector<Lit> lits);
    template <> std::string toString<std::vector<Lit> > (std::vector<Lit> lits);
    template <> std::string toString<std::vector<int> > (std::vector<int> lits);
    template <>
std::string toString<std::set<int> > (std::set<int> lits) ;
    template <>
std::string toString<std::set<std::string> > (std::set<std::string> lits);



    void writeFile(const std::string& path, const std::string& s);

}
#endif
