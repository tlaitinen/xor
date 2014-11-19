#ifndef __timestamp_hpp_
#define __timestamp_hpp_

#include <map>
#include <limits>
//#define MAX_TIMESTAMP 100000 
#define MAX_TIMESTAMP std::numeric_limits<int>::max()
namespace bx {
class TimestampRemapper {
    std::map<int, int> ts;
public:   
    void add(int t) {
        ts[t] = 1;
    }
    int compress() {
        int c = 1;
        for (std::map<int, int>::iterator i = ts.begin(); i != ts.end(); i++) {
            i->second = c++;
        }        
        assert(c < MAX_TIMESTAMP / 2);
        return c;
    }
    int remap(int t) const {
        std::map<int, int>::const_iterator i = ts.find(t);
        assert (i != ts.end());
        return i->second;
    }
};
}

#endif
