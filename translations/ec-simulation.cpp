#include <iostream>
#include <set>
#include <stdint.h>
#include <boost/tokenizer.hpp>
#include <map>
#include <boost/program_options.hpp>
#include <sys/time.h>
#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
namespace po = boost::program_options;

using namespace std;
using boost::tuple;
using boost::make_tuple;

#define D(x) if (verbose) { cerr << x << endl; }

bool verbose, printStats, stopFlag;

struct Stats {
    int newClauses;
    int newVariables;
    int numEliminated;
} stats;

class Alias {
    int32_t varId;
public:    
    Alias() : varId(0) {}
    Alias(int32_t v, bool n) : varId(n ? -v : v) {}

    int32_t getVarId() const  {
        return abs(varId);
    }
    bool getSign() const {
        return varId < 0;
    }
};

typedef map< pair<int32_t, int32_t>, Alias > AliasMap;

typedef tuple<int32_t, int32_t, int32_t> Triple;

typedef set<Triple> Triples;

struct Friend {
    int32_t clauseId;
    int32_t varId;
    Alias alias;
    Friend(int32_t cni, int vni, Alias alias_) 
        : clauseId(cni), varId(vni), alias(alias_) {}
            
};
typedef vector<Friend> Friends;

struct Var {
    int32_t id;
    bool eliminated;
    bool alias;
    Friends friends;
    bool value;
    bool scheduled;
        
    Var(int32_t i) : id(i),
      eliminated(false), alias(false), value(false), scheduled(false) {}

    void addFriend(const Friend& f) {
        D( "Var " << id << "::addFriend(" << f.clauseId << "," << f.varId << "," << f.alias.getVarId() << ")");
        assert(f.varId != id);
        for (size_t i = 0; i < friends.size(); i++) {
            if (friends[i].varId == f.varId)
                return;
        }
        friends.push_back(f);

    }
    void removeFriend(int32_t n) {
        for (size_t i = 0; i < friends.size(); i++) {
            if (friends[i].varId == n) {
                friends[i] = friends.back();
                friends.pop_back();
                return;
            }
        }
    }
};

void sort(int32_t &a, int& b, int &c) {
    assert(a != b && b != c);
    if (a>b)swap(a,b); 
    if (b>c)swap(b,c);
    if (a>b)swap(a,b); 
    assert(a < b && b < c);
}

class XorGraph {

    int32_t clauseIdSeq;
    typedef vector<Var> Vars;

    Vars vars;
    AliasMap aliasMap;
    vector<pair<Friend, Friend> > friendPairs;
    Triples triples;
    size_t lastCleanup;
    size_t remainingVars;

    bool started;
    size_t maxClauses;

    void makeFriends(int32_t v1, int32_t v2, int32_t c, Alias a) {
        
        D( "makeFriends(" << v1 << "," << v2 << ")" );
        assert(v1 != v2);
        assert(v1 >= 0 && v1 < (int) vars.size());
        assert(v2 >= 0 && v2 < (int) vars.size());
        if (vars[v1].eliminated || vars[v2].eliminated
                || vars[v1].alias || vars[v2].alias)
            return;
        assert(!vars[v1].eliminated);
        assert(!vars[v2].eliminated);
        vars[v1].addFriend(Friend(c, v2, a));
        vars[v2].addFriend(Friend(c, v1, a));
    }

public:    
    XorGraph(size_t maxClauses_) : clauseIdSeq(1), lastCleanup(0), remainingVars(0), started(false), maxClauses(maxClauses_) {
        vars.push_back(Var(0));
    }
    int32_t addVar() {
        int32_t id = vars.size();
        vars.push_back(Var(vars.size()));
        return id;
    }

    Alias getAlias(int32_t v1, int32_t v2) const {
        if (v1 > v2) 
            swap(v1,v2);
        AliasMap::const_iterator i = aliasMap.find(make_pair(v1,v2));
        if (i == aliasMap.end())
            return Alias(0,false);
        return i->second;
    }


    void storeAlias(int32_t v1, int v2, Alias a) {
        assert(getAlias(v1,v2).getVarId() == 0);
        if (v1 > v2) 
            swap(v1,v2);
        aliasMap[make_pair(v1,v2)] = a;
    }

    Alias getOrCreateAlias(int32_t v1, int v2) {
        Alias a = getAlias(v1,v2);
        if (a.getVarId()) {
            D( "Found existing alias for (" << v1 <<"," << v2 << ")");
            return a;
        }
        int32_t an = addVar();
        vars[an].eliminated = true;
        vars[an].alias = true;
        cout << "c % " << vars[an].id << endl;
        stats.newVariables++;

        D( "New alias for (" << v1 <<"," << v2 << ")");
        addClause(vars[an].id, v1, v2, true);

        return getAlias(v1,v2);            
    }

    
    bool hasClause(int32_t v1,int v2, int v3) {
        assert (v1 != v2 && v2 != v3);

        sort(v1,v2,v3);
        return triples.find(Triple(v1,v2,v3)) != triples.end();
    }


    int32_t addClause(int v1, int v2, int v3, bool rhs) {
        assert(v1 >= 1 && v2 >= 1 && v3 >= 1);
        assert(v1 != v2 && v2 != v3);
        
        sort(v1,v2,v3);
        assert(hasClause(v1,v2,v3) == false);
        size_t needVars = max(v1,max(v2,v3));
        while (vars.size() <= needVars) {
            addVar();
        }

        if (started) {
            stats.newClauses++;

            cout << "x " << (rhs ? v1 : -v1)
                << " "  << v2
                << " "  << v3
                << " 0" << endl;

            if (maxClauses && stats.newClauses >= maxClauses) {
                cerr << "Reached maximum number of " << maxClauses 
                    << " new clauses" << endl;
                stopFlag = true;    
            }
        }

        D("Adding clause " << v1 << " " << v2 << " " << v3 << " = " << rhs  );

        triples.insert(Triple(v1,v2,v3));

        if (!getAlias(v1,v2).getVarId())
            storeAlias(v1,v2,Alias(v3,!rhs));
        if (!getAlias(v1,v3).getVarId())
            storeAlias(v1,v3,Alias(v2,!rhs));
        if (!getAlias(v2,v3).getVarId())
            storeAlias(v2,v3,Alias(v1,!rhs));

        int32_t c = clauseIdSeq++;
        makeFriends(v1, v2, c,  Alias(v3,!rhs));
        makeFriends(v1, v3, c, Alias(v2,!rhs));
        makeFriends(v2, v3, c, Alias(v1,!rhs));

        return c;
    }

    void read() {

        string line;
        bool not3xcnf = false;
        while (!cin.eof()) {
            getline(cin, line);

            cout << line << endl;
            if (line.empty())
                continue;
            if (line[0] != 'x') {
                continue;
            }

            typedef boost::tokenizer<boost::char_separator<char> > 
                tokenizer;
            boost::char_separator<char> sep(" ");
            tokenizer tok(line, sep);
            int32_t v1 = 0, v2 = 0, v3 = 0;
            bool rhs = true;
            bool more = false;
            for (tokenizer::iterator i = tok.begin();
                    i != tok.end(); i++) {
                int32_t num = atoi((*i).c_str());
                if (num) {
                    if (num < 0) {
                        rhs = !rhs;
                        num = abs(num);
                    }
                    if (v1 == 0)
                        v1 = abs(num);
                    else if (v2 == 0)
                        v2 = abs(num);
                    else if (v3 == 0)
                        v3 = abs(num);
                    else {
                        more = true;
                    }
                }
            }
            if (v1 != 0 && v2 != 0 && v3 != 0 && !more) {
                if (!hasClause(v1,v2,v3))
                    addClause( v1, v2, v3, rhs);
            } else {
                not3xcnf = true;
            }
        }
        if (not3xcnf)
            cerr << "Warning: input not in 3XCNF format" << endl;
        started = true;
        remainingVars = vars.size() - 1;
        cout << "c xupify" << endl;
    }

    Var& getVar(int32_t id)  {
        assert(id >= 0 && id <(int32_t) vars.size());
        return vars[id];
    }
    void assignAlias(Alias a, bool rhs) {

        if (!vars[a.getVarId()].value) {
            stats.newClauses++;
            cout << "x " << (!rhs ? -a.getVarId() : a.getVarId()) << " 0" << endl;
            vars[a.getVarId()].value = true;
        }
        
    }
    void eliminate(int32_t varId) {
        D( "eliminate(" << varId << ")");

        cerr << "Eliminating x" << varId 
            << " (" << remainingVars << " left). Xor-friends " 
            << vars[varId].friends.size() 
            << " Aliases " << aliasMap.size() 
            << " Clauses " << triples.size() << endl;
        Var& n = vars[varId];
        assert(n.eliminated == false);
        remainingVars--;
        int32_t v1 = n.id;

        n.eliminated = true;
        stats.numEliminated++;
        for (Friends::iterator f = n.friends.begin(); f != n.friends.end();
                f++) {
            assert (varId != f->varId);
            D( "removing friend " << varId << " from " << f->varId);

            vars[f->varId].removeFriend(varId);
        }
        friendPairs.clear();

        for (Friends::iterator f2 = n.friends.begin(); f2 != n.friends.end();
                f2++) {
            Friends::iterator f3 = f2;
            f3++;

            for (; f3 != n.friends.end(); f3++) {
                friendPairs.push_back(make_pair(*f2,*f3));
            }
        }
        for (vector<pair<Friend, Friend> >::iterator fp =  friendPairs.begin();
                fp != friendPairs.end(); fp++) {
            if (stopFlag)
                return;
            Friend& f2 = fp->first;
            Friend& f3 = fp->second;

            if (f2.clauseId != f3.clauseId) {
                D(f2.varId << " " << f3.varId 
                    << " in clauses " << f2.clauseId << " and " << f3.clauseId << 
                    " aliases " << f2.alias.getVarId() << " and " << f3.alias.getVarId());
                Alias a12 = f2.alias;
                Alias a13 = f3.alias;
                int32_t v2 = f2.varId;
                int32_t v3 = f3.varId;

                Alias a23 = getOrCreateAlias(v2, v3);
                bool rhs = true;
                if (a12.getSign())
                    rhs = !rhs;
                if (a13.getSign())
                    rhs = !rhs;
                if (a23.getSign())
                    rhs = !rhs;

                D( v1 << "=" << v2 << " : " << a12.getVarId() << " neg=" << a12.getSign());
                D( v1 << "=" << v3 << " : " << a13.getVarId() << " neg=" << a13.getSign());
                D( v2 << "=" << v3 << " : " << a23.getVarId() << " neg=" << a23.getSign());


                if (a12.getVarId() == a13.getVarId()) {
                    assignAlias(a23, rhs);
                } else if (a12.getVarId() == a23.getVarId()) {
                    assignAlias(a13, rhs);
                } else if (a13.getVarId() == a23.getVarId()) {
                    assignAlias(a12, rhs);
                } else {
                    if (!hasClause(a12.getVarId(), a13.getVarId(), a23.getVarId())) {
                        addClause(a12.getVarId(), a13.getVarId(), a23.getVarId(), rhs);
                    }
                }                              
            }
        }

        if (triples.size() > lastCleanup + 100000) {
            //cleanup();
            lastCleanup = triples.size();
        }
    }

    void cleanup() {
        size_t count = 0;
        for (Triples::iterator i = triples.begin(); i != triples.end(); ) {
            Triples::iterator next = i;
            next++;
            Triple t = *i;
            if (vars[t.get<0>()].eliminated
                    || vars[t.get<1>()].eliminated
                    || vars[t.get<2>()].eliminated) {
                count ++;
                triples.erase(i);
            }
            i = next;
        }
        cerr << "Removed " << count << " clauses from cache" << endl;
        count = 0;


        for (AliasMap::iterator i = aliasMap.begin();
                i != aliasMap.end(); ) {
            pair<int32_t, int32_t> p = i->first;
            if (vars[p.first].eliminated
                || vars[p.second].eliminated) {
                AliasMap::iterator next = i;
                next++;
                aliasMap.erase(i);
                i = next;
                count++;
            } else
                i++;
        }
        cerr << "Removed " << count << " aliases from cache" << endl;

    }

    void getLeastPopularVars(vector<int32_t>& toEliminate) {
        size_t minFriends = vars.size();

        toEliminate.clear();
        for (size_t i = 0; i < vars.size(); i++) {
            Var& n = vars[i];
            if (n.eliminated || n.friends.size() == 0)
                continue;
            n.scheduled = false;
            if (n.friends.size() < minFriends) {
                minFriends = n.friends.size();
            }
        }
        for (size_t i = 0; i < vars.size(); i++) {
            Var& n = vars[i];
            if (n.eliminated || n.friends.size() != minFriends)
                continue;
            bool friendScheduled = false;
            for (size_t i2 = 0; i2 < n.friends.size(); i2++) {
                Var& f = vars[n.friends[i2].varId];
                if (f.scheduled) {
                    friendScheduled = true;
                    break;
                }
            }
            if (!friendScheduled) {
                n.scheduled = true;
                toEliminate.push_back(i);
                for (size_t i2 = 0; i2 < n.friends.size(); i2++) {
                    Var& f = vars[n.friends[i2].varId];
                    f.scheduled = true;
                }
            }
        }

    }
};
int main(int argc, char** argv) {
    struct timeval start, stop;
    gettimeofday(&start, NULL);
    po::options_description desc("Allowed options");

    size_t maxFriends;
    size_t maxClauses;
    desc.add_options()
         ("help,h", "produce help message")
         ("verbose,v", "be verbose")
         ("stats,s","print stats")
         ("max-friends,m",po::value<size_t>(&maxFriends)->default_value(0), "xupify variables with at most (arg) xor-friends")
         ("limit,l",po::value<size_t>(&maxClauses)->default_value(0), "maximum number of xor-clauses added")
            ;

    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);    

    if (vm.count("help")) {
            cout << desc << "\n";
                return 1;
    }
    verbose = vm.count("verbose");
    printStats = vm.count("stats");
    XorGraph xg(maxClauses);
    xg.read();
    vector<int32_t> toEliminate;
    stopFlag = false;
    while (!stopFlag) {
        xg.getLeastPopularVars(toEliminate);
        if (toEliminate.empty())
            break;
        Var& n = xg.getVar(toEliminate[0]);
        cerr << "Found " << toEliminate.size() << " independent variables "
            << " " << n.friends.size() << " xor-friends" << endl;
        if (maxFriends && n.friends.size() > maxFriends) {
            cerr << "Eliminated all vars with at most " << maxFriends << 
                " xor-friends." << endl;
            break;
        }

        for (size_t i = 0; i < toEliminate.size(); i++) {
            if (stopFlag)
                break;
            int32_t varId = toEliminate[i];
            assert(varId >= 0);
            Var& n = xg.getVar(varId);
            assert(n.eliminated == false);


            
            xg.eliminate(varId);
            if (printStats) {
                cerr << "STATS eliminated " 
                     << stats.numEliminated
                     << " new-variables "
                     << stats.newVariables
                     << " new-clauses "
                     << stats.newClauses
                     << endl;
            }
        }
    }

    gettimeofday(&stop, NULL);
    long double s = (long double)( stop.tv_sec * 1000000.0)
                  - (long double)(start.tv_sec * 1000000.0)
                  + (long double)(stop.tv_usec - start.tv_usec);

    cout << "c xupify took " << s / 1000000.0 << " seconds" << endl;
    cout << "c xupify added " << stats.newClauses << endl;

    return 0;
}
