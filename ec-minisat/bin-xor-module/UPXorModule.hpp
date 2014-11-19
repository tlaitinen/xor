#ifndef _UPXorModule_hpp_
#define _UPXorModule_hpp_
#include <vector>
#include <string>
#include <algorithm>
#include <queue>
#include <assert.h>
#include "util.hpp"
#include "Simplex.h"
namespace up {
    typedef bx::Lit Lit;

    struct Clause {
        float activity;
        bool learnt;
        std::vector<Lit> lits;

        Clause(const std::vector<Lit>& lits_)
            : lits(lits_), activity(0), learnt(false) {}
        Clause() : activity(0), learnt(false) {}
        
          std::string name() {
              std::set<std::string> ints;
              for (size_t i = 0; i < lits.size(); i++) {
                  Lit l = lits[i];
                  ints.insert((l.get_sign() ? "-" : "") + bx::toString(l.get_var()));
              }
              return bx::toString(ints);
          }
    };

    class XorModule {
        private:
#ifdef DEBUG
            void checkConsistency() {
                std::map<Clause*, std::vector<int> > watchCount;
                for (size_t i = 0; i < value.size(); i++) {
                    for (size_t i2 = 0; i2 < watches[i].size(); i2++) {
                        watchCount[watches[i][i2]].push_back(i);
                    }
                }

                for (size_t i = 0; i < learnts.size(); i++) {
                    int undefs = 0, parity = 0;
                    Clause& c = *learnts[i];
                    assert(watchCount[&c].size() == 2);
                    std::vector<int>& vars = watchCount[&c];
                    if (!(vars[0] == c.lits[0].get_var()
                            || vars[0] == c.lits[1].get_var())
                            || 
                       !(vars[1] == c.lits[0].get_var()
                            || vars[1] == c.lits[1].get_var())) {
                        D(1, " watches for clause " << bx::toString(c.lits)
                                << " : " << bx::toString(vars));
                    }
                   
                    assert(vars[0] == c.lits[0].get_var()
                            || vars[0] == c.lits[1].get_var());
                    assert(vars[1] == c.lits[0].get_var()
                            || vars[1] == c.lits[1].get_var());




                    for (size_t i2 = 0; i2 < c.lits.size(); i2++) {
                        Lit l = c.lits[i2];
                        switch(litValue(l)) {
                            case Undef:
                                D(1, bx::toString(l) << " undefined");
                                undefs++;
                                break;
                            case True:
                                parity++;
                                break;
                        }
                    }

                    parity = parity % 2;
                    D(1, "undefs " << undefs << " parity " << parity);
                    if (undefs == 1) {

                        for (size_t i = 0; i < c.lits.size(); i++) {
                            D(1, "level[" << c.lits[i].get_var() << "] : " << level[c.lits[i].get_var()]);
                        }
                        D(1, "Not propagated! " << bx::toString(c.lits));
                        D(1, "implied " << bx::toString(implied));
                    } else if (undefs == 0 && parity == 0 && conflict.empty()) {
                        D(1, "no conflict! " << bx::toString(c.lits));
                    }
                    assert(undefs > 1 || ((undefs == 0 && parity == 1)
                            || !conflict.empty()));


                }
                for (int v = 0; v < value.size(); v++) {
                    if (reason[v]) {
                        assert(reason[v]->lits[0].get_var() == v);
                    }
                }
            }
#else
            void checkConsistency() {
            }
#endif

            struct Chunk {
                Clause clauses[4096];
                size_t used;
                Chunk() : used(0) {}
            };
            std::vector<Chunk*> chunks;
            std::vector<Clause*> freeClauses;
            float cla_inc;
            double clause_decay;
            int nof_learnts;
            size_t firstImplied;

            void claBumpActivity(Clause& c) {
                if ((c.activity +=  cla_inc) > 1e20) {
                    for (int i = 0; i < learnts.size(); i++)
                        learnts[i]->activity *= 1e-20;
                    cla_inc *= 1e-20; 
                }
            }
            Clause* newClause(const std::vector<Lit>& lits, bool learnt) {
                if (chunks.empty() || chunks.back()->used == 4096) {
                    chunks.push_back(new Chunk());
                }

                if (freeClauses.empty()) {
                    Chunk& c = *chunks.back();
                    freeClauses.push_back(&c.clauses[c.used++]);
                }
                Clause* clause= freeClauses.back();
                freeClauses.pop_back();
                clause->lits.clear();
                clause->learnt= learnt;
                clause->activity = 0;
                std::copy(lits.begin(), lits.end(), std::back_inserter(clause->lits));
                return clause;
            }
            void deleteClause(Clause* c) {
                freeClauses.push_back(c);
            }


            struct Backjump {
                size_t numAssumptions;
                size_t numImplied;
                size_t numTrail;
                int trailHead;

                std::vector<Clause*>  postPropagate;
#ifdef DEBUG
                std::string state;
#endif
            };
            enum { Undef=0, True=1,False=-1} ;
          std::vector<Lit> conflict;

//          std::vector<Lit> assumptions;
          std::vector<Lit> implied;
#ifdef DEBUG
          std::map<std::string, int> clauseOcc;
          Simplex simplex;
#endif
        public:
          typedef std::vector< std::vector<Lit> > PendingXors;

        private:


          std::vector<Clause*> clauses;
          std::vector<Clause*> learnts;
          std::vector<Clause*> reason;
          std::vector<char> value;
          std::vector<int> level;
          std::vector< std::vector<Clause*> > watches;
          std::vector<Backjump> backjumps;
          std::vector<int> trail;
//          std::vector<int> trailPos;
          std::vector<int> numExplained;
          std::vector<char> toExplain;
          std::vector< std::vector<Lit> > cached;
          PendingXors pendingXors;
          struct ToExplain {
              int var;
              int ts;
              ToExplain(int v, int t) : var(v), ts(t) {}
              bool operator>(const ToExplain& t) const {
                  return ts < t.ts;
              }
          };
          std::priority_queue< ToExplain, std::vector<ToExplain>, std::greater<ToExplain> > toExplainQueue;

          std::vector<char> expParity;
          std::vector<int> toExplainClear;
          int trailHead;

         
        public:
          const PendingXors& getPendingXors() const {
              return pendingXors;
          }
          void clearPendingXors() {
              pendingXors.clear();
          }
        private:

          void uncheckedEnqueue(Lit p, Clause* r) {

              level[p.get_var()] = backjumps.size();

//              trailPos[p.get_var()] = trail.size();
              trail.push_back(p.get_var());
              value[p.get_var()] = p.get_sign() ? False : True;
              if (r) {
                  D(1, "Reason for " << bx::toString(p) << " is " << bx::toString(r->lits));

                  assert(r->lits[0].get_var() == p.get_var());
              }
              reason[p.get_var()] = r;

              D(1, "Trail now : " << bx::toString(trail));
          }
          void check() {
#ifdef DEBUG
              for (size_t i = 0; i < clauses.size(); i++) {
                  Clause& c = *clauses[i];
                  for (size_t j = 0; j < 2; j++) {
                      int v = c.lits[j].get_var();
//                      D(1, "literal #" << j << " " << v);
                      int count = 0;
                      for (size_t k = 0; k < watches[v].size(); k++) {
                          if (&c == watches[v][k]) {
//                              D(1, "Clause " << bx::toString(c.lits) << " watched by " << v);
                              count++;
                          }

                      }
                      assert(count == 1);
                  }
              }
#endif
          }
          struct reduceDB_lt { bool operator () (Clause* x, Clause* y) { return x->lits.size() > 2 
              && (y->lits.size() == 2 || x->activity < y->activity); } };
          bool locked(const Clause& c) const {
              return reason[c.lits[0].get_var()] == &c;
          }
          void removeWatch(int var, Clause* c) {
              std::vector<Clause*>& ws = watches[var];
              for (int i = 0; i < ws.size(); i++) {
                  if (ws[i] == c) {
                      ws[i] = ws.back();
                      ws.pop_back();
                      return;
                  }
              }
              assert(false);
          }

          void removeClause(Clause* c) {
#ifdef DEBUG
              clauseOcc[c->name()]--;
#endif


              removeWatch(c->lits[0].get_var(), c);
              removeWatch(c->lits[1].get_var(), c);
              
              deleteClause(c);
          }


        public:
          const std::vector<Clause*>& getLearnts() const {
              return learnts;
          }
          void reduceDB()
          {
              std::cout << "UP Reduce db" << std::endl;
              D(1, "UP: reduceDB");
              int     i, j;
              double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

              std::sort(learnts.begin(), learnts.end(), reduceDB_lt());

              for (i = j = 0; i < learnts.size() / 2; i++){
                  if (learnts[i]->lits.size() > 2 && !locked(*learnts[i]))
                      removeClause(learnts[i]);
                  else
                      learnts[j++] = learnts[i];
              }
              for (; i < learnts.size(); i++){
                  if (learnts[i]->lits.size() > 2 && !locked(*learnts[i]) && learnts[i]->activity < extra_lim)
                      removeClause(learnts[i]);
                  else
                      learnts[j++] = learnts[i];
              }
              learnts.resize(j);

          }
          struct {
              long long implied;
              long long explained;
              long long learnts;
              long long conflicts;
              long long assumptions;
              long long learntLits;
              long long evenElimLits;
              long long autoLearned;
              long long explanationLits;
              long long cachedExplained;
              long long deepCuts;
          } stats;

          struct {
              bool evenElim;
              int xorLearn;
              int deepCuts;
          } settings;

          void setNumLearnts(int nof) {
              nof_learnts = nof;
          }

          XorModule() : trailHead(0), cla_inc(1), clause_decay(1 / 0.999), nof_learnts(1000) {
              firstImplied = 0;
              stats.implied = 0;
              stats.explained = 0;
              stats.learnts = 0;
              stats.learntLits = 0;
              stats.conflicts=  0;
              stats.assumptions = 0;
              stats.evenElimLits = 0;
              stats.autoLearned = 0;
              stats.explanationLits = 0;
              stats.cachedExplained = 0;
              stats.deepCuts = 0;
              settings.evenElim = false;
              settings.xorLearn = 0;
              settings.deepCuts = 0;
          }

          std::string toString() const {
              std::string s;
              s += "Conflict:    " + bx::toString(conflict) + "\n";
              //s += "Assumptions: " + bx::toString(assumptions) + "\n";
              s += "Implied:     " + bx::toString(implied) + "\n";

              s += "Trail: " + bx::toString(trail) + "\n";
              s += "TrailHead : " + bx::toString(trailHead) + "\n";
              s += "Value:";
              for (size_t i = 0; i < value.size(); i++)
                  s += " " + bx::toString((int) value[i]);
              s += "\n";
            return s;                  
          }


            int new_var() {
                int id = value.size();
                value.push_back(Undef);
                numExplained.push_back(0);
                cached.push_back(std::vector<Lit>());
//                trailPos.push_back(0);
                level.push_back(0);
                toExplain.push_back(0);
                expParity.push_back(0);
                reason.push_back(NULL);
                watches.push_back( std::vector<Clause*>() );
#ifdef DEBUG
                while (1) {
                    if (simplex.new_var() == id)
                        break;
                }
#endif
                return id;
            }

        private:

            friend class LitSorter;
          struct LitSorter {
              XorModule& m;
              LitSorter(XorModule&m_ ) : m(m_) {}
              bool operator()(Lit a, Lit b) const {
                  if (m.litValue(a) == Undef && m.litValue(b) != Undef)
                      return true;
                  if (m.litValue(b) == Undef && m.litValue(a) != Undef)
                      return false;
                  return m.level[a.get_var()] > m.level[b.get_var()];
              }
          };
          void propagateClause(Clause* c) {
              // find unassigned variables to watch
              int undefs = 0;
              int parity = 0;
              for (size_t i = 0; i < c->lits.size(); i++) {
                  char val = litValue(c->lits[i]);
                  if (val == Undef) {
                      Lit tmp = c->lits[undefs];
                      c->lits[undefs] = c->lits[i];
                      c->lits[i] = tmp;

                      undefs++;
                      D(1, "Found watch " << undefs << ": " 
                              << bx::toString(c->lits[undefs]));
                      if (undefs == 2)
                          break;
                  }
                  if (val == True)
                      parity++;
              }

              D(1, "Found " << undefs << " undefs. parity " << parity);

              if (undefs == 1) {
                  char impValue = (parity & 1) ? False : True;

                  bool neg = c->lits[0].get_sign();
                  if (impValue == False)
                      neg = !neg;

                  Lit p = Lit(c->lits[0].get_var(), neg);
                  uncheckedEnqueue(p,c);
                  level[p.get_var()] = level[c->lits[1].get_var()];
                  implied.push_back(p);

                  D(1, "UP: post-propagaetd implied literal " << bx::toString(trail.back()) << " level=" << level[p.get_var()]);
                  stats.implied++;

              } else if (undefs == 0 && parity == 0) {

                  D(1, "unsatisfiable clause");
                  conflict.clear();
                  for (size_t i = 0; i < c->lits.size(); i++) {
                      conflict.push_back(Lit(c->lits[i].get_var(),
                                  value[c->lits[i].get_var()] == True));
                  }
                  D(1, "conflict : " << bx::toString(conflict));
#ifdef DEBUG
                  verify(conflict);
#endif

                  stats.conflicts++;
              }  


          }
        public:
            void add_equation(const std::vector<Lit>& lhs, bool learnt=false) {

                assert(lhs.size() >= 2);
#ifdef DEBUG
                {
                    std::vector<unsigned int> lhs2;
                    bool rhs = true;
                    for (size_t i = 0; i < lhs.size(); i++) {
                        lhs2.push_back(lhs[i].get_var());
                        if (lhs[i].get_sign())
                            rhs = !rhs;
                    }
                    simplex.add_equation(lhs2, rhs);
                }
#endif
#ifdef DEBUG
                {
                D(1, "UP: add_equation(" << bx::toString(lhs) << ", learnt=" << learnt << ")");
                int parity = 0;
                bool undef = false;
                for (size_t i = 0; i < lhs.size(); i++)   {
                    assert(lhs[i].get_var() >= 0 && lhs[i].get_var() < value.size());
                    D(1, bx::toString(lhs[i]) << " value : " << (int) litValue(lhs[i]));
                    switch (litValue(lhs[i])) {
                        case Undef:   
                            undef = true;
                           break;

                        case True:
                           parity++;
                           break;
                    }
                }
                }
#endif

                Clause* c = newClause(lhs, learnt);
#ifdef DEBUG
                    clauseOcc[c->name()]++;
                    if (clauseOcc[c->name()] > 1) {
                        std::cerr << "one too many: " << c->name() << std::endl;
                        exit(1);
                    }
                    std::cout << clauseOcc[c->name()] <<  std::endl;
#endif

                if (!learnt)
                    clauses.push_back(c);
                else {

                    learnts.push_back(c);
                    claBumpActivity(*c);
                    stats.learnts++;
                    stats.learntLits += c->lits.size();

                }
                // sort literals according to assigned/unassigned and level
                std::sort(c->lits.begin(), c->lits.end(), LitSorter(*this));
                D(1, "Sorted : " << bx::toString(c->lits));

                // find unassigned variables to watch
                int undefs = 0;
                int parity = 0;
                for (size_t i = 0; i < c->lits.size(); i++) {
                    char val = litValue(c->lits[i]);
                    if (val == Undef) {
                        Lit tmp = c->lits[undefs];
                        c->lits[undefs] = c->lits[i];
                        c->lits[i] = tmp;

                        undefs++;
                        D(1, "Found watch " << undefs << ": " 
                                << bx::toString(c->lits[undefs]));
                        if (undefs == 2)
                            break;
                    }
                    if (val == True)
                        parity++;
                }



                
                watches[c->lits[0].get_var()].push_back(c);
                watches[c->lits[1].get_var()].push_back(c);


                D(1, "Found " << undefs << " undefs. parity " << parity);

                if (undefs == 1) {
                    char impValue = (parity & 1) ? False : True;

                    bool neg = c->lits[0].get_sign();
                    if (impValue == False)
                        neg = !neg;

                    Lit p = Lit(c->lits[0].get_var(), neg);
                    uncheckedEnqueue(p,c);

                    D(1, "second watch level : " << level[c->lits[1].get_var()]);
                    
                    level[p.get_var()] = level[c->lits[1].get_var()];
                    implied.push_back(p);
                    for (int lvl = level[c->lits[1].get_var()]; 
                            lvl < backjumps.size(); lvl++) {
                        backjumps[lvl].postPropagate.push_back(c);
                        D(1, "Adding post-propagation to backjump " << lvl
                                << " for clause " << bx::toString(c->lits));
                    }
                    


                    D(1, "UP: got implied literal " << bx::toString(trail.back()));
                    stats.implied++;

                } else if (undefs == 0 && parity == 0) {

                    D(1, "unsatisfiable clause");
                    conflict.clear();
                    for (size_t i = 0; i < c->lits.size(); i++) {
                        conflict.push_back(Lit(c->lits[i].get_var(),
                                    value[c->lits[i].get_var()] == True));
                    }
                    D(1, "conflict : " << bx::toString(conflict));
#ifdef DEBUG
                    verify(conflict);
#endif

                    stats.conflicts++;
                }  
                if (learnts.size() > nof_learnts)
                    reduceDB();



            }


            bool is_sat() const {
                return conflict.empty() == true;
            }
            inline char litValue(const Lit& l) const {
                static char values[3] = {True,Undef,False};
                char v = value[l.get_var()];
                if (l.get_sign())
                    return values[v+1];
//                    return -v;
                return v;
            }

        public:

            bool propagate() {
                D(1, "trailHead " << trailHead << "/" << trail.size());
                while (trailHead < trail.size()) {
                    int v = trail[trailHead++];
                    std::vector<Clause*>& ws = watches[v];


                    D(1, "\nChecking watches of " << v);
                    int last = ws.size() - 1;
                    for (int i = 0; i <= last;) {
                        Clause& c = *ws[i];
                        D(1, "Clause " << bx::toString(c.lits));

                        int pos = 0;
                        if (c.lits[1].get_var() == v)
                            pos = 1;


                        // look for a new watch
                        int parity = 0;
                        char impValue, firstValue;
                        for (int j = 2; j < c.lits.size(); j++) {
                            int v = c.lits[j].get_var();
                            if (value[v] == Undef) {
                                // found watch

                                Lit l = c.lits[pos];
                                c.lits[pos] = c.lits[j];
                                c.lits[j] = l;
                                ws[i] = ws[last--];
                                watches[v].push_back(&c);
                                D(1, "Found new watch " << v);
                                goto FoundWatch;
                            } else if (litValue(c.lits[j]) == True) {
                                parity++;
                            }
                        }
                        if (litValue(c.lits[pos]) == True) {

                            parity++;
                        }


                        impValue = (parity & 1) ? False : True;

                        // no watch - clause unit under assignment

                        firstValue = litValue(c.lits[1-pos]);
                        if (firstValue == Undef) {
                            if (pos == 0) {
                                Lit tmp = c.lits[1];
                                c.lits[1] = c.lits[0];
                                c.lits[0] = tmp;
                            }

                            bool neg = c.lits[0].get_sign();
                            if (impValue == False)
                                neg = !neg;
                            Lit p(c.lits[0].get_var(), neg);
                            uncheckedEnqueue(p,&c);
                            implied.push_back(p);
                            D(1, "UP: got implied literal " << bx::toString(trail.back()));
                            stats.implied++;


                        } else if (firstValue != impValue) {
                            D(1, "firstValue " << firstValue << " impValue " << impValue << " parity " << parity);
                            D(1, c.lits[1-pos].get_var() << " already assigned with " << 
                                    ((value[c.lits[1-pos].get_var()] == True) ? " true " : " false "));


                            // conflict
                            for (int i = 0; i < c.lits.size(); i++) {
                                D(1, "value[" << c.lits[i].get_var() << "] : " << (int)value[c.lits[i].get_var()]);
                                conflict.push_back(Lit(c.lits[i].get_var(),
                                                       value[c.lits[i].get_var()] == True));
                            }
                            D(1, "conflict : " << bx::toString(conflict));
#ifdef DEBUG
                            verify(conflict);
#endif
                            stats.conflicts++;


                            trailHead = trail.size();
                            break;
                        }
                        i++; 
                        FoundWatch:
                        ;
                    }
                    ws.resize(last+1);
                    check();
                }

                checkConsistency();

                return !conflict.empty();
            }

            void assume(int var, bool val) {
                if (!conflict.empty())
                    return;
                D(1, "assume(" << var << "," << val << ")");

                if (value[var] == Undef) {
                    stats.assumptions++;
//                    assumptions.push_back(Lit(var, val==false));
                    uncheckedEnqueue(Lit(var, val==false), NULL);
                } else {
                    char newValue = val ? True : False;
                    if (value[var] != newValue) { 
                        D(1, var << " already has value " << (int) value[var]);

                        stats.conflicts++;
                        explain(Lit(var, val), conflict);
                    }
                }
            }

            const std::vector<Lit>* get_conflict() const {
                return &conflict; 
            }

            const std::vector<Lit>* get_implied_lits() const {
                return &implied; 
            }
            size_t get_first_implied() const {
                return firstImplied;
            }
            void reset_first_implied() {
                firstImplied = implied.size();
            }

            void explain(Lit lit, std::vector<Lit>& explanation)  {
                if (numExplained[lit.get_var()] != 0 ) {
                    if (settings.deepCuts ) {

                        numExplained[lit.get_var()]++;
                        deepExplain(lit, explanation);
                        return;
                    }
                }

                numExplained[lit.get_var()]++;
                stats.explained++;
                explanation.clear();
                explanation.push_back(lit);
                int v = lit.get_var();
                D(1, "UP: explain " << v);
                assert(reason[v] != NULL);
                assert(value[v] != Undef);
                Clause& c = *reason[v];
                D(1, "going to use " << bx::toString(c.lits));
                assert(c.lits[0].get_var() == v);
                for (int i = 1; i < c.lits.size(); i++) {
                    int rv = c.lits[i].get_var();
#ifdef DEBUG
                    if (value[rv] == Undef) {
                        std::cerr << "Value of " << rv << " is undefined!" << std::endl;
                        exit(1);
                    }
#endif
                    assert(value[rv] != Undef);
                    explanation.push_back(Lit(rv, value[rv] == True));
                }
                D(1, "UP: explain : " << bx::toString(explanation));
                claBumpActivity(c);
 #ifdef DEBUG
                verify(explanation);

#endif               
                stats.explanationLits += explanation.size();
            }

            void deepExplain(Lit lit, std::vector<Lit>& explanation) {

                if (!cached[lit.get_var()].empty()) {
                    explanation.clear();
                    int v = lit.get_var();
                    D(1, "UP using cached deep explanation : " <<
                            bx::toString(cached[v]));

                    std::copy(cached[v].begin(), cached[v].end(),
                            std::back_inserter(explanation));
                    stats.cachedExplained++;
                                        
                    return;
                }

                stats.deepCuts++;
                stats.explained++;
                D(1, "UP:deepExplain(" << bx::toString(lit) << ")");
                int numToExplain = 1;

                toExplain[lit.get_var()] = 1;
                toExplainClear.push_back(lit.get_var());
//                toExplainQueue.push(ToExplain(lit.get_var(), trailPos[lit.get_var()]));
                explanation.clear();
                explanation.push_back(lit);
                long long prevEvenElim = stats.evenElimLits;
                int pos = trail.size() - 1;
                while (numToExplain > 0) {
//                while (!toExplainQueue.empty()) {
                    while (toExplain[trail[pos--]]==0) ;
                    numToExplain--;

                    //Lit l = trail[pos+1];
                    int var = trail[pos+1];
//                    int var = toExplainQueue.top().var;
//                    toExplainQueue.pop();
                    if (toExplain[var] % 2 == 0) {
                        toExplain[var] = 0;

                        continue;
                    }

                    toExplain[var] = 0;
//                    Lit l = 


                    D(1, "explaining " <<var);
                    assert(reason[var] != NULL);
                    Clause& c = *reason[var];
                   
                    claBumpActivity(c);
                    D(1, "going to use " << bx::toString(c.lits));
                    assert(c.lits[0].get_var() == var);
                    for (int i = 1; i < c.lits.size(); i++) {
                        int rv = c.lits[i].get_var();
                        assert(value[rv] != Undef);
                        if (reason[rv] == NULL) {

                            if (expParity[rv] == 0)
                                explanation.push_back(Lit(rv, value[rv] == True));
                            expParity[rv]++;
                            D(1, "expParity[" << rv << "] = " << (int)expParity[rv]);
                        } else { 

                            if (toExplain[rv] == 0) {
                                D(1, "going to explain " << rv);
                                numToExplain++;
                                toExplain[rv] = 1;
//                                toExplainClear.push_back(rv);
//                                toExplainQueue.push((ToExplain(rv, trailPos[rv])));
                            } else if (settings.evenElim) {
                                
                                D(1, ((toExplain[rv] & 1) ? "not " :"") <<"explaining " << rv << " (even-elim)");
                                toExplain[rv]++;
                                //numToExplain--;

                            }
                        }
                    }

                }
                D(1, "parityExplain result " << bx::toString(explanation));


                for (size_t i = 0; i <toExplainClear.size(); i++) {
                    toExplain[toExplainClear[i]] = 0;
                }
                toExplainClear.clear();
                
                int last = explanation.size() - 1;
                for (int i = 1; i <= last; ) {
                    int v = explanation[i].get_var();
                    if (expParity[v] % 2 == 0 && settings.evenElim) {
                        D(1, "even-eliminating " << v);
                        explanation[i] = explanation[last--];
                        stats.evenElimLits++;
                    }  else
                        i++;
                    expParity[v] = 0;
                }
                explanation.resize(last+1);
                if (stats.evenElimLits > prevEvenElim && settings.xorLearn
                        && explanation.size() <= settings.xorLearn
                        && explanation.size() >= 2) {
                    D(1, "auto-learning " << bx::toString(explanation));
                    int maxLevel = 0;

                    for (size_t i = 0; i < explanation.size(); i++) {
                        int v = explanation[i].get_var();
                        if (level[v] > maxLevel)
                            maxLevel = level[v];
                    }
                    int onLastLevel = 0;
                    for (size_t i = 0; i < explanation.size(); i++) {
                        if (level[explanation[i].get_var()] == maxLevel) {
                            onLastLevel++;
                        D(1, "on last level : " << 
                                bx::toString(explanation[i]));
                        }
                            
                    }
                    
                    if (onLastLevel == 1) {
                        stats.autoLearned++;
                        pendingXors.push_back(explanation);

                    } else {

                       D(1, "there are " << onLastLevel
                                << " literal on the last level, so "
                                << " the explanation is redundant: " );
                   }
                    
                }
#ifdef DEBUG
                for (size_t i = 0; i< toExplain.size(); i++)
                    assert(toExplain[i] == 0);
                verify(explanation);
#endif
                stats.explanationLits += explanation.size();
                std::copy(explanation.begin(), explanation.end(),
                        std::back_inserter(cached[lit.get_var()]));
            }
            void claDecayActivity() {

                cla_inc *= clause_decay;
            }

            int set_backtrack_point() {
                int id = backjumps.size();
                backjumps.push_back(Backjump());
                Backjump& b = backjumps.back();
                
                b.numImplied        = implied.size();
//                b.numAssumptions    = assumptions.size();
                b.numTrail          = trail.size();
                b.trailHead         = trailHead;


#ifdef DEBUG
                b.state             = toString();
#endif


                return id;  
            }
            void backtrack(int bt) {
                assert(bt >= 0 && bt < backjumps.size());
                Backjump& b = backjumps[bt];

                for (int i = b.numTrail; i < trail.size(); i++) {
                    int v = trail[i];

                    D(1, " clearing value of " << v);
                    value[v] = Undef;
                    numExplained[v] = 0;
                    reason[v] = NULL;
                    cached[v].clear();
                }
                implied.resize(b.numImplied);
                firstImplied = implied.size();
//                assumptions.resize(b.numAssumptions);
                trail.resize(b.numTrail);
                trailHead = b.trailHead;


                for (size_t i = 0; i < b.postPropagate.size(); i++) {

                    D(1, "post propagate " << bx::toString(b.postPropagate[i]->lits));
                    propagateClause(b.postPropagate[i]);
                }

                backjumps.resize(bt);
                conflict.clear();
                checkConsistency();
#ifdef DEBUG
//                if (b.state != toString())
//                    std::cout << "ORIGINAL: " << b.state << std::endl << "CURRENT: " << toString() << std::endl;
//                assert(b.state == toString());
#endif
            }
#ifdef DEBUG
            void verify(std::vector<Lit>& lits) {
                D(bx::dbg::prop, "verifying " << bx::toString(lits));
                unsigned int bt = simplex.set_backtrack_point();
                bool unsat = false;
                for (int i = 0; i < lits.size(); i++) {
                    Lit& l = lits[i];
                    bool value = l.get_sign() == false;
                    if (simplex.assume(l.get_var(), !value) == false) {
                        unsat = true;
                        break;
                    }
                }
                if (simplex.is_sat() == false)
                    unsat = true;
                if (!unsat) {
                    std::cerr << "Clause verification failed: " << 
                        bx::toString(lits) << std::endl;
                    exit(1);
                }
                simplex.backtrack(bt);
            }
#endif

    };
}
#endif
