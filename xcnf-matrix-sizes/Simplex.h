#ifndef SIMPLEX_HH
#define SIMPLEX_HH

#include <cstdlib>
#include <cstdio>
#include <cassert>
#include <cstdarg>
#include <climits>
#include <vector>
/**
 * An incremental theory module for linear equations modulo 2.
 * Author: Tommi Junttila.
 * For the moment, all rights reserved by the author.
 * No distribution whatsoever allowed.
 */
class Simplex
{
  public:
    /** A class for communicating conflict literals */
  class Lit {
    unsigned int x;
  public:
    Lit(const Lit& other) {x = other.x; }
    Lit& operator=(const Lit& other) {x = other.x; return *this; }
    Lit(unsigned int v, bool sign) {x = (v + v) + (sign?1:0); }
    /** Return the variable index */
    unsigned int get_var() const {return(x / 2); }
    /** Returns true if the literal is negated */
    bool get_sign() const {return((x % 2) == 1); }
    size_t print(FILE* const fp) const {
      return fprintf(fp, "%sx%u", get_sign()?"!":"", get_var());
    }
  };
  

  Simplex();
  ~Simplex();

  unsigned int get_verbose_level() const {return verbose_level_; }
  void         set_verbose_level(const unsigned int l) {verbose_level_ = l; }
  void         set_verbose_str(FILE* const fp) {verbstr = fp; }

  size_t print(FILE* const fp, const char* const ind = "") const;
  size_t print_formula(FILE* const fp) const;

  /** Add a new variable in the system and return its index */
  unsigned int new_var();

  /** Add equation lhs = rhs to the system.
   * lhs is a list of variables (a variable can occur multiple times). */
  void add_equation(const std::vector<unsigned int>& lhs, const bool rhs);

  /** Is the system still satisfiable? */
  bool is_sat() const;

  /**
   * The number of implied literals may increase (never decrease).
   * Return false if system is in inconsistent state.
   */
  bool assume(const unsigned int var, const bool value);

  /**
   * Get the conflict; "is_sat" must have returned false.
   * The returned vector is only valid until the next call to "backtrack".
   */
  const std::vector<Lit>* get_conflict() const {return &conflict; }

  /**
   * Get the implied literals.
   * The returned vector may be grown by "assume", "add_equation" and
   * shrunk by "backtrack".
   */
  const std::vector<Lit>* get_implied_lits() const {return &implied_literals; }


  size_t getRowNum() const {
      return equations.size();
  }

  /**
   * Get the explanation of the implied literal \a lit.
   */
  void explain(Lit lit, std::vector<Lit>& explanation) const;

  unsigned int set_backtrack_point();
  void backtrack(unsigned int backtrack_point);

  /**
   *  Build a model of the system.
   * "is_sat" must return true when this is called.
   */
  void get_model(std::vector<bool>& model) const;


  /** Record the interface calls to \a fp */
  void set_record_stream(FILE* fp);


  /*
   * Stop reading, the public area ends here...
   */
 private:
  static const bool debug = false;
  void fatal_error(const char* fmt, ...) const;

  FILE* record_str;

  class Var;
  class Eq;


  class Entry {
  public:

    Var*    var;
    Eq*     eq;
    Entry*  next_in_eq;
    Entry** prev_next_in_eq;
    Entry*  next_equation;
    Entry** prev_next_equation;
    void newEntry(Var* const v, Eq* const e) {
      assert(v);
      assert(e);
      var = v;
      eq = e;
      next_in_eq = 0;
      prev_next_in_eq = 0;
      next_equation = 0;
      prev_next_equation = 0;
    }
    void var_attach() {
      assert(var);
      assert(!next_equation);
      assert(!prev_next_equation);
      if(var->equations)
	var->equations->prev_next_equation = &next_equation;
      next_equation = var->equations;
      var->equations = this;
      prev_next_equation = &var->equations;
      var->nof_equations++;
    }
    void var_detach() {
      assert(var);
      assert(var->nof_equations > 0);
      assert(prev_next_equation);
      if(next_equation)
	next_equation->prev_next_equation = prev_next_equation;
      *prev_next_equation = next_equation;
      next_equation = 0;
      prev_next_equation = 0;
      var->nof_equations--;
    }
  };

  struct Chunk {
      Entry entries[4096];
      size_t used;
      Chunk() : used(0) {}
  };
  std::vector<Chunk*> chunks;
  std::vector<Entry*> freeEntries;
  /* To be replaced with own memory management routines */
  Entry* alloc_entry(Var* const v, Eq* const e) {
      if (chunks.empty() || chunks.back()->used == 4096) {
          chunks.push_back(new Chunk());
      } 

      if (freeEntries.empty()) {
           Chunk& c = *chunks.back();
           freeEntries.push_back(&c.entries[c.used++]);
      }
      Entry* entry= freeEntries.back();
      freeEntries.pop_back();
      entry->newEntry(v,e);
      return entry;
     
        //return entryAllocator.alloc(of(Entry),true);
//      return new Entry(v, e); 
  }
  void   free_entry(Entry* e) {assert(e); 
//        entryAllocator.Deallocate(e, sizeof(Entry));
//      delete e; 
        freeEntries.push_back(e);
  }


  class Var {
  public:
    const unsigned int index;
    unsigned int nof_equations;
    Entry* equations;
    bool is_basic;
    bool has_value;
    bool value;
    Var(const unsigned int i) : index(i) {
      nof_equations = 0;
      equations = 0;
      is_basic = true;
      has_value = false;
      value = false;
    }
    size_t print(FILE* const fp) const {
      if(index == UINT_MAX) return fprintf(fp, "T");
      return fprintf(fp, "%sx%u=%s", is_basic?"*":"", index,
		     has_value?(value?"T":"F"):"?");
    }
    size_t print_formula(FILE* const fp) const {
      if(index == UINT_MAX) return fprintf(fp, "true");
      return fprintf(fp, "x%u", index);
    }
  };

  /**
   * Sentinel class for equations
   */
  class Eq {
  public:
    Entry* elements;

    Eq() {elements = 0; }

    size_t print(FILE* const fp) const {
      size_t r = 0;
      const char* sep = "";
      for(Entry* e = elements; e; e = e->next_in_eq) {
	r += fprintf(fp, "%s", sep) + e->var->print(fp);
	sep = " + ";
      }
      return r;
    }
    size_t print_formula(FILE* const fp) const {
      size_t r = fprintf(fp, "false");
      for(Entry* e = elements; e; e = e->next_in_eq)
	r += fprintf(fp, " ^ ") + e->var->print_formula(fp);
      return r;
    }
  };


  std::vector<Var*> vars;
  Var true_const;

  std::vector<Eq*> equations;

  std::vector<Lit> conflict;

  void initial_propagation();

  std::vector<Lit> assumptions;
  std::vector<Lit> implied_literals;

  std::vector<unsigned int> bt_assumptions_lim;
  std::vector<unsigned int> bt_implieds_lim;
  std::vector<bool>         bt_has_conflict;

  bool is_permanently_unsat;

  unsigned int verbose_level_;
  FILE* verbstr;

  void swap(Var* const nonbasic, Var* const basic);

  void pivot_simple(const Eq* const eq1, Eq* const eq2);
  void pivot(const Eq* const eq1, Eq* const eq2);

  void check_consistency() {
    if(debug) {
      for(unsigned int i = 0; i < equations.size(); i++)
	for(Entry* e = equations[i]->elements; e; e = e->next_in_eq)
	  assert(!e->next_in_eq or
		 e->next_in_eq->prev_next_in_eq == &e->next_in_eq);
      for(unsigned int i = 0; i < vars.size(); i++) {
	unsigned int n = 0;
	for(Entry* e = vars[i]->equations; e; e = e->next_equation) {
	  n++;
	  assert(*(e->prev_next_equation) == e);
	  assert(!e->next_equation or
		 e->next_equation->prev_next_equation == &e->next_equation);
	}
	assert(n == vars[i]->nof_equations);
      }
    }
  }




 public:
};


#endif
