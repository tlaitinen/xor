#include <cassert>

#include <algorithm>

#include "Simplex.h"

Simplex::Simplex() :
  true_const(UINT_MAX),
  is_permanently_unsat(false)
{
  true_const.has_value = true;
  true_const.value = true;
  verbose_level_ = 0;
  verbstr = stderr;
  record_str = 0;
}

Simplex::~Simplex()
{
  while(!equations.empty()) {
    Eq* eq = equations.back();
    equations.pop_back();
    for(Entry* e = eq->elements; e; ) {
      Entry* const next_e = e->next_in_eq;
      free_entry(e);
      e = next_e;
    }
    delete eq;
  }
  while(!vars.empty()) {
    delete vars.back();
    vars.pop_back();
  }
}

void
Simplex::fatal_error(const char* fmt, ...) const
{
  va_list ap;
  va_start(ap, fmt);
  fprintf(stderr,"Simplex fatal error: ");
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\nAborting!\n");
  va_end(ap);
  exit(1);
}


void
Simplex::set_record_stream(FILE* fp)
{
  record_str = fp;
}


bool
Simplex::is_sat() const
{
  return(!(is_permanently_unsat or conflict.size() > 0));
}


size_t
Simplex::print(FILE* const fp, const char* const ind) const
{
  if(is_permanently_unsat)
    return fprintf(fp, "%sPermanently unsat\n", ind);

  size_t r = 0;
  r += fprintf(fp, "%sEquations:\n", ind);
  for(unsigned int i = 0; i < equations.size(); i++) {
    Eq* eq = equations[i];
    assert(eq);
    r += fprintf(fp, "%s ", ind) + eq->print(fp) + fprintf(fp, "\n");
  }

  r += fprintf(fp, "%sAssumptions:", ind);
  for(unsigned int i = 0; i < assumptions.size(); i++)
    r += fprintf(fp, "  ") + assumptions[i].print(fp);
  r += fprintf(fp, "\n");

  r += fprintf(fp, "%sImplied literals:\n", ind);
  std::vector<Lit> explanation;
  for(unsigned int i = 0; i < implied_literals.size(); i++) {
    Lit lit = implied_literals[i];
    explain(lit, explanation);
    const char* sep = "";
    r += fprintf(fp, "%s  ", ind) + lit.print(fp) + fprintf(fp, " <- ");
    for(unsigned int j = 0; j < explanation.size(); j++) {
      r += fprintf(fp, "%s", sep) + explanation[j].print(fp);
      sep = " & ";
    }
    r += fprintf(fp, "\n");
  }

  r += fprintf(fp, "%sConflict:", ind);
  for(unsigned int i = 0; i < conflict.size(); i++)
    r += fprintf(fp, "  ") + conflict[i].print(fp);
  r += fprintf(fp, "\n");

  if(is_sat()) {
    std::vector<bool> model;
    get_model(model);
    r += fprintf(fp, "%sModel:", ind);
    for(unsigned int i = 0; i < vars.size(); i++)
      r += fprintf(fp, " %sx%u", model[i]?"":"!", i);
    r += fprintf(fp, "\n");
  }

  return r;
}



size_t
Simplex::print_formula(FILE* const fp) const
{
  if(is_permanently_unsat)
    return fprintf(fp, "false");

  size_t r = 0;

  r += fprintf(fp, "true");
  for(unsigned int i = 0; i < equations.size(); i++) {
    Eq* eq = equations[i];
    assert(eq);
    r += fprintf(fp, " & (") + eq->print_formula(fp) + fprintf(fp, ")");
  }

  for(unsigned int i = 0; i < vars.size(); i++)
    if(vars[i]->has_value) {
      const char* p = (vars[i]->value == false)?"!":"";
      r += fprintf(fp, " & (%s", p) +
	vars[i]->print_formula(fp) +
	fprintf(fp, ")");
    }

  return r;
}



unsigned int
Simplex::new_var()
{
  if(record_str) {
    fprintf(record_str, "v\n"); fflush(record_str); }

  Var* v = new Var(vars.size());
  if(!v) fatal_error("Out of memory");
  vars.push_back(v);
  return v->index;
}



void
Simplex::add_equation(const std::vector<unsigned int>& lhs, const bool rhs)
{
  if(record_str) {
    fprintf(record_str, "e");
    for(unsigned int i = 0; i < lhs.size(); i++)
      fprintf(record_str, " %u", lhs[i]);
    if(rhs == false) fprintf(record_str, " -1");
    fprintf(record_str, "\n");
    fflush(record_str);
  }

  if(assumptions.size() > 0)
    fatal_error("cannot add equations under assumtions");
  if(bt_assumptions_lim.size() > 0)
    fatal_error("cannot add equations under backtrack points");

  assert(assumptions.size() == 0);

  if(is_permanently_unsat)
    return;

  if(get_verbose_level() > 1) {
    fprintf(verbstr, "Simplex: adding equation '");
    const char* sep = "";
    for(unsigned int i = 0; i < lhs.size(); i++) {
      fprintf(verbstr, "%sx%u", sep, lhs[i]); sep = " + "; }
    fprintf(verbstr, " = %s'\n", rhs?"T":"F");
    fflush(verbstr);
  }

  /* Make a working copy of the left hand side */
  std::vector<unsigned int> l(lhs);

  /* Sort and simplify */
  std::sort(l.begin(), l.end());
  unsigned int j = 0;
  for(unsigned int i = 0; i < l.size(); ) {
    if(i+1 < l.size() and l[i] == l[i+1])
      i += 2;
    else
      l[j++] = l[i++];
  }
  l.resize(j);
  /* Analyze the result */
  if(l.size() == 0) {
    if(rhs == false) {
      /* 0 = 0 */
      return;
    }
    /* 0 = 1 */
    is_permanently_unsat = true;
    return;
  }
  /* Make a list of entries */
  Eq* eq = new Eq();
  Entry** prev_next_in_eq = &eq->elements;
  for(unsigned int i = 0; i < l.size(); i++) {
    assert(l[i] < vars.size());
    Entry* e = alloc_entry(vars[l[i]], eq);
    /* Attach */
    *prev_next_in_eq = e;
    e->prev_next_in_eq = prev_next_in_eq;
    prev_next_in_eq = &e->next_in_eq;
  }
  if(rhs == false) {
    Entry* e = alloc_entry(&true_const, eq);
    /* Attach */
    *prev_next_in_eq = e;
    e->prev_next_in_eq = prev_next_in_eq;
    prev_next_in_eq = &e->next_in_eq;    
  }


  if(get_verbose_level() > 2) {
    fprintf(verbstr, "Simplex: normal form equation '");
    eq->print(verbstr);
    fprintf(verbstr, "'\n");
    fflush(verbstr);
  }


  /* Eliminate all non-basic variables */
  while(true) {
    Entry* e = eq->elements;
    while(e and e->var->is_basic)
      e = e->next_in_eq;
    if(!e)
      break;
    assert(e->var != &true_const);
    assert(e->var->equations);
    assert(e->var->equations->next_equation == 0);
    assert(e->var->nof_equations == 1);
    e = e->var->equations;
    pivot_simple(e->eq, eq);
  }
  
  if(get_verbose_level() > 2) {
    fprintf(verbstr, "Simplex: equation on basic vars '");
    eq->print(verbstr);
    fprintf(verbstr, "'\n");
    fflush(verbstr);
  }


  if(!eq->elements) {
    /* empty equation */
    delete eq;
    is_permanently_unsat = true;
    return;
  }
  if(eq->elements->var == &true_const) {
    assert(eq->elements->next_in_eq == 0);
    /* Redundant equation, ignore */
    for(Entry* e = eq->elements; e; e = e->next_in_eq)
      free_entry(e);
    delete eq;
    return;
  }

  assert(eq);
  equations.push_back(eq);



  unsigned int min_occ = UINT_MAX;
  Entry* min_entry = 0;
  for(Entry* e = eq->elements; e and e->var != &true_const; e = e->next_in_eq) {
    if(e->var->nof_equations < min_occ) {
      min_entry = e;
      min_occ = e->var->nof_equations;
    }
    if(min_occ == 0) break;
  }
  assert(min_entry);

  Var* const pivot_var = min_entry->var;
  assert(pivot_var != &true_const);
  assert(!pivot_var->has_value);
  while(pivot_var->equations)
    pivot(eq, pivot_var->equations->eq);

  for(Entry* e = eq->elements; e; e = e->next_in_eq)
    e->var_attach();

  assert(min_entry->var->nof_equations == 1);
  assert(min_entry->var->equations == min_entry);
  assert(min_entry->var->equations->next_equation == 0);
  min_entry->var->is_basic = false;

  check_consistency();

  return;
}



void
Simplex::pivot_simple(const Eq* const eq1, Eq* const eq2)
{
  Entry*  e1 = eq1->elements;
  Entry*  e2 = eq2->elements;
  Entry*  last_e2 = 0;
  Entry** last_e2p = &eq2->elements;

  check_consistency();

  while(e1 and e2) {
    if(e1->var->index < e2->var->index) {
      Entry* e = alloc_entry(e1->var, eq2);
      e->next_in_eq = e2;
      e->prev_next_in_eq = e2->prev_next_in_eq;
      *(e2->prev_next_in_eq) = e;
      e2->prev_next_in_eq = &e->next_in_eq;
      
      last_e2 = e;
      last_e2p = &e->next_in_eq;
      
      e1 = e1->next_in_eq;
    }
    else if(e2->var->index < e1->var->index) {
      last_e2 = e2;
      last_e2p = &e2->next_in_eq;
      e2 = e2->next_in_eq;
    }
    else {
      if(e2->next_in_eq)
	e2->next_in_eq->prev_next_in_eq = e2->prev_next_in_eq;
      *(e2->prev_next_in_eq) = e2->next_in_eq;
      Entry* const e2_next = e2->next_in_eq;
      e2->next_in_eq = 0;
      e2->prev_next_in_eq = 0;
	
      free_entry(e2);

      e1 = e1->next_in_eq;
      e2 = e2_next;
    }
  }
  while(e1) {
    Entry* e = alloc_entry(e1->var, eq2);
    e->prev_next_in_eq = last_e2p;
    *last_e2p = e;
    last_e2 = e;
    last_e2p = &e->next_in_eq;
    
    e1 = e1->next_in_eq;
  }
  while(e2) {
    last_e2 = e2;
    last_e2p = &e2->next_in_eq;
    e2 = e2->next_in_eq;
  }

  check_consistency();

  if(last_e2 and last_e2->var == &true_const) {
    *(last_e2->prev_next_in_eq) = 0;
    free_entry(last_e2);
  } else {
    assert(last_e2 == 0 or last_e2p == &last_e2->next_in_eq);
    Entry* e = alloc_entry(&true_const, eq2);
    *last_e2p = e;
    e->prev_next_in_eq = last_e2p;
    last_e2p = &e->next_in_eq;
  }
  
  check_consistency();
}





void
Simplex::pivot(const Eq* const eq1, Eq* const eq2)
{
  Entry*  e1 = eq1->elements;
  Entry*  e2 = eq2->elements;
  Entry*  last_e2 = 0;
  Entry** last_e2p = &eq2->elements;

  check_consistency();
  if(get_verbose_level() > 2) {
    fprintf(verbstr, "Simplex: applying '");
    eq1->print(verbstr);
    fprintf(verbstr, "' to '");
    eq2->print(verbstr);
    fprintf(verbstr, "'\n");
  }

  while(e1 and e2)
    {
      if(e1->var->index < e2->var->index) {
	Entry* e = alloc_entry(e1->var, eq2);
	e->next_in_eq = e2;
	e->prev_next_in_eq = e2->prev_next_in_eq;
	*(e2->prev_next_in_eq) = e;
	e2->prev_next_in_eq = &e->next_in_eq;
	
	last_e2 = e;
	last_e2p = &e->next_in_eq;
	
	e->var_attach();
	
	e1 = e1->next_in_eq;
      }
      else if(e2->var->index < e1->var->index) {
	last_e2 = e2;
	last_e2p = &e2->next_in_eq;
	e2 = e2->next_in_eq;
      }
      else {
	if(e2->next_in_eq)
	  e2->next_in_eq->prev_next_in_eq = e2->prev_next_in_eq;
	*(e2->prev_next_in_eq) = e2->next_in_eq;
	Entry* const e2_next = e2->next_in_eq;
	e2->next_in_eq = 0;
	e2->prev_next_in_eq = 0;
	
	e2->var_detach();
	free_entry(e2);
	
	e1 = e1->next_in_eq;
	e2 = e2_next;
      }
    }
  while(e1)
    {
      Entry* e = alloc_entry(e1->var, eq2);
      e->prev_next_in_eq = last_e2p;
      *last_e2p = e;
      last_e2 = e;
      last_e2p = &e->next_in_eq;
      
      e->var_attach();

      e1 = e1->next_in_eq;
    }
  while(e2)
    {
      last_e2 = e2;
      last_e2p = &e2->next_in_eq;
      e2 = e2->next_in_eq;
    }

  check_consistency();

  if(last_e2 and last_e2->var == &true_const)
    {
      last_e2->var_detach();
    
      *(last_e2->prev_next_in_eq) = 0;
      free_entry(last_e2);
    }
  else
    {
      assert(!last_e2 or last_e2p == &last_e2->next_in_eq);
      Entry* e = alloc_entry(&true_const, eq2);
      *last_e2p = e;
      e->prev_next_in_eq = last_e2p;
      last_e2p = &e->next_in_eq;
      
      e->var_attach();
    }

  if(get_verbose_level() > 2) {
    fprintf(verbstr, "Simplex: result '");
    eq2->print(verbstr);
    fprintf(verbstr, "'\n");
  }

  check_consistency();

}



void
Simplex::swap(Var* const nonbasic, Var* const basic)
{
  assert(nonbasic);
  assert(nonbasic->is_basic == false);
  assert(nonbasic->has_value == false);
  assert(nonbasic->equations);
  assert(nonbasic->equations->next_equation == 0);
  Eq* const nonbasic_eq = nonbasic->equations->eq;
  assert(basic);
  assert(basic->is_basic == true);
  assert(basic->has_value == false);
  assert(basic->equations);

  Entry* e = basic->equations;
  while(e) {
    Entry* next_e = e->next_equation;
    if(e->eq != nonbasic_eq)
      pivot(nonbasic_eq, e->eq);
    e = next_e;
  }
  
  nonbasic->is_basic = true;
  basic->is_basic = false;

  assert(basic);
  assert(basic->equations);
  assert(basic->equations->next_equation == 0);
  assert(nonbasic->equations);
}



void
Simplex::initial_propagation()
{
  assert(assumptions.size() == 0);
  assert(bt_assumptions_lim.size() == 0);

  /* Detect unit clauses */
  unsigned int nof_unit_clauses = 0;
  for(unsigned int i = 0; i < vars.size(); i++) {
    Var* v = vars[i];
    if(v->nof_equations == 0)
      {
	assert(!v->has_value);
	continue;
      }
    if(v->nof_equations > 1)
      {
	assert(!v->has_value);
	assert(v->is_basic);
	continue;
      }
    assert(v->nof_equations == 1);
    Eq* eq = v->equations->eq;
    assert(eq->elements);

    if(v->is_basic)
      {
	assert(!v->has_value);
	assert(eq->elements->next_in_eq and
	       (eq->elements->next_in_eq->var != &true_const or
		eq->elements->next_in_eq->next_in_eq));
	continue;
      }

    assert(!v->is_basic);
    assert(eq->elements->var != &true_const);
    if(eq->elements->next_in_eq and
       (eq->elements->next_in_eq->var != &true_const or
	eq->elements->next_in_eq->next_in_eq))
      continue;
    assert(eq->elements->var == v and
	   (!eq->elements->next_in_eq or
	    (eq->elements->next_in_eq->var == &true_const and
	     (eq->elements->next_in_eq->next_in_eq == 0))));
    bool desired = false;
    if(eq->elements->next_in_eq == 0)
      desired = true;
    if(v->has_value)
      assert(v->value == desired);
    else {
      v->has_value = true;
      v->value = desired;
      implied_literals.push_back(Lit(v->index, desired == false));
    }
    nof_unit_clauses++;
  }

  assert(nof_unit_clauses == implied_literals.size());
}



bool
Simplex::assume(const unsigned int vnum, const bool value)
{
  if(record_str) {
    fprintf(record_str, "a %s%u\n", value?"":"!", vnum); fflush(record_str); }
  
  if(get_verbose_level() > 2)
    fprintf(verbstr, "Simplex: assuming %sx%u\n", value?"":"!", vnum);
  
  if(is_permanently_unsat) {
    assert(conflict.size() == 0);
    return false;
  }

  if(assumptions.size() == 0 and bt_assumptions_lim.size() == 0)
    initial_propagation();

  if(conflict.size() > 0) {
    return false;
  }
  assert(conflict.size() == 0);

  assert(vnum < vars.size());
  Var* const var = vars[vnum];

  if(var->has_value) {
    if(var->is_basic)
      fatal_error("cannot assume an already assumed variable");
    assert(var->nof_equations == 1);
    if(var->value == value)
      return true;
    Eq* const eq = var->equations->eq;
    assert(eq);
    for(Entry* e = eq->elements; e; e = e->next_in_eq) {
      assert(e->var->has_value);
      if(e->var == var)
	conflict.push_back(Lit(var->index, value == false));
      else if(e->var != &true_const) {
	assert(e->var->is_basic);
	conflict.push_back(Lit(e->var->index, e->var->value == false));
      }
    }
    return false;
  }

  assert(!var->has_value);

  if(!var->is_basic) {
    Var* v = 0;
    unsigned int min_occ = UINT_MAX;
    Eq* const eq = var->equations->eq;
    for(Entry* e = eq->elements; e; e = e->next_in_eq) {
      if(!e->var->has_value and e->var->is_basic and
	 e->var->nof_equations < min_occ) {
	v = e->var;
	min_occ = e->var->nof_equations;
      }
    }
    assert(v);
    swap(var, v);

    if(get_verbose_level() > 2) {
      fprintf(verbstr, "Simplex: after swap\n");
      print(verbstr, " ");
    }
  }
  assert(var->is_basic);

  var->has_value = true;
  var->value = value;
  assumptions.push_back(Lit(var->index, value == false));

  /* Propagate */
  for(Entry* ec = var->equations; ec; ec = ec->next_equation) {
    Eq* eq = ec->eq;
    Var* nonbasic = 0;
    Var* basic = 0;
    bool desired = true;
    for(Entry* e = eq->elements; e; e = e->next_in_eq) {
      Var* v = e->var;
      if(v->has_value) {
	assert(v->is_basic);
	desired = desired ^ v->value;
      }
      else {
	if(v->is_basic) {
	  basic = v;
	  break;
	}
	assert(nonbasic == 0);
	nonbasic = v;
      }
    }
    if(!basic) {
      assert(nonbasic);
      assert(!nonbasic->has_value);
      nonbasic->has_value = true;
      nonbasic->value = desired;
      implied_literals.push_back(Lit(nonbasic->index, nonbasic->value==false));
    }
  }

  return true;
}


void
Simplex::explain(Lit lit, std::vector<Lit>& explanation) const
{
  explanation.clear();
  const unsigned int vnum = lit.get_var();
  assert(vnum < vars.size());
  Var* const var = vars[vnum];
  if(!var->has_value)
    fatal_error("Cannot explain an unassigned variable");
  if(var->is_basic)
    fatal_error("Cannot explain an assumed variable");

  explanation.push_back(lit);
  assert(var->value == !lit.get_sign());
  assert(var->nof_equations == 1);
  Eq* eq = var->equations->eq;
  for(Entry* e = eq->elements; e; e = e->next_in_eq) {
    assert(e->var->has_value);
    if(e->var == var)
      ;
    else if(e->var != &true_const) {
      assert(e->var->is_basic);
      explanation.push_back(Lit(e->var->index, !(e->var->value == false)));
    }
  }
}



unsigned int
Simplex::set_backtrack_point()
{
  if(record_str) {
    fprintf(record_str, "b\n"); fflush(record_str); }

  if(assumptions.size() == 0 and bt_assumptions_lim.size() == 0)
    initial_propagation();

  const unsigned int p = bt_assumptions_lim.size();
  bt_assumptions_lim.push_back(assumptions.size());
  bt_implieds_lim.push_back(implied_literals.size());
  assert(bt_has_conflict.size() == 0 or
	 bt_has_conflict.back() == false or
	 conflict.size() > 0);
  bt_has_conflict.push_back(conflict.size() > 0);
  return p;
}



void
Simplex::backtrack(unsigned int backtrack_point)
{
  if(record_str) {
    fprintf(record_str, "j %u\n", backtrack_point); }

  assert(backtrack_point < bt_assumptions_lim.size());
  while(backtrack_point < bt_assumptions_lim.size()) {

    while(assumptions.size() > bt_assumptions_lim.back()) {
      Lit l = assumptions.back();
      assumptions.pop_back();
      assert(vars[l.get_var()]->has_value);
      assert(vars[l.get_var()]->value == !l.get_sign());
      vars[l.get_var()]->has_value = false;
    }
    bt_assumptions_lim.pop_back();

    while(implied_literals.size() > bt_implieds_lim.back()) {
      Lit l = implied_literals.back();
      implied_literals.pop_back();
      assert(vars[l.get_var()]->has_value);
      assert(vars[l.get_var()]->value == !l.get_sign());
      vars[l.get_var()]->has_value = false;
    }
    bt_implieds_lim.pop_back();

    bool c = bt_has_conflict.back();
    bt_has_conflict.pop_back();
    if(!c and conflict.size() > 0)
      conflict.clear();
  }
}


void
Simplex::get_model(std::vector<bool>& model) const
{
  if(!is_sat())
    fatal_error("system is unsat, cannot get a model");

  model.clear();
  model.resize(vars.size());
  std::vector<bool> has_value(vars.size());
  for(unsigned int i = 0; i < vars.size(); i++) {
    assert(vars[i]->index == i);
    if(vars[i]->has_value) {
      model[i] = vars[i]->value;
      has_value[i] = true;
    } else if(vars[i]->is_basic) {
      model[i] = false;
      has_value[i] = true;
    }
  }
  for(unsigned int i = 0; i < vars.size(); i++) {
    if(!has_value[i]) {
      Var* const var = vars[i];
      assert(!var->is_basic);
      assert(var->nof_equations == 1);
      Eq* eq = var->equations->eq;
      bool desired = true;
      for(Entry* e = eq->elements; e; e = e->next_in_eq) {
	Var* v = e->var;
	if(v->has_value) {
	  assert(v->is_basic);
	  desired = desired ^ v->value;
	} else if(has_value[v->index]) {
	  assert(v->is_basic);
	  desired = desired ^ model[v->index];
	} else {
	  assert(v == var);
	  assert(!v->is_basic);
	}
      }
      model[i] = desired;
    }
  }
}
