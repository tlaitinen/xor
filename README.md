xor
===

Software related to PhD Thesis [Extending SAT Solver with Parity
Reasoning](https://aaltodoc.aalto.fi/handle/123456789/14418)

 * cnf2cnf             : fixes DIMACS cnf header clause and variable counts
 * cnf2xcnf            : extracts xor-constraints from CNF 
 * ec-minisat          : minisat 2.0 with EC xor-deduction system
 * subst-minisat       : minisat 2.0 with SUBST xor-deduction system
 * translations        : translations to simulate EC and IGJ xor-deduction systems by adding redundant xor-constraints and auxiliary variables
 * up-dsimplex-minisat : minisat 2.0 with incremental Gauss-Jordan elimination (IGJ xor-deduction system)
 * up-minisat          : minisat 2.0 with UP xor-deduction system
 * xcnf-biconnected    : finds biconnected xor-constraint components
 * xcnf-clusters       : finds connected xor-constraint components (also tool for extracting junction tree)
 * xcnf-elim-internal  : eliminates variables in XCNF that occur only in xor-part
 * xcnf-matrix-sizes   : computes matrix sizes of a given XCNF
 * xcnf-preprocess     : propagates unary and binary xor-constraints
 * xcnf-simplify       : performs propagation-preserving xor-simplification
 * xcnf2cnf            : complete or partial XCNF to CNF translation
 * xcnf3xcnf           : translates XCNF to 3-xor-normal form

The software is released under General Public License (version 3). See [LICENSE](LICENSE) for details.
 
