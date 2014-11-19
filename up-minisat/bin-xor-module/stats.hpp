#ifndef __stats_hpp_
#define __stats_hpp_
namespace bx {
    struct Stats {
        // ternary => unary xor-implied
        long long ternaryXorImplied;

        // binary => unary xor-implied
        long long binaryXorImplied;

        // literals in xor-explanations
        long long xorExplanationLits;


        // number of xor-explanations
        long long xorExplanations;

        // literals in xor-conflicts
        long long binXorConflictLits;

        // number of bin-xor (chain) xor-conflicts
        long long binXorConflicts;

        // number of ternary xor-conflicts
        long long terXorConflicts;

        // number of eliminated literals in explanations due to 
        // even parity
        long long evenParityEliminated;

        long long dl0Eliminated;

        // unary xor explanations
        long long unaryExplanations;
        long long binaryExplanations;
        long long ternaryExplanations;
        long long quadExplanations;

        long long optExistingUsed, optNewVars;
        long long optUnit, optBinary, learntClauses;

        Stats() : ternaryXorImplied(0),
        binaryXorImplied(0),
        xorExplanationLits(0),
        xorExplanations(0),
        binXorConflictLits(0),
        binXorConflicts(0),
        terXorConflicts(0),
        evenParityEliminated(0),
        dl0Eliminated(0),
        unaryExplanations(0),
        binaryExplanations(0),
        ternaryExplanations(0),
        quadExplanations(0),
        optExistingUsed(0), 
        optNewVars(0),
        optUnit(0),
        optBinary(0),
        learntClauses(0)
                  {}
    };

}
    
#endif
