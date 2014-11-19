#ifndef _settings_hpp_
#define _settings_hpp_
   struct Settings {
        bool createVars;
        bool evenParityElimination;
        bool deepCuts;
        int storeXorExp;
        int pathExplanationLength;
        bool optimizeClauses;
        bool fastExp;
        Settings() : createVars(false), evenParityElimination(false), 
        deepCuts(false), 
        storeXorExp(0), pathExplanationLength(2),
        optimizeClauses(true),
        fastExp(false) {}
    };
#endif
