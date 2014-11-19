all: xcnf-preprocess

xcnf-preprocess: main.hs XorCnf.hs ParseXorCnf.hs Preprocess.hs XorCnfUnit.hs ShowXorCnf.hs XorCnfEqv.hs XorCnfProp.hs XorGauss.hs XorTernary.hs Verify.hs XorInternal.hs ClauseSet.hs
	ghc -O2 --make main.hs -o xcnf-preprocess -funbox-strict-fields


xcnf-preprocess-prof: main.hs XorCnf.hs ParseXorCnf.hs Preprocess.hs XorCnfUnit.hs ShowXorCnf.hs XorCnfEqv.hs XorCnfProp.hs XorGauss.hs XorTernary.hs Verify.hs XorInternal.hs ClauseSet.hs
	ghc -O2 --make main.hs -o xcnf-preprocess-prof -prof -auto-all -caf-all -fforce-recomp -funbox-strict-fields 

clean:
	rm xcnf-preprocess xcnf-preprocess-prof *.o *.hi
