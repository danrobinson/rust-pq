import Ideal.RustFinalClosed

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal Ideal Ideal.Realize

-- The scheme in the game is perfectly complete at EVERY table g (so verification is not trivially
-- false and the game is not vacuous).
example (g : CF St Blk) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    (Reduction.bytesAlg Link.vp (primsG (liftC g)) (codecG g) (optRandU oR g)
      ($ᵗ (Bytes 16))).PerfectlyComplete ProbCompRuntime.probComp :=
  Reduction.bytesAlg_perfectlyComplete _ _

-- sufInst is literally simulateQ (instImpl g) of the forger, against bytesAlg at primsG (liftC g)
example (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (g : CF St Blk) (pk) :
    (S.sufInst (optRandU oR) ($ᵗ (Bytes 16)) g).main pk = simulateQ (instImpl g) (S.main pk) := rfl

-- the table sampler is uniform: the instance used carries the uniformity proof
#check @SampleableType.evalDist_selectElem_eq_uniform (CF St Blk) instSampleableTypeCFStBlk
#print Ideal.cfAdvantage

-- secret seeds are uniform Bytes 16
example (g : CF St Blk) : (primsG (liftC g)).SkSeed = Bytes 16 := rfl
example (g : CF St Blk) : (primsG (liftC g)).SkPrf = Bytes 16 := rfl
#print Ideal.instSampleableTypeCFStBlk
#check @Ideal.liftC_realCF
#print axioms Ideal.liftC_realCF
