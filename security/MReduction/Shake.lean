import MLink.ShakePrimitives

namespace ShakeSecurity
set_option maxHeartbeats 1600000

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal MLink Reduction TweakableHash

instance (p : Params) : SampleableType (primitives p).PkSeed :=
  inferInstanceAs (SampleableType (Bytes p.n))
instance (p : Params) : SampleableType (primitives p).SkSeed :=
  inferInstanceAs (SampleableType (Bytes p.n))
instance (p : Params) : SampleableType (primitives p).SkPrf :=
  inferInstanceAs (SampleableType (Bytes p.n))
instance (p : Params) : SampleableType (primitives p).Y :=
  inferInstanceAs (SampleableType (Bytes p.n))
instance (p : Params) : DecidableEq (primitives p).PkSeed :=
  inferInstanceAs (DecidableEq (Bytes p.n))
instance (p : Params) : DecidableEq (primitives p).SkPrf :=
  inferInstanceAs (DecidableEq (Bytes p.n))
instance (p : Params) : DecidableEq (primitives p).Y :=
  inferInstanceAs (DecidableEq (Bytes p.n))
instance (p : Params) : DecidableEq (primitives p).AdrsKey :=
  inferInstanceAs (DecidableEq (Bytes 32))

instance (S : Sha2Set) : Inhabited (prims S).Y := ⟨Vector.replicate S.vp.params.n 0⟩
instance (S : Sha2Set) : Fintype (prims S).Y := inferInstanceAs (Fintype (Vector UInt8 S.vp.params.n))

theorem slhdsa_shake_bytes_suf_cma_final (S : Sha2Set)
    (optRand : PublicKeyCore (prims S).core → ProbComp (prims S).Y)
    (pkSeedDist : ProbComp (prims S).PkSeed)
    (F : BytesStrongForger S.vp (prims S) (wireCodec S.vp.params) optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤
      betaSufFinalMemo (bytesToTypedS F).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma_final (structural S) F

theorem slhdsa_shake_bytes_euf_cma_final (S : Sha2Set)
    (optRand : PublicKeyCore (prims S).core → ProbComp (prims S).Y)
    (pkSeedDist : ProbComp (prims S).PkSeed)
    (A : BytesForger S.vp (prims S) (wireCodec S.vp.params) optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (bytesToTyped A) :=
  slhdsa_bytes_euf_cma_final (structural S) A

theorem slhdsa_shake_pure_bytes_suf_cma_final (S : Sha2Set)
    (optRand : PublicKeyCore (prims S).core → ProbComp (prims S).Y)
    (pkSeedDist : ProbComp (prims S).PkSeed)
    (F : PureBytesStrongForger S.vp (prims S) (wireCodec S.vp.params) optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤
      betaSufFinalMemo (toInternal (pureBytesToTyped F.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma_final (structural S) F

theorem slhdsa_shake_pure_bytes_euf_cma_final (S : Sha2Set)
    (optRand : PublicKeyCore (prims S).core → ProbComp (prims S).Y)
    (pkSeedDist : ProbComp (prims S).PkSeed)
    (A : PureBytesForger S.vp (prims S) (wireCodec S.vp.params) optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  slhdsa_pure_bytes_euf_cma_final (structural S) A

end ShakeSecurity
