import Ideal.Realize.Port
import Ideal.Realize.Phase1
import Ideal.Transport.AdvTcr
import Ideal.ComposeFinal

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Tcr
open Reduction Ideal.Transport

theorem primsG_eq (g : CF St Blk) :
    primsG (liftC g) = setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) := rfl

def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

def optRand₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp core₀.Y := oR pk.pkSeed pk.pkRoot

/-- The typed forger over `R₀ (thG g) (hmG g)`. -/
noncomputable def B₀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Forger Link.vp (R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist :=
  (bytesToTypedS (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) (codec := codec₀) (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
    ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary

theorem step1 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) (n : ℕ) :
    bTcrArM n (S.typedS (optRandU oR) pkSeedDist g) = bTcrArM n (B₀ S oR pkSeedDist g) :=
  bTcrArM_bytesToTypedS_setPrf (prims := R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist n (fun pk => simulateQ (instImpl g) (S.main pk))

end Ideal.Realize.Tcr
#print axioms Ideal.Realize.Tcr.step1
