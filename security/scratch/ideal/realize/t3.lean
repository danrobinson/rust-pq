import Ideal.Realize.Chain
import Ideal.ComposeFinal
import Ideal.Transport.Verify
import Ideal.Transport.Sign
open OracleComp OracleSpec SLHDSA SLHDSA.Security Reduction
namespace Ideal.Realize
open Ideal.Transport Reduction.Open

def core₀ : CorePrimitives Link.vp.params where
  PkSeed := Bytes 16
  SkSeed := Bytes 16
  SkPrf := Bytes 16
  Y := Bytes 16
  AdrsKey := Bytes 22
  adrsToKey := SLHDSA.Concrete.sha2AdrsKey
  PRF := fun pk _ _ => pk
  PRFmsg := fun k _ _ => k
  yToBytes := id

@[reducible] def R₀ (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) : Primitives Link.vp.params :=
  { toCorePrimitives := core₀, Thash := T, Hmsg := H }

instance (priority := high) : SampleableType core₀.SkSeed := inferInstanceAs (SampleableType (Bytes 16))
instance (priority := high) : SampleableType core₀.SkPrf := inferInstanceAs (SampleableType (Bytes 16))
instance (priority := high) : SampleableType core₀.PkSeed := inferInstanceAs (SampleableType (Bytes 16))
instance (priority := high) : SampleableType core₀.Y := inferInstanceAs (SampleableType (Bytes 16))
instance (priority := high) : DecidableEq core₀.Y := inferInstanceAs (DecidableEq (Bytes 16))
instance (priority := high) : DecidableEq core₀.PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
instance (priority := high) : DecidableEq core₀.AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
instance (priority := high) : Inhabited core₀.Y := ⟨Vector.replicate 16 0⟩

theorem primsG_eq (g : CF St Blk) :
    primsG (liftC g) = setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) := rfl

example (g : CF St Blk) (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16)) (n : ℕ)
  (X : ∀ (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30)
    (prf : Bytes 16 → Bytes 16 → Adrs → Bytes 16) (pm : Bytes 16 → Bytes 16 → List Byte → Bytes 16)
    (A' : Forger Link.vp (setPrf (R₀ T H) prf pm) (fun pk => oR pk.pkSeed pk.pkRoot) d),
      𝒟[TweakableHash.SM_DT_TCR_Experiment (bTcrArM n A')] = 𝒟[(pure true : ProbComp Bool)]) :
   𝒟[TweakableHash.SM_DT_TCR_Experiment (bTcrArM n (S.typedS (optRandU oR) d g))] = 𝒟[(pure true : ProbComp Bool)] :=
  X (thG g) (hmG g) (prfG g) (pmG g) (S.typedS (optRandU oR) d g)
end Ideal.Realize
