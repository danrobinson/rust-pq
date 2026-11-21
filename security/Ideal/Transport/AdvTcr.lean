import Ideal.Transport.Verify
import Ideal.Transport.Sign
import Reduction.Open.Phase1Tcr

/-!
# Whole-adversary invariance of the class-TCR adversaries `bTcrArM n` under `setPrf`

`bTcrArM_forge_setPrf` (`Transport/Verify.lean`) is the second phase under a hypothesis `hrun` on
the forger's run.  Here `hrun` is discharged at the byte-level forger wrapper
(`g2Run_bytesToTyped_tr`, `Transport/Sign.lean`) and the first phase (`choose`, which is the
forger-free program `Reduction.Open.tcrPhase1`, `bTcrArM_choose_eq`) is shown to be the same
term at both bundles.  Result: the WHOLE adversary over `setPrf prims prf pm`, built from a
byte-level forger program `S` with the transported codec, EQUALS the adversary over `prims` built
from `S` (`bTcrArM_bytesToTyped_setPrf`, EUF wrapper; `bTcrArM_bytesToTypedS_setPrf`, SUF
wrapper).  The two sides live over `thashArityProblemT vp (setPrf prims prf pm) …` and
`thashArityProblemT vp prims …`, which are the same term up to unfolding the reducible `setPrf`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Transport

open Reduction

/-- Extensionality for SM-TCR adversaries with heterogeneous phase equalities. -/
theorem tcrAdv_ext_AdvTcr {ι PkSeed Tweak M Y : Type} [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (a b : SM_DT_TCR_Adversary prob)
    (hS : a.State = b.State) (hc : HEq a.choose b.choose) (hf : HEq a.forge b.forge) : a = b := by
  cases a; cases b
  cases hS
  cases hc; cases hf
  rfl

section Tcr

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- The first phase of `bTcrArM n` does not depend on `PRF`, `PRF_msg` (nor on the forger). -/
theorem bTcrArM_choose_setPrf (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (A' : Forger vp (setPrf prims prf pm) optRand' pkSeedDist) :
    ((bTcrArM n A').choose : OracleComp (Open.TcrP1Spec prims n) (Open.TcrP1State vp prims)) =
      (bTcrArM n A).choose :=
  (Open.bTcrArM_choose_eq n A').trans (by krfl)

include hopt in
/-- **Whole-adversary invariance of `bTcrArM n` under `setPrf`, EUF wrapper.**  The class-TCR
adversary over `setPrf prims prf pm`, built from the byte-level forger program `S` (codec
`trCodec codec`, `opt_rand` sampler `optRand'` agreeing with `optRand` along `trPk`), is the
adversary over `prims` built from `S`. -/
theorem bTcrArM_bytesToTyped_setPrf (n : ℕ)
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte)) :
    bTcrArM (prims := setPrf prims prf pm) n
        (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) =
      bTcrArM n (bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
        ⟨S⟩) := by
  have hc := bTcrArM_choose_setPrf prf pm optRand optRand' pkSeedDist n
    (bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩)
    (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
      (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)
  have hf := fun s pk => bTcrArM_forge_setPrf prims prf pm n
    (bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩)
    (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
      (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)
    (fun tbl pk => g2Run_bytesToTyped_tr prf pm codec optRand optRand' hopt pkSeedDist S tbl pk)
    s pk
  exact tcrAdv_ext_AdvTcr _ _ rfl (heq_of_eq hc)
    (heq_of_eq (funext fun s => funext fun pk => hf s pk))

include hopt in
/-- **Whole-adversary invariance of `bTcrArM n` under `setPrf`, SUF wrapper** (`bytesToTypedS`). -/
theorem bTcrArM_bytesToTypedS_setPrf (n : ℕ)
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte)) :
    bTcrArM (prims := setPrf prims prf pm) n
        (bytesToTypedS (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary =
      bTcrArM n (bytesToTypedS (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
        ⟨S⟩).toUnforgeableAdversary :=
  bTcrArM_bytesToTyped_setPrf prf pm codec optRand optRand' hopt pkSeedDist n S

end Tcr

end Ideal.Transport

#print axioms Ideal.Transport.tcrAdv_ext_AdvTcr
#print axioms Ideal.Transport.bTcrArM_choose_setPrf
#print axioms Ideal.Transport.bTcrArM_bytesToTyped_setPrf
#print axioms Ideal.Transport.bTcrArM_bytesToTypedS_setPrf
