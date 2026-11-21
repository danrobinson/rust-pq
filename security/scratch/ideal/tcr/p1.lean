import Ideal.Transport.Verify
import Ideal.Transport.Sign
import Reduction.Open.Phase1Tcr

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Transport
open Reduction

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

theorem tcrAdv_ext {ι PkSeed Tweak M Y : Type} [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (a b : SM_DT_TCR_Adversary prob)
    (hS : a.State = b.State) (hc : HEq a.choose b.choose) (hf : HEq a.forge b.forge) : a = b := by
  cases a; cases b
  cases hS
  cases hc; cases hf
  rfl

theorem bTcrArM_choose_setPrf (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (A' : Forger vp (setPrf prims prf pm) optRand' pkSeedDist) :
    ((bTcrArM n A').choose : OracleComp (Open.TcrP1Spec prims n) (Open.TcrP1State vp prims)) =
      (bTcrArM n A).choose :=
  (Open.bTcrArM_choose_eq n A').trans (by krfl)

include hopt in
theorem bTcrArM_bytesToTyped_setPrf (n : ℕ)
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte)) :
    bTcrArM (prims := setPrf prims prf pm) n
        (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) =
      bTcrArM n (bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩) := by
  have hc := bTcrArM_choose_setPrf prf pm optRand optRand' pkSeedDist n
    (bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩)
    (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)
  have hf := fun s pk => bTcrArM_forge_setPrf prims prf pm n
    (bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩)
    (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)
    (fun tbl pk => g2Run_bytesToTyped_tr prf pm codec optRand optRand' hopt pkSeedDist S tbl pk) s pk
  exact tcrAdv_ext _ _ rfl (heq_of_eq hc) (heq_of_eq (funext fun s => funext fun pk => hf s pk))
end Ideal.Transport
