import Ideal.Realize.Port
import Ideal.Realize.Phase1
import Ideal.Transport.AdvTcr
import Ideal.ComposeFinal
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport
abbrev P₀ : Primitives Link.vp.params := R₀ dT dH
variable (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
example : (F128T pkSeedDist n).collS = ((_ : Unit) × Bytes 22 × List (Bytes 16) →ₒ Option (Bytes 16)) := rfl
example : (F128T pkSeedDist n).Msg () = List (Bytes 16) := rfl
example : P₀.Y = Bytes 16 := rfl
example : P₀.AdrsKey = Bytes 22 := rfl
example : (TcrP1Spec P₀ n) = (unifSpec + (SM_DT_TCR_challengeSpec (Bytes 22) {xs : List (Bytes 16) // xs.length = n} (Bytes 16) + ((_ : Unit) × Bytes 22 × List (Bytes 16) →ₒ Option (Bytes 16)))) := rfl
end Ideal.Realize.Tcr
namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport
noncomputable def advT (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) : TcrAdv128T pkSeedDist n where
  State := TcrP1State Link.vp P₀
  choose := simulateQ embImpl (tcrPhase1 Link.vp P₀ n : OracleComp (TcrP1Spec P₀ n) (TcrP1State Link.vp P₀))
  forge := fun st pk => pure (0, ⟨List.replicate n default, by simp⟩)
theorem choose_inst (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    simulateQ (instImpl g) (advT pkSeedDist n).choose = tcrPhase1 Link.vp P₀ n := by
  kexact instImpl_emb g (tcrPhase1 Link.vp P₀ n : OracleComp (TcrP1Spec P₀ n) (TcrP1State Link.vp P₀))
end Ideal.Realize.Tcr
namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport
example (g : CF St Blk) (n : ℕ) : tcrPhase1 Link.vp (R₀ (thG g) (hmG g)) n = tcrPhase1 Link.vp P₀ n :=
  tcrPhase1_withTH (prims := P₀) (thG g) (hmG g) n
end Ideal.Realize.Tcr
