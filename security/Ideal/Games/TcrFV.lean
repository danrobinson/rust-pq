import Ideal.Games.TcrFVBridge
import Ideal.Games.TcrFVIdeal
import Ideal.Core.HiddenPrefix

/-!
# Source-final-validity SM-TCR (stand-alone) in the ideal-compression model: the bound

`Ideal.tcrFV_bound`: for a Merkle–Damgård tweakable hash whose attacked member has a single
block after the seed block, with that block injective in the message and determining the tweak,

`Adv^{SM-TCR, final validity}(A) ≤ (q₂ + 1)·δ + q₁·γ + (2·q₁ + qch + 2)/|St|`

where `q₁`, `q₂` bound the compression queries of the two phases of `A`, `qch` its challenge
queries, `γ` the guessing probability of the seed and `δ` the probability that the output map
hits a fixed value on a uniform chaining value.

Proof: `tcrFVAdvantage_eq_realGame` (bridge), `hiddenPrefix` with `C = qch`, `L = 0`
(which contributes `q₁·γ + (2·q₁ + qch·(1 + 2·0) + 1)/|St|`), `tcrFV_ideal_le`
(which contributes `(q₂ + 1)·δ + 1/|St|`).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y : Type} {F : THFam St Blk PkSeed Tweak M Y Empty}

theorem tcrFV_bound [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : FvAdv F) (q₁ qch q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hqch : A.ChalBound qch) (hq₂ : A.ForgeBound q₂) :
    tcrFVAdvantage F A ≤
      (q₂ + 1 : ℕ) * δ + q₁ * γ + (2 * q₁ + qch + 2 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [tcrFVAdvantage_eq_realGame]
  refine (hiddenPrefix F.IV F.sb hsb F.seedGen γ hγ (fvProg₁ A) (fvP₂ A) q₁ qch 0
    (fvProg₁_pubBound A hq₁) (fvProg₁_chainBound A hqch)
    (fvProg₁_chainLen A fun t m => by rw [hsingle]; exact le_rfl)).trans ?_
  refine (add_le_add_left (add_le_add_left
    (tcrFV_ideal_le hsingle btw hbtwT hinj δ hδ A q₂ hq₂) _) _).trans (le_of_eq ?_)
  push_cast
  ring

end Ideal

#print axioms Ideal.tcrFV_bound
