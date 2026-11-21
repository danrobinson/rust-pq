import Ideal.Games.TcrBridge
import Ideal.Games.TcrIdeal
import Ideal.Core.HiddenPrefix

/-!
# SM-TCR in the ideal-compression model: the bound

`Ideal.tcr_bound`: for a Merkle–Damgård tweakable-hash family whose attacked member has a single
block after the seed block, the SM-TCR advantage of an ideal-model adversary is at most
`(q₂ + 1)·δ + q₁·γ + (2 q₁ + (qch + qc)(1 + 2 L) + 2)/|St|`.

Proof: `tcrAdvantage_eq_realGame` (the game is the real game of `Core/Defs`), `hiddenPrefix`
(real ≤ ideal + bad), `tcr_ideal_le` (the ideal game).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

variable {St Blk PkSeed Tweak M Y ι : Type}

theorem tcr_bound [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (F : THFam St Blk PkSeed Tweak M Y ι) (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrAdvantage F A ≤ (q₂ + 1 : ℕ) * δ + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [tcrAdvantage_eq_realGame]
  have h1 := hiddenPrefix F.IV F.sb hsb F.seedGen γ hγ (tcrProg₁ A) (tcrP₂ A) q₁ (qch + qc) L
    (tcrProg₁_pubBound A hq₁) (tcrProg₁_chainBound A hch hc)
    (tcrProg₁_chainLen A (fun t m => by rw [hsingle]; exact Nat.zero_le _) hL)
  have h2 := tcr_ideal_le hsingle btw hbtwT hbtwC hinj δ hδ A q₂ hq₂
  refine h1.trans ((add_le_add (add_le_add h2 le_rfl) le_rfl).trans (le_of_eq ?_))
  push_cast
  ring

/-! ## Advantages over a uniform compression table

Advantages of concrete instances are stated through `idealAdvT`: at concrete types the kernel
cannot cheaply compare a definition with a `𝒟[·]`-headed term (it reduces the latter first, which
evaluates the sampler of the table type), so a definition whose body is literally `𝒟[…] {true}`
could not be unfolded.  `idealAdvT_def` and `tcrAdvantage_eq_idealAdv` are proved generically and
only instantiated. -/

/-- Probability that `X g` returns `true` for a uniformly random compression table `g`. -/
noncomputable def idealAdvT [SampleableType (CF St Blk)] (X : CF St Blk → ProbComp Bool) : ℝ≥0∞ :=
  𝒟[do
    let g ← $ᵗ (CF St Blk)
    X g] {true}

theorem idealAdvT_def [SampleableType (CF St Blk)] (X : CF St Blk → ProbComp Bool) :
    idealAdvT X = 𝒟[$ᵗ (CF St Blk) >>= X] {true} := rfl

theorem idealAdvT_congr [SampleableType (CF St Blk)] {X X' : CF St Blk → ProbComp Bool}
    (h : ∀ g, X g = X' g) : idealAdvT X = idealAdvT X' := by
  rw [funext h]

theorem tcrAdvantage_eq_idealAdv [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y ι) (A : TcrAdv F) :
    tcrAdvantage F A = idealAdvT fun g => TweakableHash.SM_DT_TCR_Experiment (A.inst g) := rfl

end Ideal

#print axioms Ideal.tcr_bound
#print axioms Ideal.tcrAdvantage_eq_idealAdv
