import Ideal.Games.PreBridge
import Ideal.Games.PreIdeal
import Ideal.Core.HiddenPrefix

/-!
# SM-PRE in the ideal-compression model: the bound

`Ideal.pre_bound`: for a Merkle–Damgård tweakable-hash family whose attacked member has a single
block after the seed block and an injective `emb : M' → M`, the SM-PRE advantage of an
ideal-model adversary is at most
`(q₂ + 1)·δ + (q₂ + 1)/|M'| + q₁·γ + (2 q₁ + (qch + qc)(1 + 2 L) + 2)/|St|`.

Proof: `preAdvantage_eq_realGame` (the game is the real game of `Core/Defs`), `hiddenPrefix`
(real ≤ ideal + bad), `pre_ideal_le` (the ideal game).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

variable {St Blk PkSeed Tweak M M' Y ι : Type}

theorem pre_bound [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    [DecidableEq Tweak] [DecidableEq Y] [SampleableType M'] [Fintype M']
    (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (hemb : Function.Injective emb)
    (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : PreAdv F M') (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.InvertBound q₂) :
    preAdvantage F emb hemb A ≤
      (q₂ + 1 : ℕ) * δ + (q₂ + 1 : ℕ) * (Fintype.card M' : ℝ≥0∞)⁻¹ + q₁ * γ +
        (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [preAdvantage_eq_realGame]
  have h1 := hiddenPrefix F.IV F.sb hsb F.seedGen γ hγ (preProg₁ emb A) (preP₂ emb A) q₁
    (qch + qc) L (preProg₁_pubBound emb A hq₁) (preProg₁_chainBound emb A hch hc)
    (preProg₁_chainLen emb A (fun t m => by rw [hsingle]; exact Nat.zero_le _) hL)
  have h2 := pre_ideal_le emb hemb hsingle btw hbtwT hbtwC hinj δ hδ A q₂ hq₂
  refine h1.trans ((add_le_add (add_le_add h2 le_rfl) le_rfl).trans (le_of_eq ?_))
  push_cast
  ring

end Ideal

#print axioms Ideal.pre_bound
