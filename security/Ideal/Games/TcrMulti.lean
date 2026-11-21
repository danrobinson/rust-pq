import Ideal.Games.Tcr
import Ideal.Games.TcrMultiIdeal

/-!
# SM-TCR in the ideal-compression model: the bound for multi-block members

`Ideal.tcr_bound_multi`: for a Merkle–Damgård tweakable-hash family whose attacked member has
`L` blocks after the first message block (for every input), with injective full block lists, the
SM-TCR advantage of an ideal-model adversary is at most
`(q₂ + 2 L + 4)·δ + q₁·γ + (18·Q² + 2 q₁ + (qch + qc)(1 + 2·max L Lc) + 1)/|St|`,
`Q = tcrMultiQ q₁ qch qc Lc q₂ L = q₁ + q₂ + (qch + qc)(1 + max L Lc) + 2 (L + 1) + 1`.

Proof: `tcrAdvantage_eq_realGame`, `hiddenPrefix` (real ≤ ideal + bad, with continuation bound
`max L Lc`), `tcr_ideal_multi_le` (the ideal game).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

variable {St Blk PkSeed Tweak M Y ι : Type}

/-- The collection-length bound of an adversary is monotone. -/
theorem TcrAdv.CollLen.mono {F : THFam St Blk PkSeed Tweak M Y ι} {A : TcrAdv F} {L L' : ℕ}
    (h : A.CollLen L) (hL : L ≤ L') : A.CollLen L' :=
  AllQueriesSatisfy.mono h fun t ht => by
    rcases t with n | q | tm | q
    · exact ht
    · exact ht
    · exact ht
    · exact le_trans ht hL

theorem tcr_bound_multi [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (F : THFam St Blk PkSeed Tweak M Y ι) (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (L : ℕ) (hlen : ∀ t m, (F.tch t m).2.length = L)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', F.tch t m = F.tch t m' → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₁ qch qc Lc q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hLc : A.CollLen Lc) (hq₂ : A.ForgeBound q₂) :
    tcrAdvantage F A ≤ (q₂ + 2 * L + 4 : ℕ) * δ + q₁ * γ +
      (18 * tcrMultiQ q₁ qch qc Lc q₂ L ^ 2 + 2 * q₁ + (qch + qc) * (1 + 2 * max L Lc) + 1 : ℕ) *
        (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [tcrAdvantage_eq_realGame]
  have h1 := hiddenPrefix F.IV F.sb hsb F.seedGen γ hγ (tcrProg₁ A) (tcrP₂ A) q₁ (qch + qc)
    (max L Lc) (tcrProg₁_pubBound A hq₁) (tcrProg₁_chainBound A hch hc)
    (tcrProg₁_chainLen A (fun t m => by rw [hlen]; exact le_max_left _ _)
      (hLc.mono (le_max_right _ _)))
  have h2 := tcr_ideal_multi_le L hlen btw hbtwT hbtwC hinj δ hδ A q₁ qch qc Lc q₂ hq₁ hch hc
    hLc hq₂
  refine h1.trans ((add_le_add (add_le_add h2 le_rfl) le_rfl).trans (le_of_eq ?_))
  push_cast
  ring

end Ideal

#print axioms Ideal.tcr_bound_multi
