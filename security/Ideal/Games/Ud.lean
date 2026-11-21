import Ideal.Games.UdBridge
import Ideal.Games.UdIdeal
import Ideal.Core.HiddenPrefix

/-!
# SM-UD in the ideal-compression model: the bound

`Ideal.ud_bound` (one-sided, the form consumed by the Reduction's linear headline): for a
Merkle–Damgård tweakable-hash family whose attacked member has a single block after the seed
block and whose output map sends uniform chaining values to uniform outputs, and an injective
`emb : M' → M`, the table-averaged success probabilities of VCVio's SM-UD experiments satisfy

`udRealI ≤ udIdealI + q₂/|M'| + 2·q₁·γ + 2·(2 q₁ + (qch + qc)(1 + 2 L) + 1)/|St|`.

`Ideal.ud_bound_ge` is the reverse inequality with the same error (`ud_bound` applied to the
adversary with its bit negated); together they bound the distinguishing advantage.

Proof: `udRealI_eq_realGame`, `udIdealI_eq_realGame` (both worlds are real games of
`Core/Defs`), `hiddenPrefix` for the real world, `ud_ideal_le` (the two ideal games),
`hiddenPrefix_ge` for the ideal world.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M M' Y ι : Type}

theorem ud_bound [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    [DecidableEq Tweak] [SampleableType M'] [Fintype M'] [SampleableType Y] [Finite Y]
    (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (hemb : Function.Injective emb)
    (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (F.out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : UdAdv F) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂) :
    udRealI F emb hemb A ≤
      udIdealI F emb hemb A + q₂ * (Fintype.card M' : ℝ≥0∞)⁻¹ + 2 * q₁ * γ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [udRealI_eq_realGame, udIdealI_eq_realGame]
  have hT : ∀ t m, (F.tch t m).2.length ≤ L := fun t m => by rw [hsingle]; exact Nat.zero_le _
  have h1 := hiddenPrefix F.IV F.sb hsb F.seedGen γ hγ (udProg₁ .real emb A) (udP₂ A) q₁
    (qch + qc) L (udProg₁_pubBound .real emb A hq₁) (udProg₁_chainBound .real emb A hch hc)
    (udProg₁_chainLen .real emb A hT hL)
  have h2 := ud_ideal_le emb hemb hsingle btw hbtwT hbtwC hinj hout A q₂ hq₂
  have h3 := hiddenPrefix_ge F.IV F.sb hsb F.seedGen γ hγ (udProg₁ .ideal emb A) (udP₂ A) q₁
    (qch + qc) L (udProg₁_pubBound .ideal emb A hq₁) (udProg₁_chainBound .ideal emb A hch hc)
    (udProg₁_chainLen .ideal emb A hT hL)
  refine h1.trans ((add_le_add (add_le_add (h2.trans (add_le_add h3 le_rfl)) le_rfl)
    le_rfl).trans (le_of_eq ?_))
  push_cast
  ring

section Neg

variable {F : THFam St Blk PkSeed Tweak M Y ι}

theorem udRealI_neg [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    [SampleableType (CF St Blk)] (emb : M' → M) (hemb : Function.Injective emb) (A : UdAdv F) :
    udRealI F emb hemb A.neg = 1 - udRealI F emb hemb A := by
  rw [udRealI_eq_realGame, udRealI_eq_realGame]
  show 𝒟[realGame F.IV F.sb F.seedGen (udProg₁ .real emb A)
    (fun pk x => not <$> udP₂ A pk x)] {true} = _
  rw [realGame_not, ← HP.prT_eq, ← HP.prT_eq, prT_not]

theorem udIdealI_neg [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    [SampleableType (CF St Blk)] (emb : M' → M) (hemb : Function.Injective emb) (A : UdAdv F) :
    udIdealI F emb hemb A.neg = 1 - udIdealI F emb hemb A := by
  rw [udIdealI_eq_realGame, udIdealI_eq_realGame]
  show 𝒟[realGame F.IV F.sb F.seedGen (udProg₁ .ideal emb A)
    (fun pk x => not <$> udP₂ A pk x)] {true} = _
  rw [realGame_not, ← HP.prT_eq, ← HP.prT_eq, prT_not]

theorem udIdealI_le_one [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    [SampleableType (CF St Blk)] (emb : M' → M) (hemb : Function.Injective emb) (A : UdAdv F) :
    udIdealI F emb hemb A ≤ 1 := by
  rw [udIdealI_eq_realGame, ← HP.prT_eq]
  exact HP.prT_le_one _

end Neg

/-- The reverse inequality of `ud_bound`, with the same error. -/
theorem ud_bound_ge [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    [DecidableEq Tweak] [SampleableType M'] [Fintype M'] [SampleableType Y] [Finite Y]
    (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (hemb : Function.Injective emb)
    (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (F.out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : UdAdv F) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂) :
    udIdealI F emb hemb A ≤
      udRealI F emb hemb A + q₂ * (Fintype.card M' : ℝ≥0∞)⁻¹ + 2 * q₁ * γ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have h := ud_bound F emb hemb hsb γ hγ hsingle btw hbtwT hbtwC hinj hout A.neg q₁ qch qc L q₂
    hq₁ hch hc hL (fun st pk => (isQueryBoundP_map_iff _ _ _).mpr (hq₂ st pk))
  rw [udRealI_neg, udIdealI_neg] at h
  have hb := udIdealI_le_one emb hemb A
  rw [← ENNReal.sub_sub_cancel ENNReal.one_ne_top hb, tsub_le_iff_left]
  calc (1 : ℝ≥0∞) ≤ (1 - udRealI F emb hemb A) + udRealI F emb hemb A := le_tsub_add
    _ ≤ _ := by
      refine (add_le_add h le_rfl).trans (le_of_eq ?_)
      ring

end Ideal

#print axioms Ideal.ud_bound
#print axioms Ideal.ud_bound_ge
