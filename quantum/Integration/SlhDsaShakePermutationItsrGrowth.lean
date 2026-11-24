import Integration.SlhDsaShakePermutationItsrBanks
import Integration.SlhDsaRawFailure

/-! Probability of a fresh coherent recording step creating a graph
ambiguity or a collision on the FIPS-decoded digest. -/
namespace Reduction.ShakePermutation.ItsrLabel
open Classical Tails MLink SLHDSA Quantum OracleSpec ENNReal SetOracle
open Compression.Recording.Database (Growth assemble Rest occupied assemble_at assemble_other occupied_assemble_le)
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local irreducible] Graph.support key targets failures Bool.decEq SetOracle.uniformMean Fintype.card

def rateBound (S : Sha2Set) (t : ℕ) : ℝ≥0∞ :=
  ((extensionBudget t + t : ℕ) : ℝ≥0∞) / Fintype.card Capacity +
    (t:ℝ≥0∞)/2^(S.vp.params.h+S.vp.params.a*S.vp.params.k)

private theorem conditional {α : Type} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (impl : ∀ x, p x → q x) : uniformMean (fun x => Classic.hit (p x)) ≤ uniformMean (fun x => Classic.hit (q x)) :=
  Classic.mean_mono fun x => by
    by_cases h : p x
    · simp [Classic.hit,h,impl x h]
    · simp [Classic.hit,h]

private theorem mask_bound (S : Sha2Set) (t : ℕ) (p : Words → Prop) [DecidablePred p] (c : Capacity → Prop)
    (im : ∀ w, p w → capOf w ∈ failures c) (cnt : (failures c).card ≤ extensionBudget t+t) :
    uniformMean (fun w => Classic.hit (p w)) ≤ rateBound S t := by
  have hm := conditional (α := Words) p (fun w : Words => capOf w ∈ failures c) im
  apply hm.trans
  rw [cap_mean (fun v => Classic.hit (v ∈ failures c)),Classic.mean_hit]
  unfold rateBound
  apply le_trans _ (le_add_right le_rfl)
  gcongr

theorem mean_step (S π L) (hp : ¬irregular π) (he : ¬Pairs.exceptional π) (D : Bank) (t : ℕ) (ht : D.size ≤ t)
    (x : Addr) (empty : D x = none) (good : label S π L D = true) :
    uniformMean (fun v : Words => Classic.hit (label S π L (Function.update D x (some v)) = false)) ≤ rateBound S t := by
  have g := of_decide_eq_true (show decide (Good S π L (masks D false) (masks D true) (held D)) = true from good)
  let left := masks D false
  let right := masks D true
  let h := held D
  have kl (b : Bool) : (Graph.support (masks D b)).card ≤ t := (slice_size _ (mask_inj b) capOf D).trans ht
  have hl : (Graph.support h).card ≤ t := (slice_size _ Sum.inr_injective rateOf D).trans ht
  rcases x with ⟨b,r⟩ | z
  · have em : masks D b r = none := by simp only [masks,slice,mask,empty,Option.map_none]
    have same (w : Words) := slice_same (mask b) (mask_inj b) capOf D r w
    have other (w : Words) := slice_other (mask (!b)) capOf D (mask b r) w (by
      intro i; cases b <;> simp [mask])
    have heads (w : Words) := slice_other tailHead rateOf D (mask b r) w (by intro i; simp [tailHead,mask])
    cases b with
    | false =>
      apply mask_bound S t _ (LeftCert π left right r) _ ((leftCert_card π hp he left right g.1 t (kl false) (kl true) r).trans (Nat.le_add_right _ _))
      intro w b
      apply (mem_failures (LeftCert π left right r) (capOf w)).mpr
      intro cert
      apply (of_decide_eq_false (show decide _ = false from b))
      change Good S π L (slice _ _ _) (slice _ _ _) (slice _ _ _)
      simp only [mask,Bool.not_false] at same other heads
      rw [same w,other w,heads w]
      exact good_left g em cert
    | true =>
      apply mask_bound S t _ (RightCert π left right (Graph.support h) r) _ ((rightCert_card π hp he left right g.1 t (kl false) (kl true) (Graph.support h) r).trans (Nat.add_le_add_left hl _))
      intro w b
      apply (mem_failures (RightCert π left right (Graph.support h) r) (capOf w)).mpr
      intro cert
      apply (of_decide_eq_false (show decide _ = false from b))
      change Good S π L (slice _ _ _) (slice _ _ _) (slice _ _ _)
      simp only [mask,Bool.not_true] at same other heads
      rw [other w,same w,heads w]
      exact good_right g em cert
  · let B := targets S π L left right h
    let pre := preHead π L left right z
    have im (w : Words) (bad : label S π L (Function.update D (.inr z) (some w)) = false) : key S pre (rateOf w) ∈ B := by
      by_contra miss
      apply (of_decide_eq_false (show decide _ = false from bad))
      have km (b : Bool) := slice_other (mask b) capOf D (.inr z) w (by intro i; simp [mask])
      have hm := slice_same tailHead Sum.inr_injective rateOf D z w
      change Good S π L (slice _ _ _) (slice _ _ _) (slice _ _ _)
      rw [km,km]
      change Good S π L left right (slice tailHead rateOf (Function.update D (tailHead z) (some w)))
      rw [hm]; exact good_head g miss
    apply (conditional _ _ im).trans
    rw [rate_mean (fun y => Classic.hit (key S pre y ∈ B)),key_mean]
    unfold rateBound
    apply le_trans _ (le_add_left le_rfl)
    gcongr
    exact (targets_card S π L left right h).trans hl

end
end Reduction.ShakePermutation.ItsrLabel
