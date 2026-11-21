import PQ.QROM.MultiTarget
import PQ.QROM.Hybrid

/-!
# Target subset resilience of a random function, non-adaptive targets (ITSR, one-shot form)

`H : K × Xm → D` is a uniformly random function (`K` randomizers, `Xm` inputs, `D` digests).
`Cov : Finset D → D → Prop` is an abstract cover relation ("every index selected by the digest `u`
is selected by one of the digests in the set"; for SLH-DSA: the FORS index tuples).

## What is shown

* `itsr_fixed_le` (core): for ANY fixed finite set `Tg` of target points of the domain and any
  "covered set" `cov H : Finset D` that depends on `H` only through its values on `Tg`, a
  `q`-query algorithm outputs a point outside `Tg` whose value lies in `cov H` with probability
  at most `(2q+1)² · E_H[|cov H| / |D|]`.
* `itsr_nonadaptive_le`: the non-adaptive ITSR game.  The target inputs `xs : ι → Xm` are fixed
  (chosen independently of `H`); the randomizers `Rs : ι → K` are uniform and handed to the
  adversary up front; the adversary makes `q` quantum queries to `H`, outputs `(R*, x*)`, and
  wins iff `(R*, x*)` is not one of the targets `(Rs i, xs i)` and
  `Cov {H (Rs i, xs i)} (H (R*, x*))`.  Bound: `(2q+1)² · itsrCoverProb`, where `itsrCoverProb`
  is the exact probability, in this very game, that a fresh uniform digest is covered by the
  target digests (an explicit finite average over `H`, `Rs` and the fresh digest).  No slack:
  colliding target points are handled exactly (they share a digest).
* `itsrCoverProb_le`: `itsrCoverProb ≤ coverProb + |ι|² / |K|`, where `coverProb` is the covering
  probability of a fresh uniform digest by `|ι|` INDEPENDENT uniform digests; the slack accounts
  for colliding randomizers (equality without slack when the target points are distinct:
  `sum_comp_injective`).
* `itsr_nonadaptive_le'`: the combined bound `(2q+1)² (coverProb + |ι|²/|K|)`;
  `itsr_nonadaptive_program_le`: the same for VCVio quantum query programs.

Coupling (per slice of the values `g` of `H` on the target points, so that the covered set `C` is
fixed): worlds `τ : X → D × Res D`; the real function is `g` on `Tg` and `Prod.fst ∘ τ` elsewhere;
a non-target point is marked iff its value lies in `C`; the hybrid function replaces a marked
value by a uniform element of the uncovered set `Cᶜ` (the randomness `Res D` contains a uniform
element of every nonempty subset of `D`).  Given the hybrid function, a non-target point is
marked with probability exactly `|C| / |D|` (`resU_fiber`).  Slices with `C = D` are bounded
trivially.  The slices are recombined with `sum_mix`.

## What is NOT shown

* ADAPTIVE target selection: in VCVio's `KeyedHash.ITSRAdvantage` (and in HK22 Def. 9) the
  adversary chooses the target inputs adaptively, interleaved with its (quantum) hash queries, and
  each target query is answered with a fresh randomizer.  Here the target inputs are fixed before
  `H` is sampled and all randomizers are given up front.  The adaptive game needs adaptive
  reprogramming of `H` at `(R_i, x_i)` for a fresh `R_i` (a Grilo–Hövelmanns–Hülsing–Majenz-type
  lemma), which is not available in the fixed-oracle `HybridModel` interface.  (With a fixed
  oracle one can only hand over a randomizer for every possible target query up front and take a
  union bound over the adversary's selection of `|ι|` of them, which loses a factor
  `C(#possible targets, |ι|)`; this is not formalised.)
* The closed form of `coverProb` for the FORS index structure.  For `D = (Fin (2^h)) × (Fin k →
  Fin t)` (hypertree leaf and `k` FORS indices in trees of `t` leaves) and `Cov S (j, v)` iff
  for every `i < k` some `(j, v') ∈ S` has `v' i = v i`, one has
  `coverProb = ∑_γ (1 − (1 − 1/t)^γ)^k · C(s, γ) (1 − 1/2^h)^(s−γ) (1/2^h)^γ` with `s = |ι|`
  (SPHINCS+ submission, Section 9.3.1); this evaluation is not proved here.
-/

open ENNReal Finset

universe u v w

namespace PQ.QROM

section Resample

variable {D : Type} [Fintype D] [DecidableEq D]

/-- Resampling randomness: a (uniform) element of every nonempty subset of `D`. -/
abbrev Res (D : Type) [DecidableEq D] : Type := ∀ U : {U : Finset D // U.Nonempty}, ↥U.1

instance : Nonempty (Res D) := ⟨fun U ↦ ⟨U.2.choose, U.2.choose_spec⟩⟩

/-- A coordinate of a uniform `Res D` is uniform. -/
theorem sum_res_coord (U : {U : Finset D // U.Nonempty}) :
    ∃ m : ℕ, ∀ f : ↥U.1 → ℝ≥0∞, ∑ r : Res D, f (r U) = m * ∑ a, f a := by
  refine ⟨Fintype.card (∀ j : {j // j ≠ U}, ↥j.1.1), fun f ↦ ?_⟩
  rw [← Equiv.sum_comp (Equiv.piSplitAt U fun U : {U : Finset D // U.Nonempty} ↦ ↥U.1).symm,
    Fintype.sum_prod_type]
  simp [Equiv.piSplitAt, Finset.mul_sum]

/-- The hybrid value: a value outside `U` (covered) is replaced by the element of `U` provided by
the randomness. -/
def resU (U : {U : Finset D // U.Nonempty}) (t : D × Res D) : D :=
  if t.1 ∈ U.1 then t.1 else (t.2 U : D)

omit [Fintype D] in
theorem resU_mem (U : {U : Finset D // U.Nonempty}) (t : D × Res D) : resU U t ∈ U.1 := by
  unfold resU
  split_ifs with h
  · exact h
  · exact (t.2 U).2

/-- The probability that a uniform value is outside `U`. -/
noncomputable def pMark (U : {U : Finset D // U.Nonempty}) : ℝ≥0∞ :=
  ((U.1ᶜ.card : ℕ) : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹

/-- Given the hybrid value, a point is marked (real value outside `U`) with probability
`|Uᶜ| / |D|`. -/
theorem resU_fiber (U : {U : Finset D // U.Nonempty}) (z : D) :
    ∑ t : D × Res D with resU U t = z, (if t.1 ∈ U.1 then (0 : ℝ≥0∞) else 1) =
      ∑ t : D × Res D with resU U t = z, pMark U := by
  by_cases hz : z ∈ U.1
  · have : Nonempty D := ⟨z⟩
    obtain ⟨mm, hm⟩ := sum_res_coord U
    have h1 : ∑ r : Res D, (if (r U : D) = z then (1 : ℝ≥0∞) else 0) = mm := by
      rw [hm (fun a ↦ if (a : D) = z then 1 else 0), Finset.sum_eq_single (⟨z, hz⟩ : ↥U.1)]
      · simp
      · intro a _ ha
        have : (a : D) ≠ z := fun h ↦ ha (Subtype.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : ∀ v : ℝ≥0∞, ∑ _r : Res D, v = mm * (U.1.card * v) := by
      intro v
      rw [hm (fun _ ↦ v)]
      simp
    have hL : ∑ h : D, ∑ r : Res D,
        (if resU U (h, r) = z then (if h ∈ U.1 then (0 : ℝ≥0∞) else 1) else 0) =
          (U.1ᶜ.card : ℝ≥0∞) * mm := by
      rw [← Finset.sum_add_sum_compl U.1]
      have a1 : ∀ h ∈ U.1, ∑ r : Res D,
          (if resU U (h, r) = z then (if h ∈ U.1 then (0 : ℝ≥0∞) else 1) else 0) = 0 := by
        intro h hh
        simp [hh]
      have a2 : ∀ h ∈ U.1ᶜ, ∑ r : Res D,
          (if resU U (h, r) = z then (if h ∈ U.1 then (0 : ℝ≥0∞) else 1) else 0) = mm := by
        intro h hh
        have hh' : h ∉ U.1 := Finset.mem_compl.1 hh
        rw [← h1]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        simp [resU, hh']
      rw [Finset.sum_congr rfl a1, Finset.sum_congr rfl a2]
      simp
    have hR : ∑ h : D, ∑ r : Res D, (if resU U (h, r) = z then pMark U else 0) =
        mm * (U.1.card * pMark U) + (U.1ᶜ.card : ℝ≥0∞) * (mm * pMark U) := by
      rw [← Finset.sum_add_sum_compl U.1]
      have a1 : ∀ h ∈ U.1, ∑ r : Res D, (if resU U (h, r) = z then pMark U else 0) =
          if h = z then mm * (U.1.card * pMark U) else 0 := by
        intro h hh
        by_cases hhz : h = z
        · subst hhz
          simp only [↓reduceIte]
          rw [← h2]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          simp [resU, hh]
        · simp [resU, hh, hhz]
      have a2 : ∀ h ∈ U.1ᶜ, ∑ r : Res D, (if resU U (h, r) = z then pMark U else 0) =
          mm * pMark U := by
        intro h hh
        have hh' : h ∉ U.1 := Finset.mem_compl.1 hh
        rw [← h1, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        simp [resU, hh']
      rw [Finset.sum_congr rfl a1, Finset.sum_congr rfl a2, Finset.sum_ite_eq']
      simp [hz]
    have hc : (U.1.card : ℝ≥0∞) + (U.1ᶜ.card : ℝ≥0∞) = (Fintype.card D : ℝ≥0∞) := by
      exact_mod_cast Finset.card_add_card_compl U.1
    rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine hL.trans (Eq.trans ?_ hR.symm)
    calc (U.1ᶜ.card : ℝ≥0∞) * mm
        = (U.1ᶜ.card : ℝ≥0∞) * mm *
            ((Fintype.card D : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
          rw [natCast_mul_inv_cancel Fintype.card_ne_zero, mul_one]
      _ = (U.1ᶜ.card : ℝ≥0∞) * mm *
            (((U.1.card : ℝ≥0∞) + (U.1ᶜ.card : ℝ≥0∞)) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
          rw [hc]
      _ = _ := by unfold pMark; ring
  · have : (univ.filter fun t : D × Res D ↦ resU U t = z) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun t _ h ↦ hz (h ▸ resU_mem U t)
    rw [this]; simp

end Resample

section Core

variable {X D : Type} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- `g` on the target points, `H` elsewhere. -/
def mix (Tg : Finset X) (g H : X → D) : X → D := fun k ↦ if k ∈ Tg then g k else H k

omit [Fintype X] [Fintype D] [DecidableEq D] in
theorem mix_mix (Tg : Finset X) (g H : X → D) : mix Tg (mix Tg g H) (mix Tg H g) = g := by
  funext k
  by_cases hk : k ∈ Tg <;> simp [mix, hk]

omit [DecidableEq D] in
/-- Two independent uniform functions mixed along `Tg` give a uniform function. -/
theorem sum_mix (Tg : Finset X) (F : (X → D) → ℝ≥0∞) :
    ∑ g : X → D, ∑ H : X → D, F (mix Tg g H) = Fintype.card (X → D) * ∑ H : X → D, F H := by
  have hinv : Function.Involutive
      (fun v : (X → D) × (X → D) ↦ (mix Tg v.1 v.2, mix Tg v.2 v.1)) := by
    intro v
    simp only [mix_mix]
  have h := Equiv.sum_comp hinv.toPerm (fun v : (X → D) × (X → D) ↦ F v.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  simp only [Function.Involutive.coe_toPerm] at h
  rw [h]
  simp [Finset.mul_sum]

/-- Given the hybrid function, a non-target point is marked (real value outside `U`) with
probability `|Uᶜ| / |D|`; target points are never marked. -/
theorem hidden_itsr (Tg : Finset X) (g : X → D) (U : {U : Finset D // U.Nonempty}) (κ : ℝ≥0∞) :
    Hidden (Ω := X → D × Res D) (fun _ ↦ κ)
      (fun τ k ↦ if k ∈ Tg then g k else resU U (τ k))
      (fun τ ↦ univ.filter fun k ↦ k ∉ Tg ∧ (τ k).1 ∉ U.1) (pMark U) := by
  intro k φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk : k ∈ Tg
  · simp [hk]
  · set G : (X → D × Res D) → X → D := fun τ j ↦ if j ∈ Tg then g j else resU U (τ j) with hG
    have e := sum_coord_change k (resU U) (resU U)
      (fun t ↦ if t.1 ∈ U.1 then (0 : ℝ≥0∞) else 1) (fun _ ↦ pMark U) (resU_fiber U)
      (fun z τ ↦ κ * φ (Function.update (G τ) k z)) (by
        intro z τ t
        have : Function.update (G (Function.update τ k t)) k z = Function.update (G τ) k z := by
          funext j
          by_cases hj : j = k
          · rw [hj]; simp
          · simp [hG, Function.update_of_ne hj]
        simp only [this])
    have hupd : ∀ τ, Function.update (G τ) k (resU U (τ k)) = G τ := fun τ ↦ by
      have : G τ k = resU U (τ k) := by simp [hG, hk]
      rw [← this]; exact Function.update_eq_self _ _
    simp only [hupd] at e
    refine le_of_eq ?_
    rw [Finset.mul_sum, ← e]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    simp only [hk, not_false_eq_true, true_and]
    split_ifs <;> simp [hG]

variable {Leaf : Type} {q : ℕ}

/-- One slice: the values on the target points are those of `g`, the covered set is `C`. -/
theorem itsr_slice_le [Nonempty D] (Tg : Finset X) (g : X → D) (C : Finset D)
    (M : HybridModel X D Leaf q) (out : Leaf → X) :
    ∑ H : X → D, (Fintype.card (X → D) : ℝ≥0∞)⁻¹ *
        M.prob (mix Tg g H) (fun l ↦ out l ∉ Tg ∧ mix Tg g H (out l) ∈ C) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * ((C.card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
  have hXD : Fintype.card (X → D) ≠ 0 := Fintype.card_ne_zero
  set cXD : ℝ≥0∞ := (Fintype.card (X → D) : ℝ≥0∞) with hcXD
  have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel hXD
  by_cases hU : Cᶜ.Nonempty
  · set U : {U : Finset D // U.Nonempty} := ⟨Cᶜ, hU⟩ with hUdef
    have hXR : Fintype.card (X → Res D) ≠ 0 := Fintype.card_ne_zero
    set cXR : ℝ≥0∞ := (Fintype.card (X → Res D) : ℝ≥0∞) with hcXR
    have iXR : cXR * cXR⁻¹ = 1 := natCast_mul_inv_cancel hXR
    set κ : ℝ≥0∞ := cXD⁻¹ * cXR⁻¹ with hκ
    have hw : ∑ _τ : X → D × Res D, κ ≤ 1 := by
      have := sum_fst_comp (X := X) (A := D) (B := Res D) (fun _ ↦ κ)
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc cXR * (cXD * κ) = (cXD * cXD⁻¹) * (cXR * cXR⁻¹) := by rw [hκ]; ring
        _ ≤ 1 := by rw [iXD, iXR, mul_one]
    have hs := (hidden_itsr Tg g U κ).search_le hw (fun _ ↦ M)
      (fun τ ↦ mix Tg g (fun k ↦ (τ k).1)) (fun v ↦ v)
      (by
        intro τ k h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hk : k ∈ Tg
        · exact (h (by simp [mix, hk])).elim
        · refine ⟨hk, fun hin ↦ h ?_⟩
          simp [mix, hk, resU, hin])
      (fun _ ↦ out)
    have hp : pMark U = (C.card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ := by
      simp [pMark, hUdef]
    rw [hp] at hs
    refine le_trans (le_of_eq ?_) hs
    have e' := sum_fst_comp (X := X) (A := D) (B := Res D)
      (fun H ↦ κ * M.prob (mix Tg g H)
        (fun l ↦ out l ∈ univ.filter fun k ↦ k ∉ Tg ∧ H k ∉ U.1))
    refine Eq.trans ?_ e'.symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    have hev : (fun l ↦ out l ∉ Tg ∧ mix Tg g H (out l) ∈ C) =
        fun l ↦ out l ∈ univ.filter fun k ↦ k ∉ Tg ∧ H k ∉ U.1 := by
      funext l
      by_cases h : out l ∈ Tg <;> simp [mix, h, hUdef]
    rw [hev]
    calc cXD⁻¹ * M.prob (mix Tg g H) (fun l ↦ out l ∈ univ.filter fun k ↦ k ∉ Tg ∧ H k ∉ U.1)
        = (cXR * cXR⁻¹) * (cXD⁻¹ * M.prob (mix Tg g H)
            (fun l ↦ out l ∈ univ.filter fun k ↦ k ∉ Tg ∧ H k ∉ U.1)) := by rw [iXR, one_mul]
      _ = _ := by rw [hκ]; ring
  · -- everything is covered: the bound is at least one
    have hC : C = univ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hU
      exact (Finset.compl_eq_empty_iff _).1 hU
    have h1 : (1 : ℝ≥0∞) ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((C.card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
      rw [hC, Finset.card_univ, natCast_mul_inv_cancel Fintype.card_ne_zero, mul_one]
      exact one_le_two_mul_add_one_sq q
    refine le_trans ?_ h1
    calc ∑ H : X → D, cXD⁻¹ * M.prob (mix Tg g H) (fun l ↦ out l ∉ Tg ∧ mix Tg g H (out l) ∈ C)
        ≤ ∑ _H : X → D, cXD⁻¹ * 1 := by
          gcongr with H _
          exact prob_le_one_of_sub M out (fun H' T ↦ M.prob_sub H' out T) _ _
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcXD]
          exact natCast_mul_inv_cancel hXD

/-- **Core bound.**  `H ← (X → D)` uniform; `Tg` a fixed set of target points; `cov H` a set of
"covered" values depending on `H` only through its values on `Tg`.  A `q`-query algorithm outputs
a non-target point whose value is covered with probability at most `(2q+1)²` times the
probability that a fresh uniform value is covered. -/
theorem itsr_fixed_le [Nonempty D] (Tg : Finset X) (cov : (X → D) → Finset D)
    (hcov : ∀ H H' : X → D, (∀ k ∈ Tg, H k = H' k) → cov H = cov H')
    (M : HybridModel X D Leaf q) (out : Leaf → X) :
    ∑ H : X → D, (Fintype.card (X → D) : ℝ≥0∞)⁻¹ *
        M.prob H (fun l ↦ out l ∉ Tg ∧ H (out l) ∈ cov H) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ∑ H : X → D, (Fintype.card (X → D) : ℝ≥0∞)⁻¹ *
          (((cov H).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
  have hXD : Fintype.card (X → D) ≠ 0 := Fintype.card_ne_zero
  set cXD : ℝ≥0∞ := (Fintype.card (X → D) : ℝ≥0∞) with hcXD
  have iXD : cXD⁻¹ * cXD = 1 := by rw [mul_comm]; exact natCast_mul_inv_cancel hXD
  have hmix : ∀ F : (X → D) → ℝ≥0∞,
      ∑ H : X → D, F H = ∑ g : X → D, cXD⁻¹ * ∑ H : X → D, F (mix Tg g H) := by
    intro F
    rw [← Finset.mul_sum, sum_mix, ← mul_assoc, iXD, one_mul]
  have hcg : ∀ g H : X → D, cov (mix Tg g H) = cov g := fun g H ↦
    hcov _ _ fun k hk ↦ by simp [mix, hk]
  rw [hmix]
  calc ∑ g : X → D, cXD⁻¹ * ∑ H : X → D, cXD⁻¹ *
          M.prob (mix Tg g H) (fun l ↦ out l ∉ Tg ∧ mix Tg g H (out l) ∈ cov (mix Tg g H))
      ≤ ∑ g : X → D, cXD⁻¹ * ((2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (((cov g).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹)) := by
        gcongr with g _
        simp only [hcg]
        exact itsr_slice_le Tg g (cov g) M out
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ ↦ by ring

end Core

section Marginal

variable {ι X D : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X] [Fintype D]

/-- Overwrite `H` at the points `pts i` with the values `d i`. -/
noncomputable def put (pts : ι → X) (d : ι → D) (H : X → D) : X → D := fun x ↦
  if h : ∃ i, pts i = x then d (Classical.choose h) else H x

/-- The values of a uniform function at distinct points are independent and uniform
(unnormalised form). -/
theorem sum_comp_injective (pts : ι → X) (hinj : Function.Injective pts)
    (f : (ι → D) → ℝ≥0∞) :
    (Fintype.card (ι → D) : ℝ≥0∞) * ∑ H : X → D, f (fun i ↦ H (pts i)) =
      (Fintype.card (X → D) : ℝ≥0∞) * ∑ d : ι → D, f d := by
  have hinv : Function.Involutive
      (fun v : (ι → D) × (X → D) ↦ ((fun i ↦ v.2 (pts i)), put pts v.1 v.2)) := by
    rintro ⟨d, H⟩
    refine Prod.ext (funext fun i ↦ ?_) (funext fun x ↦ ?_)
    · have h : ∃ j, pts j = pts i := ⟨i, rfl⟩
      simp only [put, h, ↓reduceDIte]
      rw [hinj (Classical.choose_spec h)]
    · by_cases h : ∃ i, pts i = x
      · simp only [put, h, ↓reduceDIte]
        rw [Classical.choose_spec h]
      · simp only [put, h, ↓reduceDIte]
  have h := Equiv.sum_comp hinv.toPerm (fun v : (ι → D) × (X → D) ↦ f v.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  simp only [Function.Involutive.coe_toPerm] at h
  simpa [Finset.mul_sum] using h

/-- The values of a uniform function at distinct points are independent and uniform. -/
theorem sum_comp_injective' [Nonempty D] (pts : ι → X) (hinj : Function.Injective pts)
    (f : (ι → D) → ℝ≥0∞) :
    ∑ H : X → D, (Fintype.card (X → D) : ℝ≥0∞)⁻¹ * f (fun i ↦ H (pts i)) =
      ∑ d : ι → D, (Fintype.card (ι → D) : ℝ≥0∞)⁻¹ * f d := by
  have h := sum_comp_injective pts hinj f
  set a : ℝ≥0∞ := (Fintype.card (ι → D) : ℝ≥0∞) with ha
  set b : ℝ≥0∞ := (Fintype.card (X → D) : ℝ≥0∞) with hb
  have ia : a⁻¹ * a = 1 := by
    rw [mul_comm]; exact natCast_mul_inv_cancel Fintype.card_ne_zero
  have ib : b⁻¹ * b = 1 := by
    rw [mul_comm]; exact natCast_mul_inv_cancel Fintype.card_ne_zero
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  calc b⁻¹ * ∑ H : X → D, f (fun i ↦ H (pts i))
      = b⁻¹ * (a⁻¹ * a * ∑ H : X → D, f (fun i ↦ H (pts i))) := by rw [ia, one_mul]
    _ = b⁻¹ * (a⁻¹ * (b * ∑ d : ι → D, f d)) := by rw [mul_assoc, h]
    _ = (b⁻¹ * b) * (a⁻¹ * ∑ d : ι → D, f d) := by ring
    _ = _ := by rw [ib, one_mul]

/-- Two given coordinates of a uniform tuple collide with probability `1/|K|` (unnormalised). -/
theorem sum_collide {K : Type} [Fintype K] [DecidableEq K] (i j : ι)
    (hij : i ≠ j) :
    ∑ Rs : ι → K, (if Rs i = Rs j then (1 : ℝ≥0∞) else 0) =
      (Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (ι → K) : ℝ≥0∞) := by
  have hL : ∀ Rs : ι → K, (if Rs i = Rs j then (1 : ℝ≥0∞) else 0) =
      ∑ k : K, (if Rs i = k then (1 : ℝ≥0∞) else 0) * (if Rs j = k then (1 : ℝ≥0∞) else 0) := by
    intro Rs
    rw [Finset.sum_eq_single (Rs i)]
    · simp [eq_comm]
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : ∀ Rs : ι → K, ∑ k : K, (Fintype.card K : ℝ≥0∞)⁻¹ *
      (if Rs j = k then (1 : ℝ≥0∞) else 0) = (Fintype.card K : ℝ≥0∞)⁻¹ := by
    intro Rs
    simp
  calc ∑ Rs : ι → K, (if Rs i = Rs j then (1 : ℝ≥0∞) else 0)
      = ∑ k : K, ∑ Rs : ι → K,
          (if Rs i = k then (1 : ℝ≥0∞) else 0) * (if Rs j = k then (1 : ℝ≥0∞) else 0) :=
        (Finset.sum_congr rfl fun Rs _ ↦ hL Rs).trans Finset.sum_comm
    _ = ∑ k : K, ∑ Rs : ι → K,
          (Fintype.card K : ℝ≥0∞)⁻¹ * (if Rs j = k then (1 : ℝ≥0∞) else 0) :=
        Finset.sum_congr rfl fun k _ ↦
          sum_coord_change i (fun _ : K ↦ ()) (fun _ : K ↦ ())
            (fun r ↦ if r = k then (1 : ℝ≥0∞) else 0) (fun _ ↦ (Fintype.card K : ℝ≥0∞)⁻¹)
            (by
              intro z
              have : Nonempty K := ⟨k⟩
              simp only [Finset.filter_true_of_mem, Finset.mem_univ, implies_true,
                Finset.sum_ite_eq', ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              exact (natCast_mul_inv_cancel Fintype.card_ne_zero).symm)
            (fun _ Rs ↦ if Rs j = k then (1 : ℝ≥0∞) else 0)
            (by intro _ Rs t; simp [Function.update_of_ne (Ne.symm hij)])
    _ = ∑ Rs : ι → K, (Fintype.card K : ℝ≥0∞)⁻¹ :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun Rs _ ↦ hR Rs)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Marginal

section Game

variable {K Xm D ι : Type} [Fintype K] [DecidableEq K] [Fintype Xm] [DecidableEq Xm]
  [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]
variable {Leaf : Type} {q : ℕ}

/-- The target points `(Rs i, xs i)`. -/
def itsrTargets (xs : ι → Xm) (Rs : ι → K) : Finset (K × Xm) := univ.image fun i ↦ (Rs i, xs i)

/-- The digests of the target points. -/
def itsrDigests (xs : ι → Xm) (Rs : ι → K) (H : K × Xm → D) : Finset D :=
  univ.image fun i ↦ H (Rs i, xs i)

/-- The digests covered by the set `S`. -/
def covered (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)] (S : Finset D) : Finset D :=
  univ.filter (Cov S)

/-- The probability, in the non-adaptive ITSR game (`H` uniform, `Rs` uniform), that a fresh
uniform digest is covered by the target digests. -/
noncomputable def itsrCoverProb (K : Type) [Fintype K] [DecidableEq K]
    (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)] (xs : ι → Xm) : ℝ≥0∞ :=
  ∑ H : K × Xm → D, ∑ Rs : ι → K,
    ((Fintype.card (K × Xm → D) : ℝ≥0∞)⁻¹ * (Fintype.card (ι → K) : ℝ≥0∞)⁻¹) *
      (((covered Cov (itsrDigests xs Rs H)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹)

/-- The probability that a fresh uniform digest is covered by `|ι|` independent uniform
digests. -/
noncomputable def coverProb (ι : Type) [Fintype ι] [DecidableEq ι]
    (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)] : ℝ≥0∞ :=
  ∑ d : ι → D, (Fintype.card (ι → D) : ℝ≥0∞)⁻¹ *
    (((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹)

/-- **Non-adaptive ITSR for a random function (HybridModel level).**  Fixed target inputs
`xs : ι → Xm`; `H ← (K × Xm → D)` uniform; randomizers `Rs ← (ι → K)` uniform, given to the
`q`-query algorithm `M Rs`, which has quantum access to `H` and outputs `(R*, x*) = out Rs l`.
It wins iff `(R*, x*)` is not a target point `(Rs i, xs i)` and its digest is covered by the
target digests.  The winning probability is at most `(2q+1)²` times the probability
`itsrCoverProb` that a fresh uniform digest is covered by the target digests of this game. -/
theorem itsr_nonadaptive_le [Nonempty D] (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (xs : ι → Xm) (M : (ι → K) → HybridModel (K × Xm) D Leaf q)
    (out : (ι → K) → Leaf → K × Xm) :
    ∑ H : K × Xm → D, ∑ Rs : ι → K,
        ((Fintype.card (K × Xm → D) : ℝ≥0∞)⁻¹ * (Fintype.card (ι → K) : ℝ≥0∞)⁻¹) *
          (M Rs).prob H (fun l ↦ out Rs l ∉ itsrTargets xs Rs ∧
            Cov (itsrDigests xs Rs H) (H (out Rs l))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * itsrCoverProb K Cov xs := by
  have hev : ∀ (Rs : ι → K) (H : K × Xm → D),
      (fun l ↦ out Rs l ∉ itsrTargets xs Rs ∧ Cov (itsrDigests xs Rs H) (H (out Rs l))) =
        fun l ↦ out Rs l ∉ itsrTargets xs Rs ∧
          H (out Rs l) ∈ covered Cov (itsrDigests xs Rs H) := by
    intro Rs H
    funext l
    simp [covered]
  simp only [hev]
  unfold itsrCoverProb
  rw [Finset.sum_comm, Finset.sum_comm (γ := K × Xm → D), Finset.mul_sum]
  refine Finset.sum_le_sum fun Rs _ ↦ ?_
  have h := itsr_fixed_le (itsrTargets xs Rs) (fun H ↦ covered Cov (itsrDigests xs Rs H))
    (by
      intro H H' hH
      have : itsrDigests xs Rs H = itsrDigests xs Rs H' :=
        Finset.image_congr fun i _ ↦ hH _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      simp only [this])
    (M Rs) (out Rs)
  calc ∑ H : K × Xm → D,
        ((Fintype.card (K × Xm → D) : ℝ≥0∞)⁻¹ * (Fintype.card (ι → K) : ℝ≥0∞)⁻¹) *
          (M Rs).prob H (fun l ↦ out Rs l ∉ itsrTargets xs Rs ∧
            H (out Rs l) ∈ covered Cov (itsrDigests xs Rs H))
      = (Fintype.card (ι → K) : ℝ≥0∞)⁻¹ * ∑ H : K × Xm → D,
          (Fintype.card (K × Xm → D) : ℝ≥0∞)⁻¹ *
            (M Rs).prob H (fun l ↦ out Rs l ∉ itsrTargets xs Rs ∧
              H (out Rs l) ∈ covered Cov (itsrDigests xs Rs H)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun H _ ↦ by ring
    _ ≤ (Fintype.card (ι → K) : ℝ≥0∞)⁻¹ * _ := mul_le_mul' le_rfl h
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun H _ ↦ by ring

/-- The covering probability of the game is at most that of independent uniform digests, up to
the probability `≤ |ι|² / |K|` that two randomizers collide. -/
theorem itsrCoverProb_le [Nonempty D] (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (xs : ι → Xm) :
    itsrCoverProb K Cov xs ≤
      coverProb ι Cov + (Fintype.card ι : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞) := by
  let f : (ι → D) → ℝ≥0∞ := fun d ↦
    ((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹
  have hf : ∀ d, f d ≤ 1 := by
    intro d
    calc f d ≤ (Fintype.card D : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ :=
          mul_le_mul' (by exact_mod_cast Finset.card_le_univ _) le_rfl
      _ = 1 := natCast_mul_inv_cancel Fintype.card_ne_zero
  let col : (ι → K) → ℝ≥0∞ := fun Rs ↦
    ∑ i : ι, ∑ j : ι, if i ≠ j ∧ Rs i = Rs j then (1 : ℝ≥0∞) else 0
  set cH : ℝ≥0∞ := (Fintype.card (K × Xm → D) : ℝ≥0∞) with hcH
  set cRs : ℝ≥0∞ := (Fintype.card (ι → K) : ℝ≥0∞) with hcRs
  set cK : ℝ≥0∞ := (Fintype.card K : ℝ≥0∞) with hcK
  have iH : cH * cH⁻¹ = 1 := natCast_mul_inv_cancel Fintype.card_ne_zero
  have iRs : cRs * cRs⁻¹ ≤ 1 := natCast_mul_inv_le_one _
  have hA : ∀ Rs : ι → K, ∑ H : K × Xm → D, cH⁻¹ * f (fun i ↦ H (Rs i, xs i)) ≤
      coverProb ι Cov + col Rs := by
    intro Rs
    by_cases hinj : Function.Injective Rs
    · have hinj' : Function.Injective (fun i ↦ (Rs i, xs i)) := fun a b h ↦
        hinj (congrArg Prod.fst h)
      exact le_trans (le_of_eq (sum_comp_injective' (fun i ↦ (Rs i, xs i)) hinj' f)) le_self_add
    · obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.1 hinj
      refine le_trans ?_ le_add_self
      calc ∑ H : K × Xm → D, cH⁻¹ * f (fun i ↦ H (Rs i, xs i))
          ≤ ∑ _H : K × Xm → D, cH⁻¹ * 1 := by
            gcongr with H _
            exact hf _
        _ = 1 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcH]
            exact iH
        _ = (if i ≠ j ∧ Rs i = Rs j then (1 : ℝ≥0∞) else 0) := by simp [hne, heq]
        _ ≤ ∑ j' : ι, (if i ≠ j' ∧ Rs i = Rs j' then (1 : ℝ≥0∞) else 0) :=
            Finset.single_le_sum (f := fun j' ↦ if i ≠ j' ∧ Rs i = Rs j' then (1 : ℝ≥0∞) else 0)
              (fun _ _ ↦ zero_le) (Finset.mem_univ j)
        _ ≤ col Rs :=
            Finset.single_le_sum
              (f := fun i' ↦ ∑ j' : ι, if i' ≠ j' ∧ Rs i' = Rs j' then (1 : ℝ≥0∞) else 0)
              (fun _ _ ↦ zero_le) (Finset.mem_univ i)
  have hpair : ∀ i j : ι, ∑ Rs : ι → K, (if i ≠ j ∧ Rs i = Rs j then (1 : ℝ≥0∞) else 0) ≤
      cK⁻¹ * cRs := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp only [ne_eq, hij, not_false_eq_true, true_and]
      exact le_of_eq (sum_collide i j hij)
  have hcol : ∑ Rs : ι → K, cRs⁻¹ * col Rs ≤ (Fintype.card ι : ℝ≥0∞) ^ 2 / cK := by
    calc ∑ Rs : ι → K, cRs⁻¹ * col Rs
        = cRs⁻¹ * ∑ i : ι, ∑ j : ι, ∑ Rs : ι → K,
            (if i ≠ j ∧ Rs i = Rs j then (1 : ℝ≥0∞) else 0) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm)
      _ ≤ cRs⁻¹ * ∑ _i : ι, ∑ _j : ι, cK⁻¹ * cRs := by
          gcongr with i _ j _
          exact hpair i j
      _ = (cRs * cRs⁻¹) * ((Fintype.card ι : ℝ≥0∞) ^ 2 * cK⁻¹) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ 1 * ((Fintype.card ι : ℝ≥0∞) ^ 2 * cK⁻¹) := by gcongr
      _ = _ := by rw [one_mul, div_eq_mul_inv]
  calc itsrCoverProb K Cov xs
      = ∑ Rs : ι → K, cRs⁻¹ * ∑ H : K × Xm → D, cH⁻¹ * f (fun i ↦ H (Rs i, xs i)) := by
        unfold itsrCoverProb
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun Rs _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun H _ ↦ ?_
        simp only [f, itsrDigests]
        ring
    _ ≤ ∑ Rs : ι → K, cRs⁻¹ * (coverProb ι Cov + col Rs) := by
        gcongr with Rs _
        exact hA Rs
    _ = (cRs * cRs⁻¹) * coverProb ι Cov + ∑ Rs : ι → K, cRs⁻¹ * col Rs := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hcRs]
        ring
    _ ≤ 1 * coverProb ι Cov + (Fintype.card ι : ℝ≥0∞) ^ 2 / cK := by gcongr
    _ = _ := by rw [one_mul]

/-- **Non-adaptive ITSR for a random function, independent-digest form.**  As
`itsr_nonadaptive_le`, with the bound `(2q+1)² (coverProb + |ι|² / |K|)`: `coverProb` is the
probability that a fresh uniform digest is covered by `|ι|` independent uniform digests, and
`|ι|² / |K|` bounds the probability that two of the `|ι|` randomizers collide. -/
theorem itsr_nonadaptive_le' [Nonempty D] (Cov : Finset D → D → Prop)
    [∀ S, DecidablePred (Cov S)] (xs : ι → Xm) (M : (ι → K) → HybridModel (K × Xm) D Leaf q)
    (out : (ι → K) → Leaf → K × Xm) :
    ∑ H : K × Xm → D, ∑ Rs : ι → K,
        ((Fintype.card (K × Xm → D) : ℝ≥0∞)⁻¹ * (Fintype.card (ι → K) : ℝ≥0∞)⁻¹) *
          (M Rs).prob H (fun l ↦ out Rs l ∉ itsrTargets xs Rs ∧
            Cov (itsrDigests xs Rs H) (H (out Rs l))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        (coverProb ι Cov + (Fintype.card ι : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) :=
  (itsr_nonadaptive_le Cov xs M out).trans (mul_le_mul' le_rfl (itsrCoverProb_le Cov xs))

end Game

section Programs

open Quantum

variable {K Xm D ι : Type} [Fintype K] [DecidableEq K] [Fintype Xm] [DecidableEq Xm]
  [Fintype D] [DecidableEq D] [AddCommGroup D] [Fintype ι] [DecidableEq ι]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Non-adaptive ITSR for a random function, for quantum query programs.**  Fixed target inputs
`xs`; `H ← (K × Xm → D)` uniform; randomizers `Rs ← (ι → K)` uniform; the program `x Rs` (any
VCVio quantum query program with at most `q` oracle calls on every path) runs with quantum access
to `H`; `out Rs` decodes its leaf to `(R*, x*)`; it wins iff `(R*, x*)` is not a target point and
its digest is covered by the target digests.  Bound `(2q+1)² (coverProb + |ι|² / |K|)`. -/
theorem itsr_nonadaptive_program_le (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (xs : ι → Xm) (I : L.Interp) (x : (ι → K) → QuantumComp L (qromSpec (K × Xm) D) W A)
    (ρ : (ι → K) → SubState A) (q : ℕ) (hx : ∀ Rs, QueryBounded (x Rs) q)
    (out : (ι → K) → (Σ u, W u) → K × Xm) :
    ∑ H : K × Xm → D, ∑ Rs : ι → K,
        ((Fintype.card (K × Xm → D) : ℝ≥0∞)⁻¹ * (Fintype.card (ι → K) : ℝ≥0∞)⁻¹) *
          qprob I H (x Rs) (ρ Rs) (fun p ↦ out Rs p ∉ itsrTargets xs Rs ∧
            Cov (itsrDigests xs Rs H) (H (out Rs p))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        (coverProb ι Cov + (Fintype.card ι : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) :=
  itsr_nonadaptive_le' Cov xs
    (fun Rs ↦ HybridModel.ofProgram I (x Rs) (ρ Rs) q (hx Rs) (out Rs)) (fun _ ↦ id)

/-- The same with the exact covering probability of the game. -/
theorem itsr_nonadaptive_program_le_exact (Cov : Finset D → D → Prop)
    [∀ S, DecidablePred (Cov S)]
    (xs : ι → Xm) (I : L.Interp) (x : (ι → K) → QuantumComp L (qromSpec (K × Xm) D) W A)
    (ρ : (ι → K) → SubState A) (q : ℕ) (hx : ∀ Rs, QueryBounded (x Rs) q)
    (out : (ι → K) → (Σ u, W u) → K × Xm) :
    ∑ H : K × Xm → D, ∑ Rs : ι → K,
        ((Fintype.card (K × Xm → D) : ℝ≥0∞)⁻¹ * (Fintype.card (ι → K) : ℝ≥0∞)⁻¹) *
          qprob I H (x Rs) (ρ Rs) (fun p ↦ out Rs p ∉ itsrTargets xs Rs ∧
            Cov (itsrDigests xs Rs H) (H (out Rs p))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * itsrCoverProb K Cov xs :=
  itsr_nonadaptive_le Cov xs
    (fun Rs ↦ HybridModel.ofProgram I (x Rs) (ρ Rs) q (hx Rs) (out Rs)) (fun _ ↦ id)

end Programs

end PQ.QROM

#print axioms PQ.QROM.itsr_fixed_le
#print axioms PQ.QROM.itsr_nonadaptive_le
#print axioms PQ.QROM.itsrCoverProb_le
#print axioms PQ.QROM.itsr_nonadaptive_le'
#print axioms PQ.QROM.itsr_nonadaptive_program_le
#print axioms PQ.QROM.itsr_nonadaptive_program_le_exact
