import PQ.QROM.ExactDsprTightGame
import PQ.QROM.HybridPullback

/-!
# Pulling the tight DSPR hypotheses back along a local map of oracles

`HybridModel.pullback` (`PQ/QROM/HybridPullback.lean`) turns a model whose oracle is `φ H`,
built LOCALLY from `H : X' → Y'` along an embedding `ι : X' ↪ X`, into a model for `H`.  The tight
DSPR lemma `dspr_embedded_tight` needs two more properties of the model, both statements about
its probability functional only:

* `HybridModel.Additive.pullback`: additivity is preserved (same probabilities);
* `Rows.RowsBound.pullback`: the target-count-free rows bound is preserved.  Proof: extend the
  mark probabilities by `0`, the rows by a constant and the two functions by `φ`; a mark pattern
  of positive weight vanishes off the range of `ι`, so the sums over patterns on `X` and on `X'`
  agree term by term (`sum_bw_extend`), and `φ` of the mixed function is the mixture of the
  `φ`-images (`hw_extend`).
-/

open ENNReal Finset

set_option linter.unusedSectionVars false

namespace PQ.QROM

open PQ.QROM.Rows

section

variable {X X' Y Y' Leaf : Type} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
  [DecidableEq Y] [DecidableEq Y'] {q : ℕ}

theorem HybridModel.Additive.pullback {M : HybridModel X Y Leaf q} (hM : M.Additive)
    (ι : X' ↪ X) (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x') :
    (M.pullback ι φ hφ).Additive := fun H E E' h ↦ hM (φ H) E E' h

/-- Locality on the range. -/
theorem fors_local_range (ι : X' ↪ X) (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x') (H G : X' → Y') (x' : X')
    (h : H x' = G x') : φ H (ι x') = φ G (ι x') := by
  by_contra hne
  obtain ⟨y, hy, hne'⟩ := hφ H G _ hne
  rw [ι.injective hy] at hne'
  exact hne' h

/-- Locality off the range. -/
theorem fors_local_off (ι : X' ↪ X) (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x') (H G : X' → Y') (z : X)
    (hz : ¬ ∃ x', ι x' = z) : φ H z = φ G z := by
  by_contra hne
  obtain ⟨y, hy, -⟩ := hφ H G _ hne
  exact hz ⟨y, hy⟩

/-- Extension of a mark pattern by `false`. -/
noncomputable def extB (ι : X' ↪ X) (s : X' → Bool) : X → Bool :=
  Function.extend ι s fun _ ↦ false

theorem extB_apply (ι : X' ↪ X) (s : X' → Bool) (x' : X') : extB ι s (ι x') = s x' :=
  ι.injective.extend_apply _ _ _

theorem extB_off (ι : X' ↪ X) (s : X' → Bool) (z : X) (hz : ¬ ∃ x', ι x' = z) :
    extB ι s z = false :=
  Function.extend_apply' _ _ _ hz

theorem extB_injective (ι : X' ↪ X) : Function.Injective (extB ι) := by
  intro s s' h
  funext x'
  rw [← extB_apply ι s x', ← extB_apply ι s' x', h]

/-- Extension of the mark probabilities by `0`. -/
noncomputable def extP (ι : X' ↪ X) (p : X' → ℝ) : X → ℝ := Function.extend ι p 0

theorem extP_apply (ι : X' ↪ X) (p : X' → ℝ) (x' : X') : extP ι p (ι x') = p x' :=
  ι.injective.extend_apply _ _ _

theorem extP_off (ι : X' ↪ X) (p : X' → ℝ) (z : X) (hz : ¬ ∃ x', ι x' = z) : extP ι p z = 0 :=
  Function.extend_apply' _ _ _ hz

/-- A product over `X` whose factors are `1` off the range of `ι`. -/
theorem prod_extend_one (ι : X' ↪ X) (g : X → ℝ) (hg : ∀ z, (¬ ∃ x', ι x' = z) → g z = 1) :
    ∏ z, g z = ∏ x', g (ι x') := by
  classical
  rw [← Finset.prod_map Finset.univ ι g]
  refine (Finset.prod_subset (Finset.subset_univ _) fun z _ hz ↦ hg z fun ⟨x', hx'⟩ ↦ hz ?_).symm
  rw [← hx']
  exact Finset.mem_map_of_mem ι (Finset.mem_univ _)

theorem bw_extB (ι : X' ↪ X) (p : X' → ℝ) (s : X' → Bool) :
    bw (extP ι p) (extB ι s) = bw p s := by
  unfold bw
  rw [prod_extend_one ι _ fun z hz ↦ by rw [extB_off ι s z hz, extP_off ι p z hz]; simp]
  simp only [extB_apply, extP_apply]

/-- **Sums over mark patterns**: with mark probability `0` off the range of `ι`, only patterns
extended by `false` carry weight. -/
theorem sum_bw_extend (ι : X' ↪ X) (p : X' → ℝ) (Φ : (X → Bool) → ℝ) :
    ∑ s : X → Bool, bw (extP ι p) s * Φ s = ∑ s' : X' → Bool, bw p s' * Φ (extB ι s') := by
  classical
  have hzero : ∀ s : X → Bool, s ∉ Finset.univ.image (extB ι) → bw (extP ι p) s * Φ s = 0 := by
    intro s hs
    have hex : ∃ z, (¬ ∃ x', ι x' = z) ∧ s z = true := by
      by_contra hn
      refine hs (Finset.mem_image.2 ⟨s ∘ ι, Finset.mem_univ _, funext fun z ↦ ?_⟩)
      by_cases hz : ∃ x', ι x' = z
      · obtain ⟨x', rfl⟩ := hz
        rw [extB_apply]
        rfl
      · rw [extB_off ι _ z hz]
        cases h : s z
        · rfl
        · exact absurd ⟨z, hz, h⟩ hn
    obtain ⟨z, hz, hsz⟩ := hex
    have : bw (extP ι p) s = 0 := by
      unfold bw
      refine Finset.prod_eq_zero (Finset.mem_univ z) ?_
      rw [hsz, if_pos rfl, extP_off ι p z hz]
    rw [this, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ _) fun s _ hs ↦ hzero s hs,
    Finset.sum_image fun a _ b _ h ↦ extB_injective ι h]
  simp only [bw_extB]

variable {J : Type} [Fintype J] [DecidableEq J]

/-- Extension of the rows by a constant. -/
noncomputable def extR (ι : X' ↪ X) (row : X' → J) (j₀ : J) : X → J :=
  Function.extend ι row fun _ ↦ j₀

theorem rowClean_extB (ι : X' ↪ X) (row : X' → J) (j₀ j : J) (s : X' → Bool) :
    rowClean (extR ι row j₀) j (extB ι s) ↔ rowClean row j s := by
  constructor
  · intro h x' hx'
    have := h (ι x') (by simp only [extR, ι.injective.extend_apply]; exact hx')
    rwa [extB_apply] at this
  · intro h z hz
    by_cases hr : ∃ x', ι x' = z
    · obtain ⟨x', rfl⟩ := hr
      rw [extB_apply]
      exact h x' (by simpa only [extR, ι.injective.extend_apply] using hz)
    · exact extB_off ι s z hr

theorem gam_extend (ι : X' ↪ X) (p : X' → ℝ) (row : X' → J) (j₀ j : J) :
    gam (extP ι p) (extR ι row j₀) j = gam p row j := by
  unfold gam
  rw [sum_bw_extend]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [rowClean_extB]

theorem hw_extend (ι : X' ↪ X) (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x') (G h : X' → Y')
    (s : X' → Bool) : Hw (φ G) (φ h) (extB ι s) = φ (Hw G h s) := by
  funext z
  unfold Hw
  by_cases hr : ∃ x', ι x' = z
  · obtain ⟨x', rfl⟩ := hr
    rw [extB_apply]
    by_cases hs : s x' = true
    · rw [if_pos hs]
      exact fors_local_range ι φ hφ _ _ x' (by simp [hs])
    · rw [if_neg hs]
      exact fors_local_range ι φ hφ _ _ x' (by simp [hs])
  · rw [extB_off ι s z hr]
    exact fors_local_off ι φ hφ _ _ z hr

/-- **The rows bound is preserved by the pullback along a local map of oracles.** -/
theorem RowsBound.pullback (ι : X' ↪ X) (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x')
    (f : (X → Y) → (Leaf → Prop) → ℝ) (hf : RowsBound f q) :
    RowsBound (fun H E ↦ f (φ H) E) q := by
  intro J _ _ p r row G h Ev hp0 hp1 hr hpr hdisj g hg0 hg
  classical
  by_cases hJ : IsEmpty J
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, Finset.sum_const_zero]
    positivity
  obtain ⟨j₀⟩ := not_isEmpty_iff.1 hJ
  have key := hf J (extP ι p) r (extR ι row j₀) (φ G) (φ h) Ev
    (fun z ↦ by
      by_cases hz : ∃ x', ι x' = z
      · obtain ⟨x', rfl⟩ := hz; rw [extP_apply]; exact hp0 x'
      · rw [extP_off ι p z hz])
    (fun z ↦ by
      by_cases hz : ∃ x', ι x' = z
      · obtain ⟨x', rfl⟩ := hz; rw [extP_apply]; exact hp1 x'
      · rw [extP_off ι p z hz]; exact zero_le_one)
    hr
    (fun z ↦ by
      by_cases hz : ∃ x', ι x' = z
      · obtain ⟨x', rfl⟩ := hz; rw [extP_apply]; exact hpr x'
      · rw [extP_off ι p z hz]; positivity)
    hdisj g hg0 (fun j hj ↦ by rw [gam_extend]; exact hg j hj)
  refine le_trans (le_of_eq ?_) key
  rw [sum_bw_extend]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hw_extend ι φ hφ G h s]
  simp only [rowClean_extB]

end

end PQ.QROM

#print axioms PQ.QROM.HybridModel.Additive.pullback
#print axioms PQ.QROM.RowsBound.pullback
