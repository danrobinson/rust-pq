import PQ.QROM.Interface

/-!
# Pulling a hybrid model back along a local map of oracles

`HybridModel X Y Leaf q` (`PQ/QROM/Interface.lean`) is the abstract interface of a `q`-query
algorithm on which the leaf-level Part-2 bounds are proved.  If the oracle the algorithm really
queries is `φ H : X → Y`, built from a function `H : X' → Y'` LOCALLY — `φ H x` depends on `H`
only at the point `x'` with `ι x' = x`, for an embedding `ι : X' ↪ X` — then the algorithm is a
hybrid model for `H` as well (`HybridModel.pullback`): same probabilities, masses read at `ι k`.

This is the structured-oracle form of every bound stated for a `HybridModel`: e.g. `H` one hash
component (or one seed-keyed row family) and `φ H` the port function presenting all components.
-/

open ENNReal

namespace PQ.QROM

variable {X Y X' Y' Leaf : Type} [Fintype X] [DecidableEq X] [DecidableEq Y] [Fintype X']
  [DecidableEq X'] [DecidableEq Y'] {q : ℕ}

theorem pullback_sum_le (M : HybridModel X Y Leaf q) (ι : X' ↪ X) (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x') (H G : X' → Y') :
    ∑ k ∈ Finset.univ.filter (fun k ↦ φ H k ≠ φ G k), M.mass (φ G) k ≤
      ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k), M.mass (φ G) (ι k) := by
  rw [← Finset.sum_map (Finset.univ.filter fun k ↦ H k ≠ G k) ι fun k ↦ M.mass (φ G) k]
  refine Finset.sum_le_sum_of_subset fun x hx ↦ ?_
  obtain ⟨x', rfl, hne⟩ := hφ H G x (Finset.mem_filter.1 hx).2
  exact Finset.mem_map_of_mem ι (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)

/-- **Pullback of a hybrid model along a local map of oracles.** -/
noncomputable def HybridModel.pullback (M : HybridModel X Y Leaf q) (ι : X' ↪ X)
    (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x') : HybridModel X' Y' Leaf q where
  prob H E := M.prob (φ H) E
  mass G k := M.mass (φ G) (ι k)
  prob_mono H _ _ h := M.prob_mono (φ H) h
  prob_sum_le H out := by
    have e : ∀ k : X', (fun p ↦ out p = k) = fun p ↦ ι (out p) = ι k := fun k ↦ by
      funext p
      exact propext ι.injective.eq_iff.symm
    calc ∑ k, M.prob (φ H) (fun p ↦ out p = k)
        = ∑ k, M.prob (φ H) (fun p ↦ ι (out p) = ι k) := by simp only [e]
      _ = ∑ k ∈ Finset.univ.map ι, M.prob (φ H) (fun p ↦ ι (out p) = k) :=
          (Finset.sum_map _ ι fun k ↦ M.prob (φ H) (fun p ↦ ι (out p) = k)).symm
      _ ≤ ∑ k, M.prob (φ H) (fun p ↦ ι (out p) = k) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 1 := M.prob_sum_le (φ H) fun p ↦ ι (out p)
  prob_sub H out T := by
    have e : ∀ k : X', (fun p ↦ out p = k) = fun p ↦ ι (out p) = ι k := fun k ↦ by
      funext p
      exact propext ι.injective.eq_iff.symm
    calc M.prob (φ H) (fun p ↦ out p ∈ T)
        ≤ M.prob (φ H) (fun p ↦ ι (out p) ∈ T.map ι) :=
          M.prob_mono _ fun p h ↦ Finset.mem_map_of_mem ι h
      _ ≤ ∑ k ∈ T.map ι, M.prob (φ H) (fun p ↦ ι (out p) = k) := M.prob_sub _ _ _
      _ = ∑ k ∈ T, M.prob (φ H) (fun p ↦ ι (out p) = ι k) :=
          Finset.sum_map _ ι fun k ↦ M.prob (φ H) (fun p ↦ ι (out p) = k)
      _ = ∑ k ∈ T, M.prob (φ H) (fun p ↦ out p = k) := by simp only [e]
  mass_sum_le G :=
    calc ∑ k, M.mass (φ G) (ι k) = ∑ k ∈ Finset.univ.map ι, M.mass (φ G) k :=
          (Finset.sum_map _ ι fun k ↦ M.mass (φ G) k).symm
      _ ≤ ∑ k, M.mass (φ G) k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ q := M.mass_sum_le _
  hybrid H G E := (M.hybrid (φ H) (φ G) E).trans (add_le_add le_rfl
    (ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (pullback_sum_le M ι φ hφ H G)) (by norm_num)))
  hybrid' H G E := (M.hybrid' (φ H) (φ G) E).trans (add_le_add le_rfl
    (ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (pullback_sum_le M ι φ hφ H G)) (by norm_num)))

@[simp] theorem HybridModel.pullback_prob (M : HybridModel X Y Leaf q) (ι : X' ↪ X)
    (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x') (H : X' → Y')
    (E : Leaf → Prop) : (M.pullback ι φ hφ).prob H E = M.prob (φ H) E := rfl

end PQ.QROM

#print axioms PQ.QROM.HybridModel.pullback
