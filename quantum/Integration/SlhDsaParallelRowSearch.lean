import Integration.SlhDsaShakePermutationColumnGame

/-! Parallel quantum query depth for distinguishing a change on a hidden row.
One layer can query `width` inputs in superposition on separate response
registers. The program can perform arbitrary local operations between layers.
The bound measures oracle rounds, including parallel and entangled inputs. -/

namespace Reduction.ParallelRowSearch

open Classical Quantum PQ.Interactive PQ.QROM ENNReal
open scoped Kronecker ComplexOrder

variable {K X Y E : Type}

/-- Simultaneous evaluation of one shared table on the coordinates of a batch. -/
def batch (width : ℕ) (H : X → Y) (x : Fin width → X) : Fin width → Y := H ∘ x

/-- Each lane experiences exactly its usual oracle permutation. The equality
holds on the entire computational basis of the parallel oracle unitary. -/
theorem batch_lane [AddCommGroup Y] (width : ℕ) (H : X → Y) (x : Fin width → X) (y : Fin width → Y)
    (j : Fin width) :
    (((oracleEquiv (batch width H)) (x,y)).1 j, ((oracleEquiv (batch width H)) (x,y)).2 j) =
      oracleEquiv H (x j, y j) := rfl

variable [Fintype K] [Nonempty K] [DecidableEq K] [Fintype X] [Nonempty X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype E] [DecidableEq E]

/-- Average distinguishing advantage is at most `8 * depth² * width / |K|`
when the two tables agree off a uniform hidden row. -/
theorem distinguishing (width depth : ℕ) (G : X → Y) (row : X → K)
    (H : K → X → Y) (outside : ∀ k x, row x ≠ k → H k x = G x)
    (M : ((Fin width → X) → (Fin width → Y)) →
      Closed (WS (Fin width → X) (Fin width → Y) E) Bool)
    (rounds : PUE (spec := unifSpec) cnt0 M depth)
    (ρ : SubState (((Fin width → X) × (Fin width → Y)) × E)) :
    let accept := fun h => qWeight (· = true) (M (batch width h))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    SetOracle.uniformMean (fun k => accept (H k)) ≤ accept G +
      ENNReal.ofReal (8*(depth:ℝ)^2*((width:ℝ)/Fintype.card K)) := by
  classical
  let keys (x : Fin width → X) := Finset.univ.image (row ∘ x)
  have card (x) : (keys x).card ≤ width :=
    (Finset.card_image_le).trans_eq (by simp)
  apply ShakePermutation.Program.bounded_overlap_game (batch width G)
    (fun k => batch width (H k)) keys width card _ M depth rounds ρ
  intro k x absent
  funext j
  apply outside
  intro eq
  exact absent (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, eq⟩)

/-- If the acceptance probabilities in the two experiments differ by at
least one half in favor of the modified table, the product of query depth and the
number of query slots (width times depth) is at least `|K| / 16`. -/
theorem depth_times_slots (width depth : ℕ) (G : X → Y) (row : X → K)
    (H : K → X → Y) (outside : ∀ k x, row x ≠ k → H k x = G x)
    (M : ((Fin width → X) → (Fin width → Y)) →
      Closed (WS (Fin width → X) (Fin width → Y) E) Bool)
    (rounds : PUE (spec := unifSpec) cnt0 M depth)
    (ρ : SubState (((Fin width → X) × (Fin width → Y)) × E)) :
    let accept := fun h => qWeight (· = true) (M (batch width h))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    accept G + 1/2 ≤ SetOracle.uniformMean (fun k => accept (H k)) →
      Fintype.card K ≤ 16 * depth * (width*depth) := by
  intro accept succeeds
  have bound := distinguishing width depth G row H outside M rounds ρ
  change _ ≤ accept G + _ at bound
  have finite : accept G ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (qWeight_le_trace _ _
      (ρ.posSemidef.kronecker (SubState.basis ()).posSemidef))
  have gap := (ENNReal.add_le_add_iff_left finite).mp (succeeds.trans bound)
  have le := (ENNReal.toReal_le_toReal (by norm_num) ENNReal.ofReal_ne_top).2 gap
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, ← mul_div_assoc, le_div_iff₀ (by positivity)] at le
  exact_mod_cast (show (Fintype.card K : ℝ) ≤ 16*(depth:ℝ)*((width:ℝ)*depth) by nlinarith)

end Reduction.ParallelRowSearch

#print axioms Reduction.ParallelRowSearch.batch_lane
#print axioms Reduction.ParallelRowSearch.distinguishing
#print axioms Reduction.ParallelRowSearch.depth_times_slots
