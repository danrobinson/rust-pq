import Integration.SlhDsaShakePermutationRelabelOracle
import Integration.SlhDsaShakePermutationExtensions
import Integration.SlhDsaShakePermutationRelabelUpdate
import Integration.SlhDsaShakePermutationRelabelSlice

namespace Reduction.ShakePermutation.Relabel
open Quantum Tails Classical
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local irreducible] Graph.intermediate Graph.reached Graph.support badRight
set_option linter.constructorNameAsVariable false
variable (π : Permutation) (k : Db) (m : Option Capacity → Db) {L : ℕ}

private noncomputable def one (z : Address L) (val : Rate) : Cells L := by
  classical exact fun i => if i = z then some val else none

private theorem swap_one (k' : Db) (z : Capacity) (p : Path L) (head val : Rate)
    (hit : chosen π k k' L z = some (p,head)) :
    swap π k k' L (one (.inl z) val) = one (.inr p) (rateXor val head) := by
  classical
  have eq : dest π k k' L (.inr p) = .inl z := by
    change (route π k k' L (.inr p)).1 = _
    simp [route,(mates π k k').mp hit]
  funext i
  rw [read_swap]
  by_cases atp : i = .inr p
  · subst i
    simp [eq,one,route,(mates π k k').mp hit,cellMap,twist]
  · have other : dest π k k' L i ≠ .inl z := fun e => atp ((dest π k k' L).injective (e.trans eq.symm))
    simp only [one,ite_eq_right other,ite_eq_right atp]
    cases (route π k k' L i).2 <;> rfl

/-- Coherent amplitude at the common one-path output of the right-mask
commutator.  Each input has one real h record and an empty path database. -/
theorem right_mask_coefficient (s : Finset Capacity) (z : Capacity → Capacity)
    (p : Path L) (head val : Rate)
    (hit : ∀ y ∈ s, chosen π k (m (some y)) L (z y) = some (p,head))
    (miss : mate π k (m none) p = none) :
    ∑ y ∈ s, cellAmp Capacity * RelabelSlice.coefficient
      (fun u => Function.Involutive.toPerm _ (swap_twice π k (m u) L))
      y (one (.inl (z y)) val) (one (.inr p) (rateXor val head)) =
      (s.card : ℂ) / Fintype.card Capacity := by
  classical
  apply RelabelSlice.coherent_coefficient
  · intro y hy
    exact swap_one π k _ _ _ _ _ (hit y hy)
  · intro y hy eq
    have e := congrFun eq (.inr p)
    change swap π k (m none) L _ (.inr p) = _ at e
    simp [swap,miss,one] at e

/-- A single recorded left mask suffices. All but at most 150 right
mask values route the corresponding real cell to the same one-block path. -/
theorem one_block_branches (hπ : ¬irregular π) (he : ¬Pairs.exceptional π)
    (r : Rate) (u : Capacity) :
    ∃ (s : Finset Capacity) (p : Path 1) (head : Rate) (z : Capacity → Capacity)
      (K : Db) (M : Option Capacity → Db),
      Fintype.card Capacity ≤ s.card + 150 ∧
      (∀ y ∈ s, Graph.Good (layout π) K (M (some y)) ∧
        chosen π K (M (some y)) 1 (z y) = some (p,head)) ∧ mate π K (M none) p = none := by
  classical
  let empty : Db := fun _ => none
  let K := Function.update empty r (some u)
  let a := (layout π).middle r (layout π).zero u
  let M (y : Option Capacity) := Function.update empty a.1 y
  let p : Path 1 := BList.ofList [r] (by simp)
  have tailNil {l z} (t : Graph.Tail (layout π) K empty l z) : l = [] ∧ z = (layout π).zero := by
    cases t with
    | root => exact ⟨rfl,rfl⟩
    | step _ _ h => contradiction
  have hu : K r = some u := Function.update_self ..
  have kr {r' v} (h : K r' = some v) : r' = r ∧ v = u := by
    by_cases e : r' = r
    · subst r'; exact ⟨rfl,(Option.some.inj (h.symm.trans hu))⟩
    · simp [K,Function.update_of_ne e,empty] at h
  have single {v} (hv : v ∈ Graph.intermediate (layout π) K empty) : v = a := by
    obtain ⟨z,hz,r',u',h,rfl⟩ := (Graph.mem_intermediate (layout π) K empty v).mp hv
    obtain ⟨l,t⟩ := (Graph.mem_reached (layout π) K empty z).mp hz
    obtain ⟨rfl,rfl⟩ := kr h
    rw [(tailNil t).2]
  have base : Graph.Good (layout π) K empty :=
    ⟨fun t t' => (tailNil t).1.trans (tailNil t').1.symm, fun _ h _ h' _ => (single h).trans (single h').symm⟩
  have size : Graph.support K ⊆ {r} := by
    intro r' h
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp ((Graph.mem_support ..).mp h)
    simpa only [Finset.mem_singleton] using (kr hv).1
  have bound := badRight_card π hπ he K empty base 1
    (by simpa only [Finset.card_singleton] using Finset.card_le_card size)
    (by simp [Graph.support,empty]) a.1
  let s := (badRight π K empty a.1)ᶜ
  refine ⟨s,p,a.1,fun y => (layout π).finish a.2 y,K,M,?_,?_,?_⟩
  · have card := Finset.card_compl_add_card (badRight π K empty a.1)
    change Fintype.card Capacity ≤ (badRight π K empty a.1)ᶜ.card + 150
    change _ ≤ 150 at bound
    omega
  · intro y hy
    have hg : Graph.Good (layout π) K (M (some y)) := by
      apply Classical.byContradiction
      intro bad
      dsimp only [s] at hy
      rw [Finset.mem_compl] at hy
      exact hy ((mem_badRight π K empty a.1 y).mpr bad)
    refine ⟨hg,chosen_of_visit π K _ hg ?_⟩
    simp [visit,p,BList.ofFn_ofList,run,hu,M,a,layout]
  · have hv : visit π K (M none) p = none := by
      simp [visit,p,BList.ofFn_ofList,run,hu,M,a,layout]
    simp only [mate,hv]

private theorem real_fraction (x n : ℕ) : ((x : ℂ) / (n : ℂ)).re = (x : ℝ) / (n : ℝ) := by
  have e := Complex.ofReal_div (x : ℝ) (n : ℝ)
  simpa only [Complex.ofReal_natCast,Complex.ofReal_re] using congrArg Complex.re e.symm

/-- For a sparse input projected onto good databases, a single output
coordinate of the local-compression commutator already exceeds one half.
The input is the uniform, subnormalized sum over the good mask branches,
with a single recorded h value at the capacity reached in each branch. -/
theorem right_mask_large_coefficient (hπ : ¬irregular π) (he : ¬Pairs.exceptional π)
    (r val : Rate) (u : Capacity) :
    ∃ (s : Finset Capacity) (p : Path 1) (head : Rate) (z : Capacity → Capacity)
      (K : Db) (M : Option Capacity → Db),
      (∀ y ∈ s, Graph.Good (layout π) K (M (some y))) ∧
      (1/2 : ℝ) < (∑ y ∈ s, cellAmp Capacity * RelabelSlice.coefficient
        (fun b => Function.Involutive.toPerm _ (swap_twice π K (M b) 1))
        y (one (.inl (z y)) val) (one (.inr p) (rateXor val head))).re := by
  obtain ⟨s,p,head,z,K,M,count,good,miss⟩ := one_block_branches π hπ he r u
  refine ⟨s,p,head,z,K,M,fun y hy => (good y hy).1,?_⟩
  rw [right_mask_coefficient π K M s z p head val (fun y hy => (good y hy).2) miss]
  have hc : Fintype.card Capacity = 2^512 := by
    change Fintype.card (Fin 8 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  rw [hc] at count ⊢
  have numeric : 2^512 < 2 * s.card := by omega
  have ht : (2^512 : ℝ) < 2 * s.card := by exact_mod_cast numeric
  rw [real_fraction,Nat.cast_pow,Nat.cast_ofNat]
  exact (lt_div_iff₀ (by positivity)).mpr (by linarith)

/-- On the selected good, bounded real databases, exchanging local
compression and the recorded-path relabeling has an output coefficient
above one half on an input with squared norm at most one. -/
theorem sparse_commutator_witness (hπ : ¬irregular π) (he : ¬Pairs.exceptional π)
    (r val : Rate) (u : Capacity) :
    ∃ (s : Finset Capacity) (p : Path 1) (head : Rate) (z : Capacity → Capacity)
      (K : Db) (M : Option Capacity → Db),
      let w := RelabelSlice.correlated s (fun y => (one (.inl (z y)) val : Cells 1))
      let V := RelabelSlice.relabel (fun b => Function.Involutive.toPerm _ (swap_twice π K (M b) 1))
      let out : Cells 1 := one (.inr p) (rateXor val head)
      (∀ y ∈ s, Graph.Good (layout π) K (M (some y))) ∧
      (∑ b, ∑ x, Complex.normSq (w b x)) ≤ 1 ∧
      (1/2 : ℝ) < (RelabelSlice.compress (V w) none out - V (RelabelSlice.compress w) none out).re := by
  classical
  obtain ⟨s,p,head,z,K,M,good,large⟩ := right_mask_large_coefficient π hπ he r val u
  refine ⟨s,p,head,z,K,M,good,?_,?_⟩
  · rw [RelabelSlice.correlated_mass]
    apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
    exact_mod_cast Finset.card_le_univ s
  · rw [RelabelSlice.commutator_component]
    exact large

end Reduction.ShakePermutation.Relabel
#print axioms Reduction.ShakePermutation.Relabel.right_mask_coefficient
#print axioms Reduction.ShakePermutation.Relabel.one_block_branches
#print axioms Reduction.ShakePermutation.Relabel.right_mask_large_coefficient
#print axioms Reduction.ShakePermutation.Relabel.sparse_commutator_witness
