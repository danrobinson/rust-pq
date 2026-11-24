import Integration.SlhDsaShakePermutationRegular

/-! Reachability in the two sparse capacity-mask databases of the masked permutation.
Tails are sequences of absorption inputs stored in chronological order. -/
namespace Reduction.ShakePermutation.Tails
open Classical


abbrev Db := Rate → Option Capacity
def xorCap (u v : Capacity) : Capacity := fun i => u i ^^^ v i
def mid (π : Permutation) (r : Rate) (z mask : Capacity) : Rate × Capacity :=
  let w := π (join r (xorCap z mask))
  (rateOf w, capOf w)

structure Layout (R C : Type) where
  zero : C
  middle : R → C → C → R × C
  finish : C → C → C

def layout (π : Permutation) : Layout Rate Capacity := ⟨fun _ => 0, mid π, xorCap⟩

namespace Graph
variable {R C : Type}

inductive Tail (π : Layout R C) (k k' : R → Option C) : List R → C → Prop where
  | root : Tail π k k' [] π.zero
  | step {l z r u v} : Tail π k k' l z → k r = some u → k' (π.middle r z u).1 = some v →
      Tail π k k' (l ++ [r]) (π.finish (π.middle r z u).2 v)

variable [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

noncomputable def support (k : R → Option C) : Finset R := Finset.univ.filter fun r => (k r).isSome
noncomputable def reached (π : Layout R C) (k k' : R → Option C) : Finset C := by
  classical exact Finset.univ.filter fun z => ∃ l, Tail π k k' l z

noncomputable def intermediate (π : Layout R C) (k k' : R → Option C) : Finset (R × C) :=
  ((support k) ×ˢ (reached π k k')).image fun p => π.middle p.1 p.2 ((k p.1).getD π.zero)

omit [Fintype R] [DecidableEq R] [DecidableEq C] in
theorem mem_reached (π : Layout R C) (k k' : R → Option C) (z : C) :
    z ∈ reached π k k' ↔ ∃ l, Tail π k k' l z := by classical simp [reached]
omit [Fintype C] [DecidableEq R] [DecidableEq C] in
theorem mem_support (k : R → Option C) (r : R) : r ∈ support k ↔ (k r).isSome := by simp [support]
theorem mem_intermediate (π : Layout R C) (k k' : R → Option C) (i : R × C) :
    i ∈ intermediate π k k' ↔ ∃ z ∈ reached π k k', ∃ r u, k r = some u ∧ i = π.middle r z u := by
  classical
  constructor
  · rintro hi
    obtain ⟨⟨r,z⟩,hp,he⟩ := Finset.mem_image.mp hi
    obtain ⟨hr,hz⟩ := Finset.mem_product.mp hp
    obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp ((mem_support _ _).mp hr)
    exact ⟨z,hz,r,u,hu,by simpa only [hu,Option.getD_some] using he.symm⟩
  · rintro ⟨z,hz,r,u,hu,rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨(r,z),Finset.mem_product.mpr ⟨(mem_support _ _).mpr (by simp [hu]),hz⟩,by simp [hu]⟩

structure Good (π : Layout R C) (k k' : R → Option C) : Prop where
  uniqueTail : ∀ {l₁ l₂ z}, Tail π k k' l₁ z → Tail π k k' l₂ z → l₁ = l₂
  uniqueRate : Set.InjOn Prod.fst (intermediate π k k' : Set (R × C))

private noncomputable def finished (π : Layout R C) (k k' : R → Option C) :=
  (intermediate π k k').filter fun p => p.1 ∈ support k'

private theorem cover (π : Layout R C) (k k' : R → Option C) :
    reached π k k' ⊆ insert π.zero ((finished π k k').image
      fun p => π.finish p.2 ((k' p.1).getD π.zero)) := by
  classical
  intro z hz
  obtain ⟨l,hl⟩ := (mem_reached _ _ _ _).mp hz
  cases hl with
  | root => simp
  | @step l z r u v ht hu hv =>
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨π.middle r z u, Finset.mem_filter.mpr ⟨?_,(mem_support _ _).mpr (by simp [hv])⟩,by simp [hv]⟩
    exact (mem_intermediate _ _ _ _).2 ⟨z,(mem_reached _ _ _ _).mpr ⟨l,ht⟩,r,u,hu,rfl⟩

/-- The count uses only injectivity of the intermediate rates. Each non-root reached
capacity is the completion of an intermediate pair from the second database. -/
theorem reached_card (π : Layout R C) (k k' : R → Option C) (h : Good π k k') :
    (reached π k k').card ≤ (support k').card + 1 := by
  classical
  let f : R × C → C := fun p => π.finish p.2 ((k' p.1).getD π.zero)
  calc
    _ ≤ (insert π.zero ((finished π k k').image f)).card := Finset.card_le_card (cover π k k')
    _ ≤ ((finished π k k').image f).card + 1 := Finset.card_insert_le ..
    _ ≤ (finished π k k').card + 1 := Nat.add_le_add_right Finset.card_image_le _
    _ ≤ (support k').card + 1 := by
      apply Nat.add_le_add_right
      apply Finset.card_le_card_of_injOn Prod.fst
      · exact fun _ hp => (Finset.mem_filter.mp hp).2
      · exact fun _ hp _ hq he => h.uniqueRate (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he

theorem intermediate_card (π : Layout R C) (k k' : R → Option C) :
    (intermediate π k k').card ≤ (support k).card * (reached π k k').card := by
  unfold intermediate
  exact Finset.card_image_le.trans (Finset.card_product ..).le

theorem good_card (π : Layout R C) (k k' : R → Option C) (h : Good π k k') (t : ℕ)
    (hk : (support k).card ≤ t) (hk' : (support k').card ≤ t) :
    (reached π k k').card ≤ t+1 ∧ (intermediate π k k').card ≤ t*(t+1) := by
  have hr := (reached_card π k k' h).trans (Nat.add_le_add_right hk' 1)
  exact ⟨hr,(intermediate_card π k k').trans (Nat.mul_le_mul hk hr)⟩

end Graph

theorem good_card (π : Permutation) (k k' : Db) (h : Graph.Good (layout π) k k') (t : ℕ)
    (hk : (Graph.support k).card ≤ t) (hk' : (Graph.support k').card ≤ t) :
    (Graph.reached (layout π) k k').card ≤ t+1 ∧
    (Graph.intermediate (layout π) k k').card ≤ t*(t+1) := Graph.good_card _ _ _ h t hk hk'

end Reduction.ShakePermutation.Tails
#print axioms Reduction.ShakePermutation.Tails.good_card
