import Integration.SlhDsaShakePermutationTails

namespace Reduction.ShakePermutation.Tails.Graph
open Classical

variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
variable (π : Layout R C) (k k' : R → Option C)

theorem update_left_tail (x : R) (y : C)
    (stop : ∀ z ∈ reached π k k', k' (π.middle x z y).1 = none)
    {l z} (h : Tail π (Function.update k x (some y)) k' l z) : Tail π k k' l z := by
  induction h with
  | root => exact .root
  | @step l z r u v ht hu hv ih =>
    by_cases hr : r = x
    · subst r
      simp only [Function.update_self,Option.some.injEq] at hu
      subst u
      rw [stop z ((mem_reached ..).2 ⟨l,ih⟩)] at hv
      contradiction
    · exact .step ih (by simpa only [Function.update_of_ne hr] using hu) hv

/-- Adding a left mask preserves all old tails if its new intermediate
rates are disconnected from the right database. The other hypotheses
exclude old/new and new/new intermediate-rate collisions. -/
theorem good_update_left (g : Good π k k') (x : R) (y : C)
    (stop : ∀ z ∈ reached π k k', k' (π.middle x z y).1 = none)
    (disjoint : ∀ z ∈ reached π k k', ∀ p ∈ intermediate π k k', (π.middle x z y).1 ≠ p.1)
    (inj : ∀ a ∈ reached π k k', ∀ b ∈ reached π k k',
      (π.middle x a y).1 = (π.middle x b y).1 → π.middle x a y = π.middle x b y) :
    Good π (Function.update k x (some y)) k' := by
  have hclass (p) (hp : p ∈ intermediate π (Function.update k x (some y)) k') :
      p ∈ intermediate π k k' ∨ ∃ z ∈ reached π k k', p = π.middle x z y := by
    obtain ⟨z,hz,r,u,hu,he⟩ := (mem_intermediate ..).1 hp
    obtain ⟨l,hl⟩ := (mem_reached ..).1 hz
    have hz' := (mem_reached π k k' z).2 ⟨l,update_left_tail π k k' x y stop hl⟩
    by_cases hr : r = x
    · subst r
      simp only [Function.update_self,Option.some.injEq] at hu
      exact Or.inr ⟨z,hz',hu ▸ he⟩
    · exact Or.inl ((mem_intermediate ..).2 ⟨z,hz',r,u,by simpa only [Function.update_of_ne hr] using hu,he⟩)
  refine ⟨fun h₁ h₂ => g.uniqueTail (update_left_tail π k k' x y stop h₁)
    (update_left_tail π k k' x y stop h₂),?_⟩
  intro a ha b hb he
  rcases hclass a ha with ha | ⟨z,hz,rfl⟩ <;> rcases hclass b hb with hb | ⟨w,hw,rfl⟩
  · exact g.uniqueRate ha hb he
  · exact (disjoint w hw a ha he.symm).elim
  · exact (disjoint z hz b hb he).elim
  · exact inj z hz w hw he

theorem update_right_missing_tail (x : R) (y : C)
    (miss : ∀ p ∈ intermediate π k k', p.1 ≠ x)
    {l z} (h : Tail π k (Function.update k' x (some y)) l z) : Tail π k k' l z := by
  induction h with
  | root => exact .root
  | @step l z r u v ht hu hv ih =>
    have hp := (mem_intermediate π k k' (π.middle r z u)).2
      ⟨z,(mem_reached ..).2 ⟨l,ih⟩,r,u,hu,rfl⟩
    exact .step ih hu (by simpa only [Function.update_of_ne (miss _ hp)] using hv)

/-- A query to a right mask rate outside all old intermediate rates is free
of graph transitions. -/
theorem good_update_right_missing (g : Good π k k') (x : R) (y : C)
    (miss : ∀ p ∈ intermediate π k k', p.1 ≠ x) :
    Good π k (Function.update k' x (some y)) := by
  have hsub : intermediate π k (Function.update k' x (some y)) ⊆ intermediate π k k' := by
    intro p hp
    obtain ⟨z,hz,r,u,hu,he⟩ := (mem_intermediate ..).1 hp
    obtain ⟨l,hl⟩ := (mem_reached ..).1 hz
    exact (mem_intermediate ..).2 ⟨z,(mem_reached ..).2 ⟨l,update_right_missing_tail π k k' x y miss hl⟩,r,u,hu,he⟩
  exact ⟨fun h₁ h₂ => g.uniqueTail (update_right_missing_tail π k k' x y miss h₁)
    (update_right_missing_tail π k k' x y miss h₂),fun _ ha _ hb he => g.uniqueRate (hsub ha) (hsub hb) he⟩

/-- Every path after a connected right insertion is old or is the one
extension of its unique old parent. -/
theorem update_right_tail (g : Good π k k')
    (linear : ∀ {r s z w u v}, k r = some u → k s = some v →
      π.middle r z u = π.middle s w v → r = s ∧ z = w)
    (l₀ : List R) (z₀ : C) (r₀ : R) (u₀ y : C)
    (ht₀ : Tail π k k' l₀ z₀) (hk₀ : k r₀ = some u₀)
    (stop : ∀ r u, k r = some u →
      k' (π.middle r (π.finish (π.middle r₀ z₀ u₀).2 y) u).1 = none)
    (disjoint : ∀ r u, k r = some u → ∀ p ∈ intermediate π k k',
      (π.middle r (π.finish (π.middle r₀ z₀ u₀).2 y) u).1 ≠ p.1)
    {l z} (ht : Tail π k (Function.update k' (π.middle r₀ z₀ u₀).1 (some y)) l z) :
    Tail π k k' l z ∨ (l = l₀ ++ [r₀] ∧ z = π.finish (π.middle r₀ z₀ u₀).2 y) := by
  let p₀ := π.middle r₀ z₀ u₀
  let zNew := π.finish p₀.2 y
  have hp₀ : p₀ ∈ intermediate π k k' := (mem_intermediate ..).2
    ⟨z₀,(mem_reached ..).2 ⟨_,ht₀⟩,r₀,u₀,hk₀,rfl⟩
  change Tail π k (Function.update k' p₀.1 (some y)) l z at ht
  change Tail π k k' l z ∨ (l = l₀ ++ [r₀] ∧ z = zNew)
  induction ht with
  | root => exact Or.inl .root
  | @step l z r u v ht hu hv ih =>
    rcases ih with old | ⟨_,rfl⟩
    · by_cases he : (π.middle r z u).1 = p₀.1
      · have hp : π.middle r z u ∈ intermediate π k k' := (mem_intermediate ..).2
          ⟨z,(mem_reached ..).2 ⟨_,old⟩,r,u,hu,rfl⟩
        have hm := g.uniqueRate hp hp₀ he
        obtain ⟨hr,hz⟩ := linear hu hk₀ hm
        subst r
        subst z
        have hv' : y = v := by simpa only [he,Function.update_self,Option.some.injEq] using hv
        rw [← hv',hm]
        exact Or.inr ⟨congrArg (· ++ [r₀]) (g.uniqueTail old ht₀),rfl⟩
      · exact Or.inl (.step old hu (by simpa only [Function.update_of_ne he] using hv))
    · have hn := disjoint r u hu p₀ hp₀
      have hn' : (π.middle r zNew u).1 ≠ p₀.1 := hn
      rw [Function.update_of_ne hn',stop r u hu] at hv
      contradiction

/-- Completing an old intermediate pair at the queried rate adds its one
new tail. The outgoing intermediate pairs of that tail must stay disconnected
from the right database and distinct from both old and new rate labels. -/
theorem good_update_right_hit (g : Good π k k')
    (linear : ∀ {r s z w u v}, k r = some u → k s = some v →
      π.middle r z u = π.middle s w v → r = s ∧ z = w)
    (l₀ : List R) (z₀ : C) (r₀ : R) (u₀ y : C)
    (ht₀ : Tail π k k' l₀ z₀) (hk₀ : k r₀ = some u₀)
    (fresh : π.finish (π.middle r₀ z₀ u₀).2 y ∉ reached π k k')
    (stop : ∀ r u, k r = some u →
      k' (π.middle r (π.finish (π.middle r₀ z₀ u₀).2 y) u).1 = none)
    (disjoint : ∀ r u, k r = some u → ∀ p ∈ intermediate π k k',
      (π.middle r (π.finish (π.middle r₀ z₀ u₀).2 y) u).1 ≠ p.1)
    (inj : ∀ r u s v, k r = some u → k s = some v →
      (π.middle r (π.finish (π.middle r₀ z₀ u₀).2 y) u).1 =
        (π.middle s (π.finish (π.middle r₀ z₀ u₀).2 y) v).1 →
      π.middle r (π.finish (π.middle r₀ z₀ u₀).2 y) u =
        π.middle s (π.finish (π.middle r₀ z₀ u₀).2 y) v) :
    Good π k (Function.update k' (π.middle r₀ z₀ u₀).1 (some y)) := by
  let p₀ := π.middle r₀ z₀ u₀
  let zNew := π.finish p₀.2 y
  have classify {l z} (ht : Tail π k (Function.update k' p₀.1 (some y)) l z) :
      Tail π k k' l z ∨ (l = l₀ ++ [r₀] ∧ z = zNew) :=
    update_right_tail π k k' g linear l₀ z₀ r₀ u₀ y ht₀ hk₀ stop disjoint ht
  have pairs (p) (hp : p ∈ intermediate π k (Function.update k' p₀.1 (some y))) :
      p ∈ intermediate π k k' ∨ ∃ r u, k r = some u ∧ p = π.middle r zNew u := by
    obtain ⟨z,hz,r,u,hu,he⟩ := (mem_intermediate ..).1 hp
    obtain ⟨l,hl⟩ := (mem_reached ..).1 hz
    rcases classify hl with old | ⟨_,rfl⟩
    · exact Or.inl ((mem_intermediate ..).2 ⟨z,(mem_reached ..).2 ⟨_,old⟩,r,u,hu,he⟩)
    · exact Or.inr ⟨r,u,hu,he⟩
  constructor
  · intro l₁ l₂ z h₁ h₂
    rcases classify h₁ with old | ⟨hl,hz⟩ <;> rcases classify h₂ with old' | ⟨hl',hz'⟩
    · exact g.uniqueTail old old'
    · subst z
      exact (fresh ((mem_reached π k k' zNew).2 ⟨_,old⟩)).elim
    · subst z
      exact (fresh ((mem_reached π k k' zNew).2 ⟨_,old'⟩)).elim
    · exact hl.trans hl'.symm
  · intro a ha b hb he
    rcases pairs a ha with ha | ⟨r,u,hu,rfl⟩ <;> rcases pairs b hb with hb | ⟨s,v,hv,rfl⟩
    · exact g.uniqueRate ha hb he
    · exact (disjoint s v hv a ha he.symm).elim
    · exact (disjoint r u hu b hb he).elim
    · exact inj r u s v hu hv he

end Reduction.ShakePermutation.Tails.Graph

namespace Reduction.ShakePermutation.Tails

theorem mid_injective (π : Permutation) (k : Db) {r s : Rate} {z w u v : Capacity}
    (hu : k r = some u) (hv : k s = some v) (he : mid π r z u = mid π s w v) : r = s ∧ z = w := by
  have hj := congrArg (fun t : Rate × Capacity => join t.1 t.2) he
  simp only [mid,join_split] at hj
  have hh := π.injective hj
  have hr := congrArg rateOf hh
  simp only [rate_join] at hr
  subst s
  rw [hu,Option.some.injEq] at hv
  subst v
  refine ⟨rfl,?_⟩
  have hc := congrArg capOf hh
  simp only [cap_join] at hc
  funext i
  have e := congrArg (fun a : Capacity => a i ^^^ u i) hc
  simpa [xorCap,UInt64.xor_assoc] using e

end Reduction.ShakePermutation.Tails

#print axioms Reduction.ShakePermutation.Tails.Graph.good_update_right_hit


#print axioms Reduction.ShakePermutation.Tails.Graph.good_update_left
#print axioms Reduction.ShakePermutation.Tails.Graph.good_update_right_missing
