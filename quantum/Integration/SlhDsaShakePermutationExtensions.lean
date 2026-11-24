import Integration.SlhDsaShakePermutationUpdate
import Integration.SlhDsaShakePermutationAttach
import Integration.SlhDsaShakePermutationPairAttach

namespace Reduction.ShakePermutation
open Classical Tails Tails.Graph Pairs
set_option allowUnsafeReducibility true in
attribute [local irreducible] Tails.Graph.support Tails.Graph.reached Tails.Graph.intermediate
set_option linter.unusedSectionVars false

noncomputable def forbidden (π : Permutation) (k k' : Db) : Finset Rate :=
  (intermediate (layout π) k k').image Prod.fst ∪ support k'

def extensionBudget (t : ℕ) := 4*(t+1)*(t*(t+1)+t) + 31*(t+1)^2 + (t+1)

private noncomputable def avoid (π : Permutation) (pending : Finset (Rate × Capacity)) (banned : Finset Rate) :=
  badAttach π pending banned ∪ together π pending

private theorem avoid_out (π : Permutation) (pending : Finset (Rate × Capacity)) (banned : Finset Rate)
    {y : Capacity} (hy : y ∉ avoid π pending banned) {p} (hp : p ∈ pending) :
    resultingRate π p y ∉ banned := by
  intro h
  exact hy (Finset.mem_union_left _ ((mem_badAttach ..).mpr ⟨p,hp,h⟩))

private theorem avoid_inj (π : Permutation) (pending : Finset (Rate × Capacity)) (banned : Finset Rate)
    {y : Capacity} (hy : y ∉ avoid π pending banned) {p q} (hp : p ∈ pending) (hq : q ∈ pending)
    (he : resultingRate π p y = resultingRate π q y) : p = q := by
  by_contra hn
  exact hy (Finset.mem_union_right _ ((mem_together ..).mpr ⟨p,hp,q,hq,hn,he⟩))

private theorem avoid_card (π : Permutation) (hπ : ¬irregular π) (he : ¬exceptional π)
    (k k' : Db) (g : Good (layout π) k k') (t : ℕ) (hk : (support k).card ≤ t) (hk' : (support k').card ≤ t)
    (pending : Finset (Rate × Capacity)) (hp : pending.card ≤ t+1) :
    (avoid π pending (forbidden π k k')).card ≤ 4*(t+1)*(t*(t+1)+t) + 31*(t+1)^2 := by
  have hi := (Tails.good_card π k k' g t hk hk').2
  have hf : (forbidden π k k').card ≤ t*(t+1)+t :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_image_le.trans hi) hk')
  have hbad := badAttach_step π hπ pending _ t hp hf
  have hpair := (together_card π he pending).trans (Nat.mul_le_mul_right 31 (Nat.mul_le_mul hp hp))
  simpa only [avoid,pow_two,Nat.mul_comm 31 _] using (Finset.card_union_le _ _).trans (Nat.add_le_add hbad hpair)

private theorem lookup_none {R C : Type} [Fintype R] (k : R → Option C) {r : R} (hr : r ∉ support k) : k r = none := by
  cases h : k r with
  | none => rfl
  | some x => exact (hr ((Tails.Graph.mem_support _ _).mpr (by simp [h]))).elim

private theorem rate_left (π : Permutation) (x : Rate) (z y : Capacity) :
    ((layout π).middle x z y).1 = resultingRate π (x,z) y := by
  change rateOf (π (join x (xorCap z y))) = rateOf (π (join x (xorCap y z)))
  rw [show xorCap z y = xorCap y z by funext i; exact UInt64.xor_comm ..]

noncomputable def badLeft (π : Permutation) (k k' : Db) (x : Rate) : Finset Capacity := by
  classical exact Finset.univ.filter (fun y => ¬Good (layout π) (Function.update k x (some y)) k')
noncomputable def badRight (π : Permutation) (k k' : Db) (x : Rate) : Finset Capacity := by
  classical exact Finset.univ.filter (fun y => ¬Good (layout π) k (Function.update k' x (some y)))

private theorem mem_badLeft (π : Permutation) (k k' : Db) (x : Rate) (y : Capacity) :
    y ∈ badLeft π k k' x ↔ ¬Good (layout π) (Function.update k x (some y)) k' := by classical simp [badLeft]
theorem mem_badRight (π : Permutation) (k k' : Db) (x : Rate) (y : Capacity) :
    y ∈ badRight π k k' x ↔ ¬Good (layout π) k (Function.update k' x (some y)) := by classical simp [badRight]
set_option allowUnsafeReducibility true in
attribute [local irreducible] badLeft badRight

/-- A safe left update preserves the graph and introduces no tail. -/
def LeftCert (π : Permutation) (k k' : Db) (x : Rate) (y : Capacity) : Prop :=
  Good (layout π) (Function.update k x (some y)) k' ∧
    ∀ {l z}, Tail (layout π) (Function.update k x (some y)) k' l z → Tail (layout π) k k' l z

/-- A safe right update admits at most one fresh reached capacity, outside all
previously protected capacity cells. Every other tail already existed. -/
def RightCert (π : Permutation) (k k' : Db) (held : Finset Capacity) (x : Rate) (y : Capacity) : Prop :=
  Good (layout π) k (Function.update k' x (some y)) ∧ ∃ mark : Option Capacity,
    (∀ z, mark = some z → z ∉ reached (layout π) k k' ∧ z ∉ held) ∧
    ∀ {l z}, Tail (layout π) k (Function.update k' x (some y)) l z →
      Tail (layout π) k k' l z ∨ mark = some z

noncomputable def failures (P : Capacity → Prop) : Finset Capacity := by
  classical exact Finset.univ.filter (fun y => ¬P y)

theorem mem_failures (P : Capacity → Prop) (y : Capacity) : y ∈ failures P ↔ ¬P y := by
  classical simp [failures]

set_option allowUnsafeReducibility true in
attribute [local irreducible] failures

theorem leftCert_card (π : Permutation) (hπ : ¬irregular π) (he : ¬exceptional π)
    (k k' : Db) (g : Good (layout π) k k') (t : ℕ) (hk : (support k).card ≤ t) (hk' : (support k').card ≤ t)
    (x : Rate) : (failures (LeftCert π k k' x)).card ≤ extensionBudget t := by
  classical
  let pending := (reached (layout π) k k').image fun z => (x,z)
  let banned := forbidden π k k'
  have memL (z) (hz : z ∈ reached (layout π) k k') : (x,z) ∈ pending := Finset.mem_image_of_mem (fun z => (x,z)) hz
  have sub : failures (LeftCert π k k' x) ⊆ avoid π pending banned := by
    intro y hy
    by_contra h
    apply (mem_failures _ _).mp hy
    have stop (z) (hz : z ∈ reached (layout π) k k') : k' (((layout π).middle x z y).1) = none := by
      apply lookup_none
      rw [rate_left]
      exact fun hh => avoid_out π pending banned h (memL z hz) (Finset.mem_union_right _ hh)
    refine ⟨good_update_left _ _ _ g x y stop ?_ ?_,fun ht => update_left_tail _ _ _ x y stop ht⟩
    · intro z hz p hp
      rw [rate_left]
      intro eq
      apply avoid_out π pending banned h (memL z hz)
      rw [eq]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
    · intro a ha b hb eq
      simp only [rate_left] at eq
      have hpair := avoid_inj π pending banned h (memL a ha) (memL b hb) eq
      rw [show a = b from congrArg Prod.snd hpair]
  have hp : pending.card ≤ t+1 := Finset.card_image_le.trans (Tails.good_card π k k' g t hk hk').1
  exact (Finset.card_le_card sub).trans ((avoid_card π hπ he k k' g t hk hk' pending hp).trans (Nat.le_add_right ..))

private theorem rotate (p y u : Capacity) : xorCap (xorCap p y) u = xorCap y (xorCap p u) := by
  funext i
  simp only [xorCap, UInt64.xor_comm (p i) (y i), UInt64.xor_assoc]

private theorem active_card (π : Permutation) (hπ : ¬irregular π) (he : ¬exceptional π)
    (k k' : Db) (g : Good (layout π) k k') (t : ℕ) (hk : (support k).card ≤ t) (hk' : (support k').card ≤ t)
    (held : Finset Capacity) (l : List Rate) (z : Capacity) (r : Rate) (u : Capacity) (ht : Tail (layout π) k k' l z)
    (hu : k r = some u) :
    (failures (RightCert π k k' held (mid π r z u).1)).card ≤ extensionBudget t + held.card := by
  classical
  let p := mid π r z u
  let R := reached (layout π) k k'
  let pending := (support k).image fun s => (s,xorCap p.2 ((k s).getD (fun _ => 0)))
  let banned := forbidden π k k'
  let roots := (R ∪ held).image (fun z => xorCap p.2 z)
  have pp : p ∈ intermediate (layout π) k k' :=
    (mem_intermediate ..).mpr ⟨z,(mem_reached ..).mpr ⟨l,ht⟩,r,u,hu,rfl⟩
  have mem (s : Rate) (v : Capacity) (hv : k s = some v) : (s,xorCap p.2 v) ∈ pending := by
    apply Finset.mem_image.mpr
    exact ⟨s,(Tails.Graph.mem_support _ _).mpr (by simp [hv]),by simp [hv]⟩
  have out (s : Rate) (v y : Capacity) : ((layout π).middle s ((layout π).finish p.2 y) v).1 =
      resultingRate π (s,xorCap p.2 v) y := by
    change rateOf (π (join s (xorCap (xorCap p.2 y) v))) = rateOf (π (join s (xorCap y (xorCap p.2 v))))
    rw [rotate]
  have sub : failures (RightCert π k k' held p.1) ⊆ avoid π pending banned ∪ roots := by
    intro y hy
    by_contra h
    have h₁ : y ∉ avoid π pending banned := fun v => h (Finset.mem_union_left _ v)
    have h₂ : y ∉ roots := fun v => h (Finset.mem_union_right _ v)
    apply (mem_failures _ _).1 hy
    let newCap := xorCap p.2 y
    have fresh : newCap ∉ R ∪ held := by
      intro hr
      apply h₂
      exact Finset.mem_image.mpr ⟨xorCap p.2 y,hr,by funext i; simp [xorCap,← UInt64.xor_assoc]⟩
    have stop (s v) (hv : k s = some v) : k' (((layout π).middle s ((layout π).finish p.2 y) v).1) = none := by
      rw [out]
      have hn := avoid_out π pending banned h₁ (mem s v hv)
      exact lookup_none k' (fun h => hn (Finset.mem_union_right _ h))
    have disjoint (s v) (hv : k s = some v) (b) (hb : b ∈ intermediate (layout π) k k') :
        ((layout π).middle s ((layout π).finish p.2 y) v).1 ≠ b.1 := by
      rw [out]
      intro eq
      apply avoid_out π pending banned h₁ (mem s v hv)
      rw [eq]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)
    have good : Good (layout π) k (Function.update k' p.1 (some y)) := by
      apply good_update_right_hit _ _ _ g (fun ha hb hc => mid_injective π k ha hb hc) l z r u y ht hu
        (fun h => fresh (Finset.mem_union_left _ h)) stop disjoint
      intro s v b w hv hw eq
      change ((layout π).middle s ((layout π).finish p.2 y) v).1 =
        ((layout π).middle b ((layout π).finish p.2 y) w).1 at eq
      rw [out,out] at eq
      obtain hs := congrArg Prod.fst (avoid_inj π pending banned h₁ (mem s v hv) (mem b w hw) eq)
      change s = b at hs
      subst b
      rw [hv,Option.some.injEq] at hw
      subst w
      rfl
    refine ⟨good,some newCap,?_,?_⟩
    · rintro z' h
      cases h
      exact ⟨fun h => fresh (Finset.mem_union_left _ h),fun h => fresh (Finset.mem_union_right _ h)⟩
    · intro tail cap h
      obtain h | h := update_right_tail _ _ _ g (fun ha hb hc => mid_injective π k ha hb hc) l z r u y ht hu
        stop disjoint h
      · exact Or.inl h
      · exact Or.inr (congrArg some h.2.symm)
  have hp : pending.card ≤ t+1 := Finset.card_image_le.trans (hk.trans (Nat.le_succ _))
  have hroots : roots.card ≤ (t+1) + held.card := Finset.card_image_le.trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Tails.good_card π k k' g t hk hk').1 _))
  have h := (Finset.card_le_card sub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (avoid_card π hπ he k k' g t hk hk' pending hp) hroots))
  simpa only [extensionBudget,Nat.add_assoc] using h

theorem rightCert_card (π : Permutation) (hπ : ¬irregular π) (he : ¬exceptional π)
    (k k' : Db) (g : Good (layout π) k k') (t : ℕ) (hk : (support k).card ≤ t) (hk' : (support k').card ≤ t)
    (held : Finset Capacity) (x : Rate) : (failures (RightCert π k k' held x)).card ≤ extensionBudget t + held.card := by
  classical
  by_cases hx : ∃ p ∈ intermediate (layout π) k k', p.1 = x
  · obtain ⟨p,hp,rfl⟩ := hx
    obtain ⟨z,hz,r,u,hu,rfl⟩ := (mem_intermediate ..).mp hp
    obtain ⟨l,hl⟩ := (mem_reached ..).mp hz
    exact active_card π hπ he k k' g t hk hk' held l z r u hl hu
  · have hem : failures (RightCert π k k' held x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      apply (mem_failures _ _).1 hy
      have miss : ∀ p ∈ intermediate (layout π) k k', p.1 ≠ x := fun p hp e => hx ⟨p,hp,e⟩
      exact ⟨good_update_right_missing _ _ _ g x y miss,none,by simp,fun h => Or.inl (update_right_missing_tail _ _ _ x y miss h)⟩
    simp [hem]

theorem badLeft_card (π : Permutation) (hπ : ¬irregular π) (he : ¬exceptional π)
    (k k' : Db) (g : Good (layout π) k k') (t : ℕ) (hk : (support k).card ≤ t) (hk' : (support k').card ≤ t)
    (x : Rate) : (badLeft π k k' x).card ≤ extensionBudget t := by
  refine (Finset.card_le_card ?_).trans (leftCert_card π hπ he k k' g t hk hk' x)
  exact fun y hy => (mem_failures _ _).2 (fun h => (mem_badLeft ..).1 hy h.1)

theorem badRight_card (π : Permutation) (hπ : ¬irregular π) (he : ¬exceptional π)
    (k k' : Db) (g : Good (layout π) k k') (t : ℕ) (hk : (support k).card ≤ t) (hk' : (support k').card ≤ t)
    (x : Rate) : (badRight π k k' x).card ≤ extensionBudget t := by
  have h := rightCert_card π hπ he k k' g t hk hk' ∅ x
  simp only [Finset.card_empty,Nat.add_zero] at h
  refine (Finset.card_le_card ?_).trans h
  exact fun y hy => (mem_failures _ _).2 (fun h => (mem_badRight ..).1 hy h.1)

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.badLeft_card
#print axioms Reduction.ShakePermutation.badRight_card
