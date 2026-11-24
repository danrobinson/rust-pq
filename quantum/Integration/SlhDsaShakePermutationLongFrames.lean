import Integration.SlhDsaShakePermutationLongGram
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fin.Tuple.Basic

/-! The exact factorial coefficient for a tagged order-r partial graph
in one row of the completion Gram matrix. An unmatched coordinate must
avoid both previously occupied sets. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical OracleComp PermutationConditioning Finset
noncomputable section
set_option linter.unusedSectionVars false
variable {A : Type} [Fintype A] [DecidableEq A] {r : ℕ}

def pairs (x y : Fin r → A) : Trace A := List.ofFn (fun i => (x i,y i))

theorem inputs_mem (t : Trace A) (x : A) : x ∈ inputs t ↔ ∃ y, (x,y) ∈ t := by
  simp only [inputs,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨⟨a,b⟩,hab,rfl⟩; exact ⟨b,hab⟩
  · rintro ⟨b,hab⟩; exact ⟨_,hab,rfl⟩

def admissible (D : Finset A) (p : Equiv.Perm A) (x y : Fin r → A) :=
  ∀ i, (x i ∈ D → y i = p (x i)) ∧ (x i ∉ D → p.symm (y i) ∉ D)

theorem compatible (t : Trace A) (p : Extensions t) (x y : Fin r → A)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    Nonempty (Extensions (t++pairs x y)) ↔ admissible (inputs t) p.val x y := by
  let D := inputs t
  constructor
  · rintro ⟨q⟩
    have old (a : A) (ha : a ∈ D) : q.val a = p.val a := by
      obtain ⟨b,mem⟩ := (inputs_mem t a).mp ha
      exact (q.property _ (List.mem_append_left _ mem)).trans (p.property _ mem).symm
    have new (i : Fin r) : q.val (x i) = y i :=
      q.property _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    intro i
    refine ⟨fun h => (new i).symm.trans (old _ h),?_⟩
    intro fresh used
    have same : q.val (x i) = q.val (p.val.symm (y i)) := (new i).trans
      ((p.val.apply_symm_apply _).symm.trans (old _ used).symm)
    exact fresh (q.val.injective same ▸ used)
  · intro h
    let I := {i : Fin r // x i ∉ D}
    let U := {a : A // a ∉ D}
    let src (i : I) : U := ⟨x i.val,i.property⟩
    let dst (i : I) : U := ⟨p.val.symm (y i.val),(h _).2 i.property⟩
    have hs : Function.Injective src := fun _ _ eq => Subtype.ext (hx (congrArg Subtype.val eq))
    have hd : Function.Injective dst := fun _ _ eq => Subtype.ext (hy (p.val.symm.injective (congrArg Subtype.val eq)))
    obtain ⟨u,hu⟩ := Equiv.Perm.exists_extending_pair src dst hs hd
    let q := (Equiv.Perm.ofSubtype (p := fun a => a ∉ D) u).trans p.val
    refine ⟨q,?_⟩
    intro e he
    change p.val (Equiv.Perm.ofSubtype u e.1) = e.2
    rcases List.mem_append.mp he with old|new
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem (p:=fun a => a ∉ D) u (not_not.mpr ((inputs_mem t _).mpr ⟨e.2,old⟩)),p.property _ old]
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp new
      change p.val (Equiv.Perm.ofSubtype u (x i)) = y i
      by_cases hi : x i ∈ D
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem (p:=fun a => a ∉ D) u (not_not.mpr hi),(h _).1 hi]
      · let i' : I := ⟨i,hi⟩
        have eq : ((u (src i')).val) = p.val.symm (y i) := congrArg Subtype.val (hu i')
        rw [Equiv.Perm.ofSubtype_apply_of_mem (p:=fun a => a ∉ D) u hi]
        exact (congrArg p.val eq).trans (p.val.apply_symm_apply _)

def freshSet (s : Finset A) (x : Fin r → A) := univ.filter (fun i => x i ∉ s)

theorem rank_append (t : Trace A) (x y : Fin r → A) (hx : Function.Injective x) :
    rank (t++pairs x y) = rank t + (freshSet (inputs t) x).card := by
  let fresh := freshSet (inputs t) x
  let emb : Fin r ↪ A := ⟨x,hx⟩
  have eq : inputs (t++pairs x y) = inputs t ∪ fresh.map emb := by
    ext a; simp only [inputs,List.map_append,List.toFinset_append,Finset.mem_union,Finset.mem_map,fresh,
      freshSet,Finset.mem_filter,Finset.mem_univ,true_and,emb,Function.Embedding.coeFn_mk,pairs,List.map_ofFn,List.mem_toFinset,List.mem_ofFn,Function.comp_apply]
    by_cases ha : a ∈ t.map Prod.fst
    · exact iff_of_true (Or.inl ha) (Or.inl ha)
    · constructor
      · rintro (old|⟨i,rfl⟩)
        · exact Or.inl old
        · exact Or.inr ⟨i,ha,rfl⟩
      · rintro (old|⟨i,_,eq⟩); exact Or.inl old; exact Or.inr ⟨i,eq⟩
  have disj : Disjoint (inputs t) (fresh.map emb) := by
    rw [Finset.disjoint_left]
    rintro a ha mem
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp mem
    exact (Finset.mem_filter.mp hi).2 ha
  rw [rank,eq,card_union_of_disjoint disj,card_map]; rfl

theorem coefficient (t : Trace A) (p : Extensions t) (x y : Fin r → A) (hx : Function.Injective x)
    (hy : Function.Injective y) : count (t++pairs x y) = if admissible (inputs t) p.val x y then
      (Fintype.card A - (rank t + (freshSet (inputs t) x).card)).factorial else 0 := by
  rw [count,compatible t p x y hx hy,rank_append t x y hx]

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.coefficient
