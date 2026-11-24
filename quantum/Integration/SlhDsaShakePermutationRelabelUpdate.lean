import Integration.SlhDsaShakePermutationRelabel
import Integration.SlhDsaShakePermutationGraph

namespace Reduction.ShakePermutation.Relabel
open Classical Tails
variable (π : Permutation) (k k' l l' : Db) {L : ℕ}

def realCells (L : ℕ) (h : Capacity → Option Rate) : Cells L := Sum.elim h (fun _ => none)

theorem run_extends (hk : ∀ r u, k r = some u → l r = some u)
    (hk' : ∀ r u, k' r = some u → l' r = some u)
    (rs : List Rate) {h : Rate} {z : Capacity} (hr : run π k k' rs = some (h,z)) :
    run π l l' rs = some (h,z) := by
  induction rs generalizing z h with
  | nil => exact hr
  | cons r rs ih =>
    cases he : run π k k' rs with
    | none => simp [run,he] at hr
    | some a =>
      rcases a with ⟨head,c⟩
      cases hu : k r with
      | none => simp [run,he,hu] at hr
      | some u =>
        cases hw : k' ((layout π).middle r c u).1 with
        | none => simp [run,he,hu,hw] at hr
        | some w => simpa [run,ih he,hk _ _ hu,hk' _ _ hw] using (by simpa [run,he,hu,hw] using hr :
            ((layout π).middle r c u).1 = h ∧ (layout π).finish ((layout π).middle r c u).2 w = z)

theorem chosen_of_visit (good : Graph.Good (layout π) k k') {x : Path L} {z : Capacity} {h : Rate}
    (e : visit π k k' x = some (h,z)) : chosen π k k' L z = some (x,h) := by
  classical
  have ok : ∃ b : Path L × Rate, visit π k k' b.1 = some (b.2,z) := ⟨(x,h),e⟩
  rw [chosen,dite_eq_left ok]
  congr 1
  have f := ok.choose_spec
  have same := good.uniqueTail ((run_tail π k k').mp ⟨_,f⟩) ((run_tail π k k').mp ⟨_,e⟩)
  have eqx : ok.choose.1 = x := by
    let packPath (xs : List Rate) := if h : xs.length ≤ L then some (BList.ofList xs h) else none
    have full (a : Path L) : packPath (List.ofFn a.2) = some a := by
      have small : (List.ofFn a.2).length ≤ L := by simpa only [List.length_ofFn] using Nat.le_of_lt_succ a.1.isLt
      simp only [packPath,dite_eq_left small,BList.ofList_ofFn]
    exact Option.some.inj ((full _).symm.trans ((congrArg packPath same).trans (full _)))
  apply Prod.ext eqx
  have eqh := f.symm.trans (by simpa only [eqx] using e)
  exact congrArg Prod.fst (Option.some.inj eqh)

theorem chosen_extends (hk : ∀ r u, k r = some u → l r = some u)
    (hk' : ∀ r u, k' r = some u → l' r = some u)
    (good : Graph.Good (layout π) l l') {z : Capacity} {x : Path L} {h : Rate}
    (e : chosen π k k' L z = some (x,h)) : chosen π l l' L z = some (x,h) :=
  chosen_of_visit π l l' good (run_extends π k k' l l' hk hk' _ (chosen_sound π k k' e))

private theorem opt_ext {α : Type} {a b : Option α} (eq : ∀ v, a = some v ↔ b = some v) : a = b := by
  cases a with
  | some v => exact ((eq v).mp rfl).symm
  | none => cases b with
    | none => rfl
    | some v => exact (eq v).mpr rfl

private theorem read_right (h : Capacity → Option Rate) (x : Path L) (v : Rate) :
    swap π k k' L (realCells L h) (.inr x) = some v ↔
      ∃ z hd, chosen π k k' L z = some (x,hd) ∧ twist hd (h z) = some v := by
  cases e : mate π k k' x with
  | none =>
    constructor
    · intro impossible; simp [swap,e,realCells] at impossible
    · rintro ⟨z,hd,he,_⟩
      rw [(mates π k k').mp he] at e; contradiction
  | some a =>
    rcases a with ⟨z,hd⟩
    simp only [swap,e,realCells,Sum.elim_inl]
    constructor
    · exact fun hv => ⟨z,hd,(mates π k k').mpr e,hv⟩
    · rintro ⟨w,b,he,hv⟩
      have same := Option.some.inj (e.symm.trans ((mates π k k').mp he))
      cases same
      exact hv

/-- An insertion of either mask commutes with the database relabeling on the
embedded real basis whenever no populated h cell changes its path or head. -/
theorem swap_real_stable (h : Capacity → Option Rate)
    (stable : ∀ z, h z ≠ none → chosen π k k' L z = chosen π l l' L z) :
    swap π k k' L (realCells L h) = swap π l l' L (realCells L h) := by
  funext i
  cases i with
  | inl z =>
    by_cases empty : h z = none
    · cases a : chosen π k k' L z <;> cases b : chosen π l l' L z <;>
        simp [swap,realCells,a,b,empty,twist]
    · simp only [swap,stable z empty]
  | inr x =>
    apply opt_ext; intro v
    rw [read_right,read_right]
    constructor <;> rintro ⟨z,hd,he,hv⟩ <;> refine ⟨z,hd,?_,hv⟩
    · rw [← stable z]; exact he
      intro e; simp [e,twist] at hv
    · rw [stable z]; exact he
      intro e; simp [e,twist] at hv

end Reduction.ShakePermutation.Relabel
#print axioms Reduction.ShakePermutation.Relabel.chosen_extends
#print axioms Reduction.ShakePermutation.Relabel.swap_real_stable
