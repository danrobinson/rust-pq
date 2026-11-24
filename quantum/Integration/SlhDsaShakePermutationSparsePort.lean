import Integration.SlhDsaShakePermutationResample
import Integration.SlhDsaShakeXofRows
import Mathlib.Data.Fintype.CardEmbedding

/-! Local simulation of simultaneous full-word swaps on a sparse formatted
domain. Only the original row and two private-suffix candidates need an
ideal head value, even when the public query is inverse. -/
namespace Reduction.ShakePermutation.SparsePort
open Classical ShakeXof
noncomputable section
set_option linter.unusedSectionVars false
variable {J Y Z : Type} [Fintype J] [DecidableEq J] [DecidableEq Y] [DecidableEq Z]
variable (e : Words ≃ Y × Z) (a : J ↪ Words) (π : Permutation) (suffix : J → Z)

abbrev Bucket (z : Z) := {j : J // suffix j = z}

def small := ∀ z, Fintype.card (Bucket suffix z) ≤ 2

def candidate (z : Z) (i : Fin 2) : Option J :=
  if h : i.val < Fintype.card (Bucket suffix z) then
    some (((Fintype.equivFin (Bucket suffix z)).symm ⟨i.val,h⟩).val) else none

theorem candidate_sound {z : Z} {i : Fin 2} {j : J} (record : candidate suffix z i = some j) :
    suffix j = z := by
  unfold candidate at record
  split_ifs at record with h
  · rw [← Option.some.inj record]; exact ((Fintype.equivFin (Bucket suffix z)).symm ⟨i.val,h⟩).property

theorem candidate_cover (bound : small suffix) (j : J) :
    ∃ i : Fin 2, candidate suffix (suffix j) i = some j := by
  let u : Bucket suffix (suffix j) := ⟨j,rfl⟩
  let k := Fintype.equivFin _ u
  refine ⟨⟨k.val,lt_of_lt_of_le k.isLt (bound _)⟩,?_⟩
  simp only [candidate,dite_eq_left k.isLt]
  exact congrArg (fun v : Bucket suffix (suffix j) => some v.val) ((Fintype.equivFin _).symm_apply_apply u)

def old (w : Words) : Option J := locate a (π.symm w)

def slot (p : Port) (i : Fin 3) : Option J :=
  let w := if p.1 then p.2 else π p.2
  Fin.cases (old a π w) (candidate suffix (e w).2) i

def eval (p : Port) (v : Fin 3 → Y) : Words := Id.run do
  let w := if p.1 then p.2 else π p.2
  let moved := match old a π w with
    | some j => e.symm (v 0,suffix j)
    | none =>
      if h : ∃ i : Fin 2, (candidate suffix (e w).2 i).isSome ∧ v i.succ = (e w).1 then
        ((candidate suffix (e w).2 h.choose).map (fun j => π (a j))).getD w
      else w
  return if p.1 then π.symm moved else moved

def target (F : J → Y) (j : J) : Words := e.symm (F j,suffix j)

def value (F : J → Y) (base : J) (p : Port) (i : Fin 3) := F ((slot e a π suffix p i).getD base)

private theorem old_hit (j : J) : old a π (π (a j)) = some j := by
  simp only [old,Equiv.symm_apply_apply,locate_emb]

private theorem old_sound {w : Words} {j : J} (h : old a π w = some j) : π (a j) = w := by
  exact π.eq_symm_apply.mp (ShakeXof.located a h)

private theorem local_swap (bound : small suffix) (F : J → Y)
    (ok : Function.Injective (Program.pair a π (target e suffix F))) (w : Words)
    (v : Fin 3 → Y)
    (vo : ∀ j, old a π w = some j → v 0 = F j)
    (vc : ∀ i j, candidate suffix (e w).2 i = some j → v i.succ = F j) :
    (match old a π w with
      | some j => e.symm (v 0,suffix j)
      | none =>
        if h : ∃ i : Fin 2, (candidate suffix (e w).2 i).isSome ∧ v i.succ = (e w).1 then
          ((candidate suffix (e w).2 h.choose).map (fun j => π (a j))).getD w
        else w) = Program.exchange ⟨_,ok⟩ w := by
  let f : (Bool × J) ↪ Words := ⟨_,ok⟩
  cases hOld : old a π w with
  | some j =>
    have hw := old_sound a π hOld
    rw [vo j hOld,← hw]
    exact (Program.exchange_hit f false j).symm
  | none =>
    split_ifs with h
    · obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp h.choose_spec.1
      rw [hj]
      have new : target e suffix F j = w := e.symm_apply_eq.mpr
        (Prod.ext ((vc _ _ hj).symm.trans h.choose_spec.2) (candidate_sound suffix hj))
      rw [← new]
      exact (Program.exchange_hit f true j).symm
    · apply (Program.exchange_miss f _ ?_).symm
      rintro ⟨⟨b,j⟩,hit⟩
      cases b with
      | false =>
        change π (a j) = w at hit
        rw [← hit,old_hit] at hOld
        contradiction
      | true =>
        change target e suffix F j = w at hit
        have parts := e.symm_apply_eq.mp hit
        obtain ⟨i,hi⟩ := candidate_cover suffix bound j
        have row : candidate suffix (e w).2 i = some j := by rw [← parts]; exact hi
        exact h ⟨i,by simp [row],(vc _ _ row).trans (congrArg Prod.fst parts)⟩

/-- Coherent-query response computed from three selected cells of F. On the
exceptional branches the evaluator is still total and uses the same slots. -/
theorem eval_eq (bound : small suffix) (F : J → Y) (base : J)
    (ok : Function.Injective (Program.pair a π (target e suffix F))) (p : Port) :
    eval e a π suffix p (value e a π suffix F base p) =
      oracle (π.trans (Program.exchange ⟨_,ok⟩)) p := by
  let w := if p.1 then p.2 else π p.2
  have h := local_swap e a π suffix bound F ok w (value e a π suffix F base p)
    (by intro j hj; simp only [value,slot,Fin.cases_zero,w] at *; simp [hj])
    (by intro i j hj; simp only [value,slot,Fin.cases_succ,w] at *; simp [hj])
  have inv (z : Words) : (Program.exchange (⟨_,ok⟩ : (Bool × J) ↪ Words)).symm z =
      Program.exchange ⟨_,ok⟩ z := (Equiv.symm_apply_eq _).mpr (Program.exchange_self ..).symm
  rcases p with ⟨d,x⟩
  cases d
  · exact h
  · change π.symm _ = π.symm ((Program.exchange (⟨_,ok⟩ : (Bool × J) ↪ Words)).symm x)
    rw [inv]
    exact congrArg π.symm h

end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.eval_eq
