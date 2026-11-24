import Integration.SlhDsaShakePermutationSparseArity
import Integration.SlhDsaShakePermutationSparseTransfer

/-! The local first-phase hash evaluator uses ideal heads only at the
specified tweak. A real forward step agrees except at an off-tweak input
or a recorded auxiliary target output. -/
namespace Reduction.ShakePermutation.SparsePort
open Classical ShakeXof
noncomputable section
variable {J Y Z T : Type} [DecidableEq T]
variable (e : Words ≃ Y × Z) (a : J ↪ Words) (π : Permutation) (s : J → Z)
variable (tag : J → T)

def shadow (F : J → Y) (d : T) (w : Words) : Words :=
  match locate a w with
  | none => π w
  | some j => if tag j = d then target e s F j else π w

theorem shadow_local (F G : J → Y) (d : T) (w : Words)
    (eq : ∀ j, tag j = d → F j = G j) :
    shadow e a π s tag F d w = shadow e a π s tag G d w := by
  unfold shadow
  split
  · rfl
  · rename_i j _
    by_cases h : tag j = d
    · simp only [h,target,ite_true,eq j h]
    · simp only [h,ite_false]

variable [Fintype J]
theorem shadow_agrees (F : J → Y)
    (ok : Function.Injective (Program.pair a π (target e s F)))
    (d : T) (w : Words) (valid : ∀ j, a j = w → tag j = d)
    (clear : ∀ j, (Program.resample a (π,target e s F)).1 w ≠ (Program.resample a (π,target e s F)).2 j) :
    shadow e a π s tag F d w = (Program.resample a (π,target e s F)).1 w := by
  let f : (Bool × J) ↪ Words := ⟨_,ok⟩
  simp only [Program.resample,dite_eq_left ok,Equiv.trans_apply,Function.comp_apply] at clear ⊢
  unfold shadow
  cases caseRow : locate a w with
  | some j =>
    have hw := located a caseRow
    change (if tag j = d then target e s F j else π w) = _
    rw [ite_eq_left (valid j hw),← hw]
    exact (Program.exchange_hit f false j).symm
  | none =>
    apply (Program.exchange_miss f (π w) ?_).symm
    rintro ⟨⟨b,j⟩,eq⟩
    cases b with
    | false =>
      change π (a j) = π w at eq
      rw [← π.injective eq,locate_emb] at caseRow
      contradiction
    | true =>
      apply clear j
      change Program.exchange f (π w) = π (a j)
      rw [← eq,Program.exchange_hit]
      rfl

namespace Arity
open MLink SLHDSA
variable (S : Sha2Set) (pk : S.Node)

private theorem tweak_byte (addr : Bytes 32) (l : List S.Node) (i : Fin 32) :
    blockByte (rateBlock (padded (sp (thBytes S pk addr l))) 0)
      ⟨S.vp.params.n + i.val,by have : S.vp.params.n ≤ 32 := by cases S <;> decide
                                omega⟩ = addr[i.val].toBitVec := by
  let j := S.vp.params.n+i.val
  have pre : j < (sp (pk.toList ++ addr.toList)).length := by simp [j,sp]
  have all : j < (sp (thBytes S pk addr l)).length := by
    unfold thBytes; rw [sp_append,List.length_append]; omega
  rw [blockByte_rateBlock]
  simp only [Nat.mul_zero,Nat.zero_add,Fin.val_mk]
  change (padded (sp (thBytes S pk addr l)))[j]?.getD 0 = _
  rw [padded,List.getElem?_append_left all,thBytes,sp_append,List.getElem?_append_left pre,sp_append,
    List.getElem?_append_right (by simp [j,sp])]
  simp [j,sp]

/-- Even if a longer input begins with the exact padding of a shorter one,
the public seed and all 32 tweak bytes precede that boundary. -/
theorem first_tweak (ar : ℕ) (bound : ar ≤ 2) (addr : Bytes 32) (xs : List S.Node)
    (j : Row S ar) (eq : input S ar pk bound j =
      join (rateBlock (padded (sp (thBytes S pk addr xs))) 0) 0) : j.1 = addr := by
  have hr := congrArg rateOf eq
  change rateOf (join (rateBlock (padded (sp (thBytes S pk j.1 j.2.val))) 0) 0) = _ at hr
  simp only [rate_join] at hr
  apply Vector.ext; intro i hi
  let w : Fin 32 := ⟨i,hi⟩
  have h := congrArg (fun r => blockByte r ⟨S.vp.params.n+w.val,by
    have : S.vp.params.n ≤ 32 := by cases S <;> decide
    omega⟩) hr
  simp only [tweak_byte] at h
  exact UInt8.toBitVec_inj.mp h

theorem later_miss (ar : ℕ) (bound : ar ≤ 2) (w : Words) (r : Rate) (safe : capOf w ≠ 0)
    (j : Row S ar) : input S ar pk bound j ≠ join r (capOf w) := by
  intro eq
  have cap := congrArg capOf eq
  change capOf (join _ 0) = capOf (join r (capOf w)) at cap
  exact safe ((cap_join _ _).symm.trans (cap.symm.trans (cap_join _ _)))

end Arity
end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.shadow_agrees
#print axioms Reduction.ShakePermutation.SparsePort.Arity.first_tweak
