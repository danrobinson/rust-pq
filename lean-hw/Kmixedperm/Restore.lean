import Kmixedperm.Pack
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace slhdsa.Kmixedperm
open KeccakRegisters KmixedpermRust
open KmixedpermRust.shake256.parallel
set_option maxHeartbeats 1200000

private theorem rowAt (s : Matrix 3#usize) (k : Usize) (r : Array U64 3#usize) (i : Nat) (h : i<25) :
    (s.set k r).val[i]! = if k.val=i then r else s.val[i]! := by
  rw [Array.set_val_eq,getElem!_pos _ i (by simp; omega),List.getElem_set,getElem!_pos s.val i (by simpa using h)]

theorem restore (s : Matrix 3#usize) (a : Rows) :
    mixed.permute_loop1 ⟨0#usize,25#usize⟩ s a ⦃ out => ∀ j, view out j = lane a j ⦄ := by
  unfold mixed.permute_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Matrix 3#usize) => 25-p.1.start.val)
    (inv := fun p => p.1.end = 25#usize ∧ p.1.start.val ≤ 25 ∧
      ∀ i, i < p.1.start.val → ∀ j : Fin 3, p.2.val[i]!.val[j.val]!.bv = atLane a.val[i]! j)
  · rintro ⟨it,st⟩ ⟨he,hb,prior⟩
    simp only at *
    unfold mixed.permute_loop1.body
    by_cases more : it.start.val < 25
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      rw [get]
      simp only [bind_ok]
      step as ⟨v,hv⟩
      simp only [core.core_arch.arm_shared.neon.generated.vgetq_lane_u64,
        show (0#i32).bv.toNat<2 by decide,show (1#i32).bv.toNat<2 by decide,dif_pos, bind_ok]
      step as ⟨out,hout⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro i hi j
      rw [hout,rowAt _ _ _ _ (by omega)]
      split
      · subst i
        rw [getElem!_pos a.val it.start.val (by simpa using more),← hv]
        fin_cases j <;> rfl
      · exact prior i (by omega) j
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.not_lt.mp more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      intro j
      unfold lane view
      congr 1
      funext i
      exact prior i.val (by have := i.isLt; omega) j
  · exact ⟨rfl,Nat.zero_le _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
end slhdsa.Kmixedperm
