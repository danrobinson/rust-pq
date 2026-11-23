import Kappleone.Funs
import Kappleperm.Proof
import Slhdsa.Proofs.Keccak
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace slhdsa.Kappleone
open KappleoneRust.shake256.parallel
open KeccakRegisters
set_option maxHeartbeats 1200000
theorem duplicate (s : Array U64 25#usize) :
    core.array.from_fn 25#usize single.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642 s
      ⦃ out => Kappleperm.view out 0 = Keccak.words s ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 25#usize _ _
    (fun i (v : Array U64 2#usize) => v.val[0]! = s.val[i]!) ?_)
  · intro out h
    apply ext25 _ _ (by simp [Kappleperm.view]) (by simp [Keccak.words])
    intro i hi
    unfold Kappleperm.view
    rw [ofFnAt _ _ hi]
    have eq := h i hi
    simp only [Array.getElem!_Nat_eq] at eq
    simpa [Keccak.words,getElem!_pos,hi] using congrArg UScalar.bv eq
  intro i hi
  unfold single.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642
  simp only [single.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642.call_mut,bind_tc_eq]
  step as ⟨word,hword⟩
  simp [Array.getElem!_Nat_eq,Array.repeat,getElem!_pos,hi,hword,
    getElem?_pos s.val i.val (by simpa using hi)]

theorem first (s : Array U64 25#usize) (words : Matrix 2#usize) :
    single_loop ⟨0#usize,25#usize⟩ s words ⦃ out => Keccak.words out = Kappleperm.view words 0 ⦄ := by
  unfold single_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U64 25#usize) => 25-p.1.start.val)
    (inv := fun p => p.1.end = 25#usize ∧ p.1.start.val ≤ 25 ∧
      ∀ j, j < p.1.start.val → p.2.val[j]! = words.val[j]!.val[0]!)
  · rintro ⟨it,st⟩ ⟨he,hb,prior⟩
    simp only at *
    unfold single_loop.body
    by_cases more : it.start.val < 25
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      rw [get]
      simp only [bind_ok]
      step as ⟨row,r⟩
      step as ⟨x,hx⟩
      step as ⟨out,hout⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro j hj
      rw [hout,Array.set_val_eq,getElem!_pos _ _ (by simp; omega),List.getElem_set]
      split
      · subst j
        simpa [r,getElem!_pos,more] using hx
      · rename_i ne
        rw [← getElem!_pos st.val j (by simp; omega)]
        exact prior j (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.not_lt.mp more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      apply ext25 _ _ (by simp [Keccak.words]) (by simp [Kappleperm.view])
      intro j hj
      unfold Kappleperm.view
      rw [ofFnAt _ _ hj]
      simpa [Keccak.words,getElem!_pos,hj] using congrArg UScalar.bv (prior j (by omega))
  · exact ⟨rfl,Nat.zero_le _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

theorem single_fips (s : Array U64 25#usize) :
    single s ⦃ out => Keccak.words out = permute (Keccak.words s) ⦄ := by
  unfold single
  step with duplicate as ⟨matrix,hm⟩
  simp only [KappleoneRust.sha512.hw.arm.available,bind_ok,massert,ite_true]
  step with Kappleperm.permute_fips matrix as ⟨r,hr⟩
  step with first s r as ⟨out,eq⟩
  rw [eq,hr,hm]
end slhdsa.Kappleone
