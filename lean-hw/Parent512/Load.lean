import Parent512.Funs
import Slhdsa.Proofs.Platform
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Parents
open ParentsRust.sha512.x86
abbrev Blocks := Array (Array U8 128#usize) 8#usize

theorem initial_spec (N : Usize) (st : Array U64 8#usize) :
    core.array.Array.map (compress_parents.closure.Insts.CoreOpsFunctionFnMutTupleU64__m512i N) st ()
      ⦃ a => ∀ i, i < 8 → ∀ j : Fin 8, word64 a.val[i]! j = st.val[i]!.bv ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 8#usize _ () (fun i v => ∀ j : Fin 8, word64 v j = st.val[i]!.bv) ?_)
  · intro a h i hi j; simpa only [Array.getElem!_Nat_eq] using h i hi j
  intro i hi
  simp only [compress_parents.closure.Insts.CoreOpsFunctionFnMutTupleU64__m512i,
    compress_parents.closure.Insts.CoreOpsFunctionFnMutTupleU64__m512i.call_mut, lift, bind_ok,
    core.core_arch.x86.avx512f._mm512_set1_epi64]
  step*
  simp_all [step_simps, ← getElem!_pos]

private theorem be_eight (a0 a1 a2 a3 a4 a5 a6 a7 : U8) :
    (core.num.U64.from_be_bytes (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])).bv = a0.bv ++ a1.bv ++ a2.bv ++ a3.bv ++ a4.bv ++ a5.bv ++ a6.bv ++ a7.bv := by
  change (BitVec.fromLEBytes [a7.bv,a6.bv,a5.bv,a4.bv,a3.bv,a2.bv,a1.bv,a0.bv]).cast (by rfl) = _
  simp only [BitVec.fromLEBytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, BitVec.cast_eq]
  ext i hi
  simp only [BitVec.getElem_append (x := a0.bv ++ a1.bv ++ a2.bv ++ a3.bv ++ a4.bv ++ a5.bv ++ a6.bv) (y := a7.bv),
    BitVec.getElem_append (x := a0.bv ++ a1.bv ++ a2.bv ++ a3.bv ++ a4.bv ++ a5.bv) (y := a6.bv),
    BitVec.getElem_append (x := a0.bv ++ a1.bv ++ a2.bv ++ a3.bv ++ a4.bv) (y := a5.bv),
    BitVec.getElem_append (x := a0.bv ++ a1.bv ++ a2.bv ++ a3.bv) (y := a4.bv),
    BitVec.getElem_append (x := a0.bv ++ a1.bv ++ a2.bv) (y := a3.bv),
    BitVec.getElem_append (x := a0.bv ++ a1.bv) (y := a2.bv),
    BitVec.getElem_append (x := a0.bv) (y := a1.bv)]
  interval_cases i <;> simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]

theorem read_word (N : Usize) (bs : Blocks) (k j : Usize) (hk : k.val < 16) (hj : j.val < 8) :
    compress_parents.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (N := N) (bs,k) j ⦃ w c => w.bv = Spec.SHA512.word (bytes bs.val[j.val]!.val) (8*k.val) ∧ c = (bs,k) ⦄ := by
  unfold compress_parents.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  step*
  · cases r with
    | Ok a => exact ⟨a,rfl⟩
    | Err e => cases e; simp only at r_post; omega
  · refine ⟨?_, rfl⟩
    rename_i htry _ _
    have hlen : a2.val.length = 8 := by scalar_tac
    have hslice : a2.val = a1.val.slice (8*k.val) (8*k.val+8) := by
      subst r
      simp_all [Array.val_to_slice]
    let b (i : Nat) := a1.val[8*k.val+i]!
    have hv : a2.val = [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7] := by
      apply List.ext_getElem
      · simpa using hlen
      · intro i hi _
        have ht : i < 8 := by omega
        rw [← getElem!_pos a2.val i hi, hslice, List.getElem!_slice _ _ _ _ (by scalar_tac)]
        interval_cases i <;> rfl
    have hx : a2 = Array.make 8#usize [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7] := by
      exact Aeneas.Std.Array.ext _ _ hv
    have res : i3.bv = (core.num.U64.from_be_bytes a2).bv := i3_post
    rw [res,hx,be_eight, Spec.SHA512.word, getElem!_pos bs.val j.val (by scalar_tac), ← a1_post]
    repeat rw [bytes_getElem! _ _ (by scalar_tac)]
    simp (disch := scalar_tac) [b,getElem!_pos]

def block (bs : Blocks) (j : Fin 8) := bytes bs.val[j.val]!.val

theorem group_spec (N : Usize) (bs : Blocks) (k : Usize) (hk : k.val < 16) :
    compress_parents.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut (N := N) bs k
      ⦃ w c => (∀ j : Fin 8, word64 w j = Spec.SHA512.word (block bs j) (8*k.val)) ∧ c = bs ⦄ := by
  unfold compress_parents.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut
  let* ⟨lanes, hl⟩ ← core.array.from_fn.spec_stateless_getElem! 8#usize (compress_parents.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) (bs,k)
    (fun j (v : U64) => v.bv = Spec.SHA512.word (bytes bs.val[j]!.val) (8*k.val))
    (fun j hj => read_word N bs k j hk hj)
  simp only [core.intrinsics.transmute, bind_ok, step_simps]
  intro j
  change word64 (ofWords64 _) _ = _
  rw [word64_ofWords64]
  simpa only [Array.getElem!_Nat_eq, block] using hl j.val j.isLt

theorem words_spec (N : Usize) (bs : Blocks) :
    core.array.from_fn 16#usize
      (compress_parents.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N) bs ⦃ w =>
      ∀ k, k < 16 → ∀ j : Fin 8, word64 w.val[k]! j = Spec.SHA512.word (block bs j) (8*k) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize (compress_parents.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N) bs
    (fun k v => ∀ j : Fin 8, word64 v j = Spec.SHA512.word (block bs j) (8*k))
    (fun k hk => group_spec N bs k hk))
  intro a ha k hk j
  simpa only [Array.getElem!_Nat_eq] using ha k hk j

#print axioms words_spec
end slhdsa.X86.S512.Parents
