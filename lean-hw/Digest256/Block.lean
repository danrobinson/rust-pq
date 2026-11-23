import Digest256.Read
import Slhdsa.Proofs.Platform
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Digest
open DigestRust.sha256.x86.avx512
open _root_.core.core_arch.x86

def laneBlock {L : Usize} (rows : Slice (Array U8 L)) (j : Fin 16) (off : Nat) :=
  if j.val < rows.length then (bytes rows.val[j.val]!.val).slice off (off+64) else []

theorem word_at {L : Usize} (rows : Slice (Array U8 L)) (j : Fin 16) (off k : Nat)
    (hoff : off+64 ≤ L.val) (hk : k < 16) :
    laneWord rows j (off+4*k) = Spec.SHA256.word (laneBlock rows j off) (4*k) := by
  unfold laneWord laneBlock
  split
  · have len : (bytes rows.val[j.val]!.val).length = L.val := by simp
    have get (t : Nat) (ht : t < 64) :=
      List.getElem!_slice off (off+64) t (bytes rows.val[j.val]!.val) (by omega)
    simp (disch := omega) only [Spec.SHA256.word,get,Nat.add_assoc]
  · simp [Spec.SHA256.word,List.getElem!_eq_getElem?_getD]; rfl

theorem words_spec (N L : Usize) (rows : Slice (Array U8 L)) (mask : U16) (stride : __m512i) (off : Usize)
    (hm : Mask mask rows.length) (hs : Stride stride L.val) (hn : 0 < rows.length) (hoff : off.val+64 ≤ L.val) :
    core.array.from_fn 16#usize (key_digests.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N L)
      (mask,stride,rows,off,Store.control) ⦃ w => ∀ k, k < 16 → ∀ j : Fin 16,
        w.val[k]! j = Spec.SHA256.word (laneBlock rows j off.val) (4*k) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize
    (key_digests.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N L) _
    (fun k v => ∀ j : Fin 16, v j = laneWord rows j (off.val+4*k))
    (fun k hk => read_spec N L rows mask stride off k hm hs hn hk hoff))
  intro a ha k hk j
  simpa only [Array.getElem!_Nat_eq, word_at _ _ _ _ hoff hk] using ha k hk j

private theorem constants : ∀ i : Fin 64, (DigestRust.sha256.K.val[i.val]!).bv = Spec.SHA256.K[i.val]! := by
  unfold DigestRust.sha256.K Spec.SHA256.K
  decide

theorem first_four (iv : Array Reg 8#usize) (w : Array Reg 16#usize) (blocks : Fin 16 → Spec.Bytes)
    (hw : ∀ k, k < 4 → ∀ j, w.val[k]! j = Spec.SHA256.word (blocks j) (4*k)) :
    key_digests_loop0_loop0 ⟨0#usize,4#usize⟩ w iv ⦃ s =>
      Trace s (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) 4 ⦄ := by
  unfold key_digests_loop0_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array Reg 8#usize => 4-p.1.start.val)
    (inv := fun p => p.1.end = 4#usize ∧ p.1.start.val ≤ 4 ∧
      Trace p.2 (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) p.1.start.val)
  · rintro ⟨it,s⟩ ⟨he,hi,ht⟩
    simp only at he hi ht
    unfold key_digests_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · have hsmall : it.start.val < 4 := by rw [he] at hlt; exact hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨opt,nxt,hopt,hn,hen⟩
      simp only [hopt]
      step as ⟨v,hv⟩
      step as ⟨c,hc⟩
      have hconst := constants ⟨it.start.val,by omega⟩
      step with round_spec s v c (fun j => Spec.SHA256.schedule (blocks j)) it.start.val
        (by simpa only [hc,← getElem!_pos] using hconst)
        (fun j => by rw [hv, ← getElem!_pos, hw _ (by omega), slhdsa.schedule_lt16 _ _ (by omega)]) as ⟨s',hs⟩
      refine ⟨hen.trans he, by omega, fun j => ?_, by omega⟩
      rw [hs,ht,hn,List.range_succ,List.foldl_append]; rfl
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨opt,nxt,hopt,hn⟩
      simp only [hopt,step_simps]
      have h : it.start.val = 4 := by rw [he] at hlt; change ¬it.start.val < 4 at hlt; omega
      exact h ▸ ht
  · simp [Trace]

end slhdsa.X86.Digest
