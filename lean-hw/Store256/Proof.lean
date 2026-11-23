import Store256.Write
import Gather512.Memory
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Store
open StoreRust StoreRust.sha256.x86.avx512

def control : Reg512 := fun j => slhdsa.Intel.get ⟨0x00010203,0x04050607,0x08090a0b,0x0c0d0e0f⟩ j.val
abbrev reverse32 := S512.Gather.rev32
theorem shuffle (v : Reg512) :
    StoreRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8 v control ⦃ r =>
      ∀ j, r j = reverse32 (v j) ⦄ := by
  simp only [StoreRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8,
    GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8,step_simps]
  intro j
  fin_cases j <;> rfl

private theorem words (N : Usize) (s : Array Reg512 8#usize) (o : Usize) (ho : o.val ≤ 16) :
    core.array.from_fn 4#usize (write_words.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N)
      (s,o,control) ⦃ a => ∀ k, k < 4 → ∀ j, a.val[k]! j = reverse32 (s.val[o.val/4+k]! j) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 4#usize
    (write_words.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N) _
    (fun k v => ∀ j, v j = reverse32 (s.val[o.val/4+k]! j)) ?_)
  · intro a ha k hk
    simpa only [Array.getElem!_Nat_eq] using ha k hk
  · intro k hk
    change write_words.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut (N := N) (s,o,control) k ⦃ _ _ => _ ⦄
    unfold write_words.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut
    step as ⟨i,hi⟩
    step as ⟨u,hu⟩
    step as ⟨v,hv⟩
    step with shuffle v as ⟨out,hout⟩
    refine ⟨fun j => ?_, rfl⟩
    rw [hout,hv, ← getElem!_pos, hu,hi]

private abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)
private theorem next (it : Iter) (hlt : it.iter.start.val < it.iter.end.val) (hs : it.step_by = 16#usize) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it ⦃ o t =>
      o = some it.iter.start ∧ t.iter.start.val = min (it.iter.start.val+16) it.iter.end.val ∧
      t.iter.end = it.iter.end ∧ t.step_by = it.step_by ⦄ := by
  unfold core.iter.adapters.step_by.IteratorStepBy.next
  step with core.iter.range.IteratorRange.next_Usize_some_spec it.iter hlt as ⟨opt,r,hopt,hstart,hend⟩
  simp only [hopt]
  step with core.iter.adapters.step_by.skipN_Range_Usize_spec r (it.step_by.val-1) (by rw [hend]; omega) (by scalar_tac) as ⟨u,hu,he⟩
  simp [hu,he,hend,hstart,hs,Nat.add_assoc]

def digestByte (s : Array Reg512 8#usize) (j : Fin 16) (k : Nat) :=
  (s.val[k/4]! j).extractLsb' (8*(3-k%4)) 8

private theorem reversed_byte (v : BitVec 32) (k : Nat) :
    (reverse32 v).extractLsb' (8*(k%4)) 8 = v.extractLsb' (8*(3-k%4)) 8 := by
  have h : k%4 < 4 := Nat.mod_lt _ (by decide)
  generalize k%4 = n at *
  interval_cases n <;> unfold reverse32 S512.Gather.rev32 <;> bv_decide

private theorem choose {a : Array Reg512 4#usize} (i : Nat) (hi : i < 4) :
    chooseWord a.val[0]! a.val[1]! a.val[2]! a.val[3]! i = a.val[i]! := by
  interval_cases i <;> rfl

private def Written {N : Usize} (s : Array Reg512 8#usize) (orig out : Slice (Array U8 N)) (n : Nat) :=
  out.length = orig.length ∧ ∀ j : Fin 16, j.val < orig.length → ∀ k, k < n →
    (out.val[j.val]!.val[k]!).bv = digestByte s j k

theorem write_words_spec {N : Usize} (s : Array Reg512 8#usize) (out : Slice (Array U8 N))
    (hn : N.val = 16 ∨ N.val = 24 ∨ N.val = 32) (hl : out.length ≤ 16) :
    write_words s out ⦃ r => r.length = out.length ∧ ∀ j : Fin 16, j.val < out.length →
      ∀ k, k < N.val → (r.val[j.val]!.val[k]!).bv = digestByte s j k ⦄ := by
  change write_words s out ⦃ r => Written s out r N.val ⦄
  unfold write_words
  simp only [core.core_arch.x86.sse2._mm_set_epi32, StoreRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,bind_ok]
  step as ⟨it,hit,hs0⟩
  change write_words_loop0 it s out control ⦃ _ => _ ⦄
  unfold write_words_loop0
  apply loop.spec_decr_nat (measure := fun p : Iter × Slice (Array U8 N) => N.val-p.1.iter.start.val)
    (inv := fun p => p.1.iter.end = N ∧ p.1.step_by = 16#usize ∧ p.1.iter.start.val ≤ N.val ∧
      (p.1.iter.start.val % 16 = 0 ∨ p.1.iter.start = N) ∧ Written s out p.2 p.1.iter.start.val)
  · rintro ⟨it,buf⟩ ⟨he,hs,hb,ha,hlen,hbytes⟩
    simp only at he hs hb ha hlen hbytes
    unfold write_words_loop0.body
    by_cases hlt : it.iter.start.val < it.iter.end.val
    · have hltN : it.iter.start.val < N.val := he ▸ hlt
      have ho : it.iter.start.val ≤ 16 := by rw [he] at hlt; rcases ha with h | h <;> first | omega | simp_all
      have align : it.iter.start.val % 16 = 0 := ha.resolve_right (by intro h; rw [he,h] at hlt; omega)
      step with next it hlt hs as ⟨opt,nxt,hopt,hnx,hend,hstep⟩
      simp only [hopt]
      step with words N s it.iter.start ho as ⟨a,hw⟩
      step as ⟨a0,ha0⟩
      step as ⟨a1,ha1⟩
      step as ⟨a2,ha2⟩
      step as ⟨a3,ha3⟩
      step with transpose_rows_spec a0 a1 a2 a3 as ⟨rows,hrow⟩
      step as ⟨diff,hdiff⟩
      step as ⟨width,hwidth⟩
      simp only [core.slice.Slice.iter_mut,bind_ok]
      have hwid : width.val = min (N.val-it.iter.start.val) 16 := by simp [hwidth,hdiff]
      step with write_rows buf it.iter.start width rows (by omega) (by omega) (by omega) as ⟨im,b,hbl,hwritten⟩
      refine ⟨hend.trans he,hstep.trans hs, by rw [hnx,he]; omega, ?_, ⟨hbl.trans hlen, ?_⟩, by rw [hnx,he]; omega⟩
      · by_cases h : it.iter.start.val+16 ≤ N.val
        · left; rw [hnx,he,Nat.min_eq_left h]; omega
        · right; apply UScalar.eq_of_val_eq; rw [hnx,he]; omega
      · intro j hj k hk
        have hlocal := hwritten j.val (hlen.symm ▸ hj)
        unfold WriteRow at hlocal
        change ((b im).slice.val[j.val]!.val[k]!).bv = _
        rw [hlocal]
        by_cases old : k < it.iter.start.val
        · rw [List.getElem!_setSlice!_prefix _ _ _ _ old]
          exact hbytes j hj k old
        · have hlim : k-it.iter.start.val < width.val := by rw [hnx,he] at hk; omega
          have hpos : k < N.val := by rw [hnx,he] at hk; omega
          have kw : k-it.iter.start.val < 16 := by omega
          rw [List.getElem!_setSlice!_middle _ _ _ _ (by simp; omega)]
          rw [List.getElem!_eq_getElem?_getD,List.getElem?_take_of_lt hlim, ← List.getElem!_eq_getElem?_getD]
          rw [hrow j ⟨_,kw⟩]
          simp only [ha0,ha1,ha2,ha3, ← getElem!_pos]
          rw [choose _ (by omega),hw _ (by omega),reversed_byte]
          unfold digestByte
          rw [show it.iter.start.val/4+(k-it.iter.start.val)/4 = k/4 by omega,
            show (k-it.iter.start.val)%4 = k%4 by omega]
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨opt,it',hopt,hit'⟩
      simp only [hopt,step_simps]
      have eq : it.iter.start.val = N.val := by rw [he] at hlt; omega
      exact ⟨hlen,eq ▸ hbytes⟩
  · simp [hit,hs0,Written]

#print axioms write_words_spec
end slhdsa.X86.Store
