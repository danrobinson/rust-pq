import Leaf256.Batch
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Leaf
open LeafRust.sha256.x86.avx512
open _root_.core.core_arch.x86.avx512f
open LeafRust.core.core_arch.x86.avx512f
open Spec.SHA256

abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)
abbrev Nodes (N : Usize) := Slice (Array U8 N)

/-- The production loop inlines the batch and then passes its writer the returned slice. -/
def batchK {N : Usize} {α : Type} (base : Array Reg 16#usize) (state prefix_prf prefix_f : Array Reg 8#usize)
    (idx half change : Reg) (batch : Nodes N) (next : Nodes N → Result α) : Result α := do
  let mi1 ← Array.index_usize base 4#usize
  let mi2 ← _mm512_srli_epi32 16#u32 idx
  let mi3 ← _mm512_or_si512 mi1 mi2
  let base1 ← Array.update base 4#usize mi3
  let high ← _mm512_slli_epi32 16#u32 idx
  let mi4 ← Array.index_usize base1 5#usize
  let mi5 ← _mm512_and_si512 mi4 half
  let mi6 ← _mm512_or_si512 high mi5
  let base2 ← Array.update base1 5#usize mi6
  let prf ← LeafRust.sha256.x86.avx512.compress state prefix_prf base2
  let mi7 ← Array.index_usize base2 2#usize
  let mi8 ← _mm512_xor_si512 mi7 change
  let base3 ← Array.update base2 2#usize mi8
  let mi9 ← Array.index_usize prf 0#usize
  let mi10 ← _mm512_srli_epi32 16#u32 mi9
  let mi11 ← _mm512_or_si512 high mi10
  let a ← Array.update base3 5#usize mi11
  let i6 ← N / 4#usize
  let w ←
    LeafRust.sha256.x86.avx512.fors_leaves_loop1_loop0
    { start := 1#usize, «end» := i6 } a prf
  let i7 ← i6 - 1#usize
  let mi12 ← Array.index_usize prf i7
  let mi13 ← _mm512_slli_epi32 16#u32 mi12
  let i8 ← 5#usize + i6
  let mi14 ← Array.index_usize w i8
  let mi15 ← _mm512_and_si512 mi14 half
  let mi16 ← _mm512_or_si512 mi13 mi15
  let i9 ← 5#usize + i6
  let w1 ← Array.update w i9 mi16
  let leaf ← LeafRust.sha256.x86.avx512.compress state prefix_f w1
  let batch1 ← LeafRust.sha256.x86.avx512.write_words leaf batch
  next batch1

theorem batchK_eq {N : Usize} {α : Type} (base : Array Reg 16#usize) (state pp pf : Array Reg 8#usize)
    (idx half change : Reg) (batch : Nodes N) (next : Nodes N → Result α) :
    batchK base state pp pf idx half change batch next =
      (hashBatch base state pp pf idx half change batch >>= next) := by
  unfold batchK hashBatch prfMessage leafMessage
  simp only [bind_tc_eq,Std.bind_assoc,bind_ok]

abbrev VecState := Array Reg 8#usize
abbrev VecBlock := Array Reg 16#usize

def computed (s : VecState) (base : VecBlock) (first : U32) (change : Reg)
    (n off lane k : Nat) (j : Fin 16) :=
  ((leafDigest (stateWords (laneState s j)) (laneWords base j) (BitVec.ofNat 32 (first.val+off+lane))
    (change j) n)[k/4]!).extractLsb' (8*(3-k%4)) 8

def Processed {N : Usize} (s : VecState) (base : VecBlock) (first : U32) (change : Reg)
    (before after : Nodes N) (done : Nat) := after.length = before.length ∧
    ∀ k, k < before.length → if k < done then
      ∀ i, i < N.val → (after.val[k]!.val[i]!).bv =
        computed s base first change N.val (k/16*16) (k%16) i ⟨k%16,by omega⟩
      else after.val[k]! = before.val[k]!

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

theorem batches_spec {N : Usize} (first : U32) (base : VecBlock) (s pp pf : VecState)
    (change : Reg) (out : Nodes N) (hn : N.val = 16 ∨ N.val = 24 ∨ N.val = 32)
    (bound : first.val + out.length ≤ 2^32)
    (hp : Trace pp (fun j => schedule (blockOf (laneWords base j))) (laneState s) 4)
    (hf : Trace pf (fun j => schedule (blockOf (withType (laneWords base j) (change j)))) (laneState s) 4) :
    fors_leaves_loop1 ⟨⟨0#usize,out.len⟩,16#usize⟩ first out base s change pp pf
      (fun j => BitVec.ofNat 32 j.val) (fun _ => 0xffff) ⦃ r => Processed s base first change out r out.length ⦄ := by
  unfold fors_leaves_loop1
  apply loop.spec_decr_nat (measure := fun p : Iter × Nodes N => out.length-p.1.iter.start.val)
    (inv := fun p => p.1.iter.end = out.len ∧ p.1.step_by = 16#usize ∧ p.1.iter.start.val ≤ out.length ∧
      (p.1.iter.start.val%16 = 0 ∨ p.1.iter.start.val = out.length) ∧
      Processed s base first change out p.2 p.1.iter.start.val)
  · rintro ⟨it,buf⟩ ⟨he,hs,hle,ha,hlen,hr⟩
    simp only at he hs hle ha hlen hr
    unfold fors_leaves_loop1.body
    by_cases hlt : it.iter.start.val < it.iter.end.val
    · have lt : it.iter.start.val < out.length := by rw [he] at hlt; exact hlt
      have align : it.iter.start.val%16 = 0 := ha.resolve_right (by omega)
      step with next it hlt hs as ⟨o,t,ho,ht,hend,hstep⟩
      simp only [ho,lift,bind_ok,_mm512_set1_epi32,_mm512_add_epi32]
      step as ⟨diff,hdiff⟩
      step as ⟨stop,hstop⟩
      step as ⟨dst,back,hbuf,hl,hback⟩
      step as ⟨pos,hpos⟩
      let idx : Reg := fun j => BitVec.ofNat 32 j.val + pos.bv
      change batchK base s pp pf idx (fun _ => 0xffff) change dst (fun r => ok (cont (t,back r))) ⦃ _ => _ ⦄
      rw [batchK_eq]
      have stopval : stop.val = min (it.iter.start.val+16) out.length := by
        change diff.val = buf.length-it.iter.start.val at hdiff
        rw [hstop,show (core.cmp.impls.OrdUsize.min diff 16#usize).val = min diff.val 16 by simp]
        omega
      have advance : t.iter.start.val = stop.val := by rw [ht,he,stopval]; rfl
      step with hash_batch_spec base s pp pf idx change dst hn (by omega) hp hf as ⟨r,len,hash⟩
      have posval : pos.val = first.val+it.iter.start.val := by
        rw [hpos,UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change it.iter.start.val < 2^32; omega)]
      refine ⟨hend.trans he,hstep.trans hs,by omega,?_,⟨?_,?_⟩,by omega⟩
      · by_cases b : it.iter.start.val+16 ≤ out.length
        · left; rw [advance,stopval,Nat.min_eq_left b]; omega
        · right; omega
      · simp only [Slice.length,hback,Slice.setSlice!_val,List.length_setSlice!]; exact hlen
      · intro k hk
        by_cases early : k < it.iter.start.val
        · simp only [if_pos (show k < t.iter.start.val by omega),hback,Slice.setSlice!_val,
            List.getElem!_setSlice!_prefix _ _ _ _ early]
          simpa only [if_pos early] using hr k hk
        · by_cases active : k < t.iter.start.val
          · simp only [if_pos active,hback,Slice.setSlice!_val]
            rw [List.getElem!_setSlice!_middle _ _ _ _ (by change it.iter.start.val ≤ k ∧ k-it.iter.start.val < r.length ∧ k < buf.length; omega)]
            let j : Fin 16 := ⟨k-it.iter.start.val,by omega⟩
            have jval : j.val = k%16 := by dsimp [j]; omega
            have jeq : j = ⟨k%16,by omega⟩ := Fin.ext jval
            have ix : idx j = BitVec.ofNat 32 (first.val + k/16*16 + k%16) := by
              change BitVec.ofNat 32 j.val + pos.bv = _
              rw [show pos.bv = BitVec.ofNat 32 pos.val by simp,← BitVec.ofNat_add,posval,jval]
              congr 1; omega
            intro i hi
            have ht' := hash j (by change k-it.iter.start.val < dst.length; omega) i hi
            change (r.val[j.val]!.val[i]!).bv = _
            rw [ht']
            change ((leafDigest (stateWords (laneState s j)) (laneWords base j) (idx j) (change j) N.val)[i/4]!).extractLsb' _ _ = _
            rw [ix,jeq]
            rfl
          · simp only [if_neg active,hback,Slice.setSlice!_val]
            rw [List.getElem!_setSlice!_suffix _ _ _ _ (by change it.iter.start.val+r.length ≤ k; omega)]
            simpa only [if_neg early] using hr k hk
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨o,t,ho,ht⟩
      simp only [ho,step_simps]
      have eq : it.iter.start.val = out.length := by rw [he] at hlt; change ¬it.iter.start.val < out.length at hlt; omega
      exact ⟨hlen,eq ▸ hr⟩
  · simp [Processed]

end slhdsa.X86.Leaf
