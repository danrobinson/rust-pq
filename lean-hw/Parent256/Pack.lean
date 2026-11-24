import Parent256.Gather
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Parent
open S512.Gather (flat flat_length)
open TreeRust.sha256.x86.avx512
open TreeRust.core
open _root_.core.core_arch.x86

def readChild (rows : Slice (Array U8 16#usize)) (stride : Reg) (start k : Usize) (mask : U16) := do
  let p ← TreeRust.core.slice.Slice.as_ptr rows
  let p1 ← ptr.const_ptr.RawPtrConstT.cast U8 p
  let i ← 32#usize * start
  let i1 ← 4#usize * k
  let i2 ← i + i1
  let ptr ← ptr.const_ptr.RawPtrConstT.add p1 i2
  let mi ← TreeRust.core.core_arch.x86.avx512f._mm512_setzero_si512
  let p2 ← TreeRust.core.ptr.const_ptr.RawPtrConstT.cast I32 ptr
  let input ← TreeRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32 4#i32 mi mask stride p2
  TreeRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8 input Store.control

def sourceWord (rows : Slice (Array U8 16#usize)) (start count k : Nat) (j : Fin 16) :=
  if j.val < count then childWord rows (start+j.val) k else 0

theorem read_child (rows : Slice (Array U8 16#usize)) (stride : Reg) (start k : Usize) (mask : U16)
    (count : Nat) (hm : Digest.Mask mask count) (hs : Digest.Stride stride 32) (hk : k.val < 8)
    (hn : 0 < count) (bound : 2*(start.val+count) ≤ rows.length)
    (size : 32*(start.val+count) ≤ Usize.max) :
    readChild rows stride start k mask ⦃ word => ∀ j, word j = sourceWord rows start.val count k.val j ⦄ := by
  unfold readChild
  simp only [TreeRust.core.slice.Slice.as_ptr, GatherRust.core.slice.Slice.as_ptr,
    TreeRust.core.ptr.const_ptr.RawPtrConstT.cast, GatherRust.core.ptr.const_ptr.RawPtrConstT.cast]
  step as ⟨i,hi⟩
  step as ⟨off,hoff⟩
  step as ⟨at',hat⟩
  have eq : at'.val = 32*start.val+4*k.val := by scalar_tac
  have hb : at'.val ≤ (flat rows.val).length := by
    rw [flat_length]
    change _ ≤ rows.val.length*16
    change 2*(start.val+count) ≤ rows.val.length at bound
    omega
  unfold flat at hb
  simp only [TreeRust.core.ptr.const_ptr.RawPtrConstT.add, GatherRust.core.ptr.const_ptr.RawPtrConstT.add,
    Nat.zero_add, TreeRust.core.core_arch.x86.avx512f._mm512_setzero_si512,
    DigestRust.core.core_arch.x86.avx512f._mm512_setzero_si512,
    GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512]
  rw [if_pos hb]
  simp only [bind_tc_eq,bind_ok,eq]
  exact shuffled_pairs rows start.val k.val count mask stride hm hs hk bound

private def storeChild (next : core.ops.range.Range Usize) (k : Usize)
    (w : Array Reg 16#usize) (high word : Reg) :
    Result (ControlFlow (core.ops.range.Range Usize × Array Reg 16#usize × Reg) (Array Reg 16#usize × Reg)) := do
  let low ← _root_.core.core_arch.x86.avx512f._mm512_srli_epi32 16#u32 word
  let merged ← TreeRust.core.core_arch.x86.avx512f._mm512_or_si512 high low
  let pos ← 5#usize + k
  let dst ← Array.update w pos merged
  let carry ← TreeRust.core.core_arch.x86.avx512f._mm512_slli_epi32 16#u32 word
  ok (cont (next,dst,carry))

theorem pack_children (rows : Slice (Array U8 16#usize)) (stride : Reg) (start : Usize) (mask : U16)
    (count : Nat) (hm : Digest.Mask mask count) (hs : Digest.Stride stride 32)
    (hn : 0 < count) (bound : 2*(start.val+count) ≤ rows.length)
    (size : 32*(start.val+count) ≤ Usize.max) (w : Array Reg 16#usize) (high : Reg) :
    let word := sourceWord rows start.val count
    let carry := fun k j => if k = 0 then high j else word (k-1) j <<< 16
    fors_parents_loop1_loop0 ⟨0#usize,8#usize⟩ rows stride Store.control start mask w high
      ⦃ out last => (∀ i, i < 16 → ∀ j, out.val[i]! j =
        if 5 ≤ i ∧ i < 13 then carry (i-5) j ||| (word (i-5) j >>> 16) else w.val[i]! j) ∧
        ∀ j, last j = carry 8 j ⦄ := by
  intro word carry
  unfold fors_parents_loop1_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array Reg 16#usize × Reg =>
    8-p.1.start.val)
    (inv := fun p => p.1.end = 8#usize ∧ p.1.start.val ≤ 8 ∧
      (∀ i, i < 16 → ∀ j, p.2.1.val[i]! j = if 5 ≤ i ∧ i < 5+p.1.start.val then
        carry (i-5) j ||| (word (i-5) j >>> 16) else w.val[i]! j) ∧
      ∀ j, p.2.2 j = carry p.1.start.val j)
  · rintro ⟨it,arr,prev⟩ ⟨he,hi,ha,hp⟩
    simp only at he hi ha hp
    unfold fors_parents_loop1_loop0.body
    by_cases lt : it.start.val < it.end.val
    · have hk : it.start.val < 8 := by rw [he] at lt; exact lt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,next,ho,hnxt,hend⟩
      simp only [ho]
      conv => lhs; equals (readChild rows stride start it.start mask >>= storeChild next it.start arr prev) =>
        unfold readChild storeChild
        simp only [bind_tc_eq,Std.bind_assoc]
      apply WP.spec_bind (read_child rows stride start it.start mask count hm hs hk hn bound size)
      intro src hsrc
      unfold storeChild
      simp only [_root_.core.core_arch.x86.avx512f._mm512_srli_epi32,
        TreeRust.core.core_arch.x86.avx512f._mm512_or_si512, LeafRust.core.core_arch.x86.avx512f._mm512_or_si512,
        TreeRust.core.core_arch.x86.avx512f._mm512_slli_epi32, LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,bind_ok]
      step*
      refine ⟨hend.trans he,by omega,?_,?_,by omega⟩
      · intro i hb j
        rw [dst_post,Array.set_val_eq]
        by_cases hx : i = 5+it.start.val
        · subst i
          rw [show 5+it.start.val = pos.val by omega, Avx2.setSame _ _ _ (by scalar_tac),if_pos (by omega)]
          simp only [hp,hsrc,show pos.val-5 = it.start.val by omega]
          rfl
        · rw [Avx2.setOther _ _ _ _ (by omega),ha i hb j]
          split_ifs <;> first | rfl | omega
      · intro j
        simp only [carry,show next.start.val ≠ 0 by omega,↓reduceIte,show next.start.val-1=it.start.val by omega,hsrc]
        rfl
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,hend⟩
      simp only [ho,step_simps]
      have eq : it.start.val = 8 := by rw [he] at lt; change ¬ it.start.val < 8 at lt; omega
      rw [eq] at ha hp
      exact ⟨ha,hp⟩
  · simp [carry]

end slhdsa.X86.Parent
