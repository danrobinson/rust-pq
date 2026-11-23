import Wots.Refill
import Chainwide.Load
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.core.core_arch.x86.avx512f
open DigestRust.core.core_arch.x86 (little address)
open WotsRust.sha256.x86.avx512

def loadLanes (v : LaneArray) := do
  let p ← WotsRust.core.slice.Slice.as_ptr (Array.to_slice v)
  let q ← WotsRust.core.ptr.const_ptr.RawPtrConstT.cast _root_.core.core_arch.x86.__m512i p
  _mm512_loadu_si512 q

theorem load_lanes_spec (v : LaneArray) :
    loadLanes v ⦃ reg => ∀ j : Fin 16, reg j = v.val[j.val]!.bv ⦄ := by
  let xs := v.val.map (fun x => (⟨x.bv⟩ : U32))
  let mem := v.val.flatMap ChainWideRust.MemoryElement.encode
  have eq : mem = xs.flatMap ChainWideRust.MemoryElement.encode := by
    simp only [mem,xs,List.flatMap_map]; rfl
  obtain ⟨size,words⟩ := Chain.packed_u32 xs
  have length : mem.length = 64 := by rw [eq,size]; simp [xs]
  unfold loadLanes
  simp only [WotsRust.core.slice.Slice.as_ptr,ChainWideRust.core.slice.Slice.as_ptr,
    Array.val_to_slice,WotsRust.core.ptr.const_ptr.RawPtrConstT.cast,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,bind_tc_eq,bind_ok]
  change _mm512_loadu_si512 ⟨mem,0⟩ ⦃ _ ⦄
  simp only [_mm512_loadu_si512,Nat.zero_add,length,le_refl,ite_true,step_simps]
  intro j
  rw [eq,words _ (by simp [xs])]
  simp (disch := simp) only [xs,getElem!_pos,List.getElem_map]

theorem signature_gather (sig : Slice U8) (pos : Nat) (src offsets : Reg) (mask : U16)
    (base : Fin 16 → Nat)
    (ranges : ∀ j, enabled mask j = true → (offsets j).toInt = (base j : Int) ∧ base j+pos+4 ≤ sig.length) :
    _mm512_mask_i32gather_epi32 1#i32 src mask offsets ⟨sig.val,pos⟩ ⦃ out =>
      ∀ j, out j = if enabled mask j then little sig.val (base j+pos) else src j ⦄ := by
  let p : GatherRust.ReadPtr I32 := ⟨sig.val,pos⟩
  have addr (j) (h : enabled mask j = true) : address p 1#i32 offsets j = (base j+pos : Nat) := by
    change (pos : Int) + 1 * (offsets j).toInt = _
    rw [(ranges j h).1]; omega
  have safe (j : Fin 16) (h : mask.bv.getLsbD j.val = true) :
      0 ≤ address p 1#i32 offsets j ∧ address p 1#i32 offsets j+4 ≤ (p.allocation.length : Int) := by
    rw [addr j h]
    have bound := (ranges j h).2
    change _ ∧ _ ≤ (sig.length : Int); omega
  change DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32 _ _ _ _ p ⦃ _ ⦄
  unfold DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
  rw [if_pos ⟨by decide,safe⟩]
  simp only [step_simps]
  intro j
  by_cases h : enabled mask j = true
  · rw [if_pos h,addr j h,Int.toNat_natCast]; change (if enabled mask j then _ else _) = _; rw [if_pos h]
  · rw [if_neg h]; change (if enabled mask j then _ else _) = _; rw [if_neg h]


theorem signature_words (sig : Slice U8) (src offsets : Reg) (mask : U16) (limit : Usize)
    (initial : Hash) (base : Fin 16 → Nat) (size : limit.val ≤ 8)
    (ptr : 4*limit.val ≤ sig.length)
    (safe : ∀ j, enabled mask j = true → (offsets j).toInt = (base j : Int) ∧ base j+4*limit.val ≤ sig.length) :
    recover_loop5_loop1 src ⟨0#usize,limit⟩ sig Store.control initial mask offsets ⦃ hash =>
      ∀ k < 8, ∀ j : Fin 16, hash.val[k]! j =
        if k < limit.val ∧ enabled mask j then Spec.SHA256.word (bytes sig.val) (base j+4*k)
        else initial.val[k]! j ⦄ := by
  unfold recover_loop5_loop1
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Hash => limit.val-p.1.start.val)
    (inv := fun p => p.1.end = limit ∧ p.1.start.val ≤ limit.val ∧ ∀ k < 8, ∀ j : Fin 16,
      p.2.val[k]! j = if k < p.1.start.val ∧ enabled mask j then Spec.SHA256.word (bytes sig.val) (base j+4*k)
        else initial.val[k]! j)
  · rintro ⟨it,h⟩ ⟨he,hi,prior⟩
    simp only at he hi prior
    unfold recover_loop5_loop1.body
    by_cases live : it.start.val < limit.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rwa [he]) as ⟨o,t,ho,hn,he'⟩
      simp only [ho,WotsRust.core.slice.Slice.as_ptr,ChainWideRust.core.slice.Slice.as_ptr,bind_ok]
      step as ⟨pos,hpos⟩
      have off : pos.val = 4*it.start.val := by scalar_tac
      have alloc : sig.val.flatMap ChainWideRust.MemoryElement.encode = sig.val := by
        change sig.val.flatMap (fun v => [v]) = _; simp
      have bound : pos.val ≤ sig.val.length := by change pos.val ≤ sig.length; omega
      simp only [WotsRust.core.ptr.const_ptr.RawPtrConstT.add,ChainWideRust.core.ptr.const_ptr.RawPtrConstT.add,
        alloc,show ChainWideRust.MemoryElement.width U8 = 1 by rfl,Nat.mul_one,Nat.zero_add,if_pos bound,bind_ok,
        WotsRust.core.ptr.const_ptr.RawPtrConstT.cast,GatherRust.core.ptr.const_ptr.RawPtrConstT.cast]
      have valid (j) (hj : enabled mask j = true) :
          (offsets j).toInt = (base j : Int) ∧ base j + pos.val + 4 ≤ sig.length := by
        obtain ⟨eq,room⟩ := safe j hj; exact ⟨eq,by omega⟩
      step with signature_gather sig pos.val src offsets mask base valid as ⟨read,hread⟩
      step as ⟨old,hold⟩
      step with Store.shuffle read as ⟨swapped,hs⟩
      simp only [WotsRust.core.core_arch.x86.avx512f._mm512_mask_mov_epi32,
        ChainVectorRust.core.core_arch.x86.avx512f._mm512_mask_mov_epi32,bind_ok]
      step as ⟨result,hr⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro k hk j
      rw [hr,Array.set_val_eq]
      by_cases same : it.start.val=k
      · subst k; rw [Avx2.setSame _ _ _ (by simp; omega)]
        change (if enabled mask j then swapped j else old j) = _
        by_cases active : enabled mask j = true
        · rw [if_pos active,hs,hread,if_pos active,Digest.big_after_little _ _ (valid j active).2,
            if_pos ⟨by omega,active⟩,off]
        · rw [if_neg active,hold,← getElem!_pos,prior _ (by omega),if_neg (by simp),if_neg (fun h => active h.2)]
      · rw [Avx2.setOther _ _ _ _ same,prior k hk]
        have eq : k < t.start.val ↔ k < it.start.val := by omega
        simp only [eq]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; omega) as ⟨o,t,ho,_⟩
      simp only [ho,step_simps]
      simpa only [show it.start.val=limit.val by omega] using prior
  · simp

/-- Charon emits separate copies when the outer loop begins with no active lanes. -/
theorem refill_empty_branch : recover_loop5_loop6 = recover_loop5_loop0 := rfl

theorem gather_empty_branch : recover_loop5_loop7 = recover_loop5_loop1 := rfl

end slhdsa.X86.Wots
