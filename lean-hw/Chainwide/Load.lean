import Chainwide.Counters
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 1600000
namespace slhdsa.X86.Chain
open ChainWideRust
open DigestRust.core.core_arch.x86 (little)

private abbrev encoded (xs : List U32) := xs.flatMap MemoryElement.encode

private theorem size (xs : List U32) : (encoded xs).length = 4*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change ((a.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))) ++ encoded xs).length = _
    simp [ih,Nat.mul_add,Nat.add_comm]

private theorem byte_at (xs : List U32) (i n : Nat) (hi : i < xs.length) (hn : n < 4) :
    (encoded xs)[4*i+n]! = (MemoryElement.encode xs[i]!)[n]! := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    have len : (MemoryElement.encode a).length = 4 := by change (a.bv.toLEBytes.map _).length = 4; simp
    cases i with
    | zero =>
      change (MemoryElement.encode a ++ encoded xs)[4*0+n]! = (MemoryElement.encode a)[n]!
      simp only [Nat.mul_zero,Nat.zero_add,List.getElem!_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    | succ i =>
      change (MemoryElement.encode a ++ encoded xs)[4*(i+1)+n]! = (MemoryElement.encode xs[i]!)[n]!
      rw [← ih i (by simpa using hi)]
      simp only [List.getElem!_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega),len,show 4*(i+1)+n-4 = 4*i+n by omega]

private theorem roundtrip (x : U32) : little (MemoryElement.encode x) 0 = x.bv := by
  change little (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))) 0 = x.bv
  generalize x.bv = w
  simp (disch := simp) only [little,Nat.reduceAdd,getElem!_pos,List.getElem_map]
  simp [BitVec.toLEBytes]
  bv_decide

private theorem word_at (xs : List U32) (i : Nat) (hi : i < xs.length) :
    little (encoded xs) (4*i) = xs[i]!.bv := by
  rw [← roundtrip xs[i]!]
  unfold little
  simp (disch := decide) only [byte_at xs i _ hi,Nat.zero_add]
  rw [← Nat.add_zero (4*i),byte_at xs i 0 hi (by decide)]

theorem packed_u32 (xs : List U32) :
    (xs.flatMap MemoryElement.encode).length = 4*xs.length ∧
      ∀ i < xs.length, little (xs.flatMap MemoryElement.encode) (4*i) = xs[i]!.bv :=
  ⟨size xs,word_at xs⟩

def loadCounters (xs : Slice U32) (off : Usize) (mask : U16) : Result Reg := do
  let base ← ChainWideRust.core.slice.Slice.as_ptr xs
  let ptr ← ChainWideRust.core.ptr.const_ptr.RawPtrConstT.add base off
  let p ← ChainWideRust.core.ptr.const_ptr.RawPtrConstT.cast I32 ptr
  ChainWideRust.core.core_arch.x86.avx512f._mm512_maskz_loadu_epi32 mask p

theorem load_counters_spec (xs : Slice U32) (off : Usize) (mask : U16)
    (ho : off.val ≤ xs.length) (enabled : ∀ j : Fin 16, mask.bv.getLsbD j.val → off.val+j.val < xs.length) :
    loadCounters xs off mask ⦃ r => ∀ j : Fin 16,
      r j = if mask.bv.getLsbD j.val then xs.val[off.val+j.val]!.bv else 0 ⦄ := by
  have bound : off.val*4 ≤ (encoded xs.val).length := by rw [size]; change off.val*4 ≤ 4*xs.length; omega
  have safe (j : Fin 16) (h : mask.bv.getLsbD j.val = true) : off.val*4+4*j.val+4 ≤ (encoded xs.val).length := by
    rw [size]; have := enabled j h; change _ ≤ 4*xs.length; omega
  have eq : loadCounters xs off mask = ok (fun j : Fin 16 =>
      if mask.bv.getLsbD j.val then little (encoded xs.val) (off.val*4+4*j.val) else 0) := by
    have add : ChainWideRust.core.ptr.const_ptr.RawPtrConstT.add
        (⟨encoded xs.val,0⟩ : GatherRust.ReadPtr U32) off = ok ⟨encoded xs.val,off.val*4⟩ := by
      change (if 0+off.val*4 ≤ (encoded xs.val).length then ok _ else fail .undef) = _
      rw [if_pos (by omega)]
      simp only [Nat.zero_add]
      rfl
    have load : ChainWideRust.core.core_arch.x86.avx512f._mm512_maskz_loadu_epi32 mask
        (⟨encoded xs.val,off.val*4⟩ : GatherRust.ReadPtr I32) = ok (fun j : Fin 16 =>
        if mask.bv.getLsbD j.val then little (encoded xs.val) (off.val*4+4*j.val) else 0) := by
      unfold ChainWideRust.core.core_arch.x86.avx512f._mm512_maskz_loadu_epi32
      rw [if_pos safe]
    have base : ChainWideRust.core.slice.Slice.as_ptr xs = ok (⟨encoded xs.val,0⟩ : GatherRust.ReadPtr U32) := rfl
    have cast : ChainWideRust.core.ptr.const_ptr.RawPtrConstT.cast I32 (⟨encoded xs.val,off.val*4⟩ : GatherRust.ReadPtr U32) =
        ok (⟨encoded xs.val,off.val*4⟩ : GatherRust.ReadPtr I32) := rfl
    simp only [loadCounters,base,bind_ok,add,cast,load]
  rw [eq]
  simp only [step_simps]
  intro j
  split <;> rename_i h
  · rw [show off.val*4+4*j.val = 4*(off.val+j.val) by omega,word_at xs.val _ (enabled j h)]
  · rfl
end slhdsa.X86.Chain
