import Wots.Funs
import Chainwide.Counters
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust.core.core_arch.x86.avx512f
open _root_.core.core_arch.x86.avx512f
def slotRegs (lanes : Reg) (first : U32) (atSlot len : Usize) := do
  let slot ← atSlot % len
  let sv ← _mm512_set1_epi32 (UScalar.hcast .I32 slot)
  let chains ← _mm512_add_epi32 lanes sv
  let limit ← _mm512_set1_epi32 (UScalar.hcast .I32 len)
  let cross ← _mm512_cmpge_epi32_mask chains limit
  let offset ← atSlot / len
  let firstKey ← first + UScalar.cast .U32 offset
  let kv ← _mm512_set1_epi32 (UScalar.hcast .I32 firstKey)
  let one ← _mm512_set1_epi32 1#i32
  let keys ← _mm512_mask_add_epi32 kv cross kv one
  let limit ← _mm512_set1_epi32 (UScalar.hcast .I32 len)
  let ids ← _mm512_mask_sub_epi32 chains cross chains limit
  ok (keys,ids)

private theorem small_signed (n : Nat) (h : n < 2^31) : (BitVec.ofNat 32 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp; omega
  · rw [BitVec.msb_eq_decide]
    simp; omega

/-- A 16-lane WOTS batch crosses at most one keypair boundary. -/
theorem slot_components (atSlot len lane : Nat) (lenOK : 16 ≤ len) (laneOK : lane < 16) :
    (atSlot+lane)/len = atSlot/len + (if len ≤ atSlot%len+lane then 1 else 0) ∧
    (atSlot+lane)%len = if len ≤ atSlot%len+lane then atSlot%len+lane-len else atSlot%len+lane := by
  let slot := atSlot%len+lane
  have pos : 0 < len := by omega
  have bounded := Nat.mod_lt atSlot pos
  have twice : slot < len+len := by dsimp [slot]; omega
  have eq : atSlot+lane = slot+len*(atSlot/len) := by
    have h := Nat.mod_add_div atSlot len
    dsimp [slot]; omega
  rw [eq,Nat.add_mul_div_left _ _ pos,Nat.add_mul_mod_self_left]
  change slot / len + atSlot / len = _ ∧ slot % len = _
  by_cases crosses : len ≤ slot
  · have rem : slot-len < len := by omega
    have decomp : slot = (slot-len)+len := by omega
    have d : slot/len = 1 := by rw [decomp,Nat.add_div_right _ pos,Nat.div_eq_of_lt rem]
    have m : slot%len = slot-len := by conv => lhs; rw [decomp,Nat.add_mod_right,Nat.mod_eq_of_lt rem]
    simp only [show len ≤ atSlot%len+lane from crosses,ite_true,d,m]
    omega
  · have small : slot < len := by omega
    simp only [show ¬len ≤ atSlot%len+lane from crosses,ite_false,Nat.div_eq_of_lt small,
      Nat.mod_eq_of_lt small,Nat.zero_add,Nat.add_zero,slot,and_self]

theorem slot_regs_spec (lanes : Reg) (first : U32) (atSlot len : Usize)
    (seqLanes : ∀ j : Fin 16, lanes j = BitVec.ofNat 32 j.val)
    (lenLo : 16 ≤ len.val) (lenHi : len.val ≤ 67)
    (safe : first.val+atSlot.val/len.val < 2^32) :
    slotRegs lanes first atSlot len ⦃ keys chains => ∀ j : Fin 16,
      keys j = BitVec.ofNat 32 (first.val+(atSlot.val+j.val)/len.val) ∧
      chains j = BitVec.ofNat 32 ((atSlot.val+j.val)%len.val) ⦄ := by
  unfold slotRegs
  step as ⟨slot,hslot⟩
  simp only [_mm512_set1_epi32,_mm512_add_epi32,_mm512_cmpge_epi32_mask,bind_ok]
  step as ⟨offset,hoff⟩
  have offsmall : offset.val < 2^32 := by omega
  have castOff : (UScalar.cast .U32 offset).val = offset.val := by scalar_tac
  step as ⟨firstKey,hfirst⟩
  simp only [_mm512_set1_epi32,_mm512_mask_add_epi32,_mm512_mask_sub_epi32,bind_ok,step_simps,Chain.lane_mask]
  intro j
  have slotSmall := Nat.mod_lt atSlot.val (by omega : 0 < len.val)
  have castSlot : (UScalar.hcast .I32 slot).bv = BitVec.ofNat 32 slot.val := by
    rw [UScalar.hcast_bv_eq]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]; rfl
  have castLen : (UScalar.hcast .I32 len).bv = BitVec.ofNat 32 len.val := by
    rw [UScalar.hcast_bv_eq]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]; rfl
  have castKey : (UScalar.hcast .I32 firstKey).bv = BitVec.ofNat 32 firstKey.val := by
    rw [UScalar.hcast_bv_eq]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]; rfl
  have wlen := small_signed len.val (by omega)
  have wslot := small_signed (j.val+slot.val) (by have := j.isLt; omega)
  simp only [seqLanes,castSlot,castLen,castKey,← BitVec.ofNat_add,wlen,wslot,decide_eq_true_eq]
  rw [hslot,hfirst,castOff,hoff]
  obtain ⟨div,mod⟩ := slot_components atSlot.val len.val j.val lenLo j.isLt
  rw [div,mod]
  by_cases cross : len.val ≤ atSlot.val%len.val+j.val
  · simp only [show j.val+atSlot.val%len.val = atSlot.val%len.val+j.val by omega,Nat.cast_le,cross,decide_true,ite_true]
    constructor
    · conv_rhs => rw [← Nat.add_assoc,BitVec.ofNat_add]
      congr 1
    · apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub,BitVec.toNat_ofNat]
      omega
  · simp only [show j.val+atSlot.val%len.val = atSlot.val%len.val+j.val by omega,Nat.cast_le,cross,decide_false,ite_false,Nat.add_zero,and_self]

/-- Both bulk-copy ranges address exactly the keypair and slot computed for each live SIMD lane. -/
theorem destination_spec (atSlot len used j : Nat) (lenLo : 16 ≤ len)
    (hu : used ≤ 16) (hj : j < used) :
    let firstWidth := min used (len-atSlot%len)
    ((atSlot+j)/len,(atSlot+j)%len) =
      if j < firstWidth then (atSlot/len,atSlot%len+j)
      else (atSlot/len+1,j-firstWidth) := by
  have hm := Nat.mod_lt atSlot (by omega : 0 < len)
  obtain ⟨hq,hr⟩ := slot_components atSlot len j lenLo (by omega)
  dsimp only
  rw [hq,hr]
  by_cases h : j < min used (len-atSlot%len)
  · have stays : ¬len ≤ atSlot%len+j := by omega
    simp only [if_neg stays,if_pos h,Nat.add_zero]
  · have cross : len ≤ atSlot%len+j := by omega
    simp only [if_pos cross,if_neg h,Prod.mk.injEq,true_and]
    omega

end slhdsa.X86.Wots
