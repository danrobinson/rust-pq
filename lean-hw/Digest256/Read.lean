import Store256.Proof
import Gather512.Rows
import Digest256.Funs
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Digest
open S512.Gather (flat flat_length flat_byte)
open DigestRust.core.core_arch.x86
open _root_.core.core_arch.x86
open DigestRust.sha256.x86.avx512

def active (mask : U16) (j : Fin 16) := mask.bv.getLsbD j.val
def Mask (mask : U16) (n : Nat) := ∀ j : Fin 16, active mask j = true ↔ j.val < n
def Stride (v : __m512i) (L : Nat) := ∀ j : Fin 16, (v j).toInt * 4 = (j.val*L : Nat)

private theorem big_after_little (a : List U8) (pos : Nat) (h : pos+4 ≤ a.length) :
    Store.reverse32 (little a pos) = Spec.SHA256.word (bytes a) pos := by
  unfold little Spec.SHA256.word
  repeat rw [bytes_getElem! _ _ (by omega)]
  simp (disch := omega) only [← getElem!_pos]
  generalize a[pos]! = b0
  generalize a[pos+1]! = b1
  generalize a[pos+2]! = b2
  generalize a[pos+3]! = b3
  unfold Store.reverse32 S512.Gather.rev32
  bv_decide

private theorem flat_word {L : Usize} (rows : List (Array U8 L)) (j off : Nat) (hj : j < rows.length) (ho : off+4 ≤ L.val) :
    Spec.SHA256.word (bytes (flat rows)) (j*L.val+off) = Spec.SHA256.word (bytes rows[j]!.val) off := by
  unfold Spec.SHA256.word
  have hlen : j*L.val+off+4 ≤ (flat rows).length := by
    rw [flat_length]
    calc
      _ ≤ (j+1)*L.val := by rw [Nat.add_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hj
  repeat rw [bytes_getElem! _ _ (by scalar_tac)]
  simp (disch := scalar_tac) only [← getElem!_pos, Nat.add_assoc, flat_byte]

theorem gather_spec {L : Usize} (rows : Slice (Array U8 L)) (pos : Nat)
    (mask : U16) (v : __m512i) (hm : Mask mask rows.length) (hs : Stride v L.val) (hp : pos+4 ≤ L.val) :
    DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32 4#i32 (fun _ => 0) mask v
      ⟨flat rows.val,pos⟩ ⦃ out => ∀ j,
        out j = if active mask j then little (flat rows.val) (j.val*L.val+pos) else 0 ⦄ := by
  let p : GatherRust.ReadPtr I32 := ⟨flat rows.val,pos⟩
  have ea (j : Fin 16) : address p 4#i32 v j = (j.val*L.val+pos : Nat) := by
    change (pos : Int) + 4*(v j).toInt = _
    rw [Int.mul_comm, hs j]
    omega
  have range (j : Fin 16) (h : mask.bv.getLsbD j.val = true) :
      0 ≤ address p 4#i32 v j ∧ address p 4#i32 v j + 4 ≤ (p.allocation.length : Int) := by
    have bound := (hm j).1 h
    have hbound : (j.val+1)*L.val ≤ rows.val.length*L.val := Nat.mul_le_mul_right _ bound
    rw [Nat.add_mul, Nat.one_mul] at hbound
    rw [ea]
    change _ ∧ _ ≤ ((flat rows.val).length : Int)
    rw [flat_length]
    omega
  change DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32 _ _ _ _ p ⦃ _ => _ ⦄
  unfold DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
  rw [if_pos ⟨by decide,range⟩]
  simp only [step_simps]
  intro j
  rw [ea, Int.toNat_natCast]
  rfl

def laneWord {L : Usize} (rows : Slice (Array U8 L)) (j : Fin 16) (pos : Nat) :=
  if j.val < rows.length then Spec.SHA256.word (bytes rows.val[j.val]!.val) pos else 0

/-- The actual closure used by array::from_fn reads one big-endian SHA-256 word per
active key; disabled lanes produce zero without a memory access. -/
theorem read_spec (N L : Usize) (rows : Slice (Array U8 L)) (mask : U16) (v : __m512i) (off k : Usize)
    (hm : Mask mask rows.length) (hs : Stride v L.val) (hn : 0 < rows.length)
    (hk : k.val < 16) (hoff : off.val + 64 ≤ L.val) :
    key_digests.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut (N := N)
      (mask,v,rows,off,Store.control) k ⦃ r c =>
      (∀ j : Fin 16, r j = laneWord rows j (off.val+4*k.val)) ∧ c = (mask,v,rows,off,Store.control) ⦄ := by
  unfold key_digests.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut
  simp only [DigestRust.core.core_arch.x86.avx512f._mm512_setzero_si512, GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512, DigestRust.core.slice.Slice.as_ptr, DigestRust.core.ptr.const_ptr.RawPtrConstT.cast, DigestRust.core.ptr.const_ptr.RawPtrConstT.add, GatherRust.core.slice.Slice.as_ptr,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,bind_ok]
  step as ⟨idx,hidx⟩
  step as ⟨at',hat⟩
  have hp : at'.val + 4 ≤ L.val := by scalar_tac
  have htotal : L.val ≤ (flat rows.val).length := by
    rw [flat_length]; exact Nat.le_mul_of_pos_left _ hn
  have hb : at'.val ≤ (flat rows.val).length := by omega
  unfold flat at hb
  simp only [GatherRust.core.ptr.const_ptr.RawPtrConstT.add, Nat.zero_add, hb, ↓reduceIte,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast, bind_ok]
  rw [← show flat rows.val = rows.val.flatMap (·.val) from rfl]
  apply WP.spec_bind (gather_spec rows at'.val mask v hm hs hp)
  intro ws hw
  step with Store.shuffle ws as ⟨r,hr⟩
  refine ⟨?_,rfl⟩
  intro j
  rw [hr,hw]
  by_cases ha : active mask j = true
  · have hj := (hm j).1 ha
    have hbound : j.val*L.val + at'.val + 4 ≤ (flat rows.val).length := by
      rw [flat_length]
      calc
        _ ≤ (j.val+1)*L.val := by rw [Nat.add_mul]; omega
        _ ≤ _ := Nat.mul_le_mul_right _ hj
    rw [if_pos ha,big_after_little (flat rows.val) _ hbound,flat_word rows.val _ _ hj hp]
    simp only [laneWord,hj,↓reduceIte,hat,hidx]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte, laneWord, mt (hm j).2 ha]
    rfl

#print axioms read_spec
end slhdsa.X86.Digest
