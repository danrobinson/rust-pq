import Gather512.Rows
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Gather
open GatherRust.core.core_arch.x86
open _root_.core.core_arch.x86
open GatherRust.sha512.x86

def active (mask : U8) (j : Fin 8) := mask.bv.getLsbD j.val
def Mask (mask : U8) (n : Nat) := ∀ j : Fin 8, active mask j = true ↔ j.val < n
def Stride (v : __m256i) (L : Nat) := ∀ j : Fin 8, (v j).toInt * 8 = (j.val*L : Nat)

theorem gather_spec {L : Usize} (rows : Slice (Array U8 L)) (pos : Nat)
    (mask : U8) (v : __m256i) (hm : Mask mask rows.length) (hs : Stride v L.val) (hp : pos+8 ≤ L.val) :
    GatherRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi64 8#i32 (fun _ => 0) mask v
      ⟨flat rows.val,pos⟩ ⦃ out => ∃ words : Fin 8 → BitVec 64, out = ofWords64 words ∧ ∀ j,
        words j = if active mask j then littleWord (flat rows.val) (j.val*L.val+pos) else 0 ⦄ := by
  let p : GatherRust.ReadPtr I64 := ⟨flat rows.val,pos⟩
  have ea (j : Fin 8) : address p 8#i32 v j = (j.val*L.val+pos : Nat) := by
    change (pos : Int) + 8*(v j).toInt = _
    rw [Int.mul_comm, hs j]
    omega
  have range (j : Fin 8) (h : mask.bv.getLsbD j.val = true) :
      0 ≤ address p 8#i32 v j ∧ address p 8#i32 v j + 8 ≤ (p.allocation.length : Int) := by
    have bound := (hm j).1 h
    have hbound : (j.val+1)*L.val ≤ rows.val.length*L.val := Nat.mul_le_mul_right _ bound
    rw [Nat.add_mul, Nat.one_mul] at hbound
    rw [ea]
    change _ ∧ _ ≤ ((flat rows.val).length : Int)
    rw [flat_length]
    omega
  change GatherRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi64 _ _ _ _ p ⦃ _ => _ ⦄
  unfold GatherRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi64
  rw [if_pos ⟨by decide,range⟩]
  simp only [step_simps]
  refine ⟨_,rfl,fun j => ?_⟩
  rw [ea, Int.toNat_natCast]
  simp [active,word64,p]

theorem ofWords_even (ws : Fin 8 → BitVec 64) (j : Fin 8) :
    ofWords64 ws ⟨2*j.val,by omega⟩ = (ws j).extractLsb' 0 32 := by
  fin_cases j <;> rfl
theorem ofWords_odd (ws : Fin 8 → BitVec 64) (j : Fin 8) :
    ofWords64 ws ⟨2*j.val+1,by omega⟩ = (ws j).extractLsb' 32 32 := by
  fin_cases j <;> rfl

def laneWord {L : Usize} (rows : Slice (Array U8 L)) (j : Fin 8) (pos : Nat) :=
  if j.val < rows.length then Spec.SHA512.word (bytes rows.val[j.val]!.val) pos else 0

/-- The actual closure used by array::from_fn reads one big-endian SHA-512 word per
active key; disabled lanes produce zero without a memory access. -/
theorem read_spec (N L : Usize) (rows : Slice (Array U8 L)) (mask : U8) (v : __m256i) (off k : Usize)
    (hm : Mask mask rows.length) (hs : Stride v L.val) (hn : 0 < rows.length)
    (hk : k.val < 16) (hoff : off.val + 128 ≤ L.val) :
    digest_groups.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut (N := N)
      (mask,v,rows,off,swapControl) k ⦃ r c =>
      (∀ j : Fin 8, word64 r j = laneWord rows j (off.val+8*k.val)) ∧ c = (mask,v,rows,off,swapControl) ⦄ := by
  unfold digest_groups.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut
  simp only [GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512, GatherRust.core.slice.Slice.as_ptr,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,bind_ok]
  step as ⟨idx,hidx⟩
  step as ⟨at',hat⟩
  have hp : at'.val + 8 ≤ L.val := by scalar_tac
  have htotal : L.val ≤ (flat rows.val).length := by
    rw [flat_length]; exact Nat.le_mul_of_pos_left _ hn
  have hb : at'.val ≤ (flat rows.val).length := by omega
  unfold flat at hb
  simp only [GatherRust.core.ptr.const_ptr.RawPtrConstT.add, Nat.zero_add, hb, ↓reduceIte,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast, bind_ok]
  rw [← show flat rows.val = rows.val.flatMap (·.val) from rfl]
  apply WP.spec_bind (gather_spec rows at'.val mask v hm hs hp)
  rintro g ⟨ws,rfl,hw⟩
  step with shuffle_swap (ofWords64 ws) as ⟨r,hr⟩
  refine ⟨?_,rfl⟩
  intro j
  rw [hr, ofWords_even,ofWords_odd,hw]
  by_cases ha : active mask j = true
  · have hj := (hm j).1 ha
    have hbound : j.val*L.val + at'.val + 8 ≤ (flat rows.val).length := by
      rw [flat_length]
      calc
        _ ≤ (j.val+1)*L.val := by rw [Nat.add_mul]; omega
        _ ≤ _ := Nat.mul_le_mul_right _ hj
    rw [if_pos ha,big_after_little (flat rows.val) _ hbound,flat_word rows.val _ _ hj hp]
    simp only [laneWord,hj,↓reduceIte,hat,hidx]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte, laneWord, mt (hm j).2 ha]
    rfl

#print axioms read_spec
end slhdsa.X86.S512.Gather
