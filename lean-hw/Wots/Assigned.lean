import Wots.Load
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open WotsRust.core.core_arch.x86.avx512f
open _root_.core.core_arch.x86.avx512f

def loadAssigned (N : Usize) (indices starts : LaneArray) (counter src : Reg) (assigned : U16)
    (sig : Slice U8) (hash : Hash) (w : Words) (swap : Reg) := do
  let idx ← loadLanes indices
  let digits ← loadLanes starts
  let counters ← _mm512_mask_mov_epi32 counter assigned digits
  let n ← _mm512_set1_epi32 (UScalar.hcast .I32 N)
  let offsets ← _mm512_mullo_epi32 idx n
  let limit ← N / 4#usize
  let h ← recover_loop5_loop1 src ⟨0#usize,limit⟩ sig swap hash assigned offsets
  let chainWord ← _mm512_slli_epi32 16#u32 idx
  let words ← Array.update w 4#usize chainWord
  ok (idx,counters,h,words)

private theorem stride (index : BitVec 32) (N : Usize) (hi : index.toNat < 67) (hn : N.val ≤ 32) :
    (index * (show BitVec 32 from (UScalar.hcast .I32 N).bv)).toInt = (index.toNat*N.val : Nat) := by
  have bound : index.toNat*N.val < 2^31 := by nlinarith [Nat.mul_le_mul (by omega : index.toNat ≤ 66) hn]
  have n : (UScalar.hcast .I32 N).bv.toNat = N.val := by
    rw [UScalar.hcast_bv_eq,BitVec.toNat_setWidth]; change N.val % 2^32 = _; omega
  have prod : (index * (show BitVec 32 from (UScalar.hcast .I32 N).bv)).toNat = index.toNat*N.val := by
    rw [BitVec.toNat_mul,n,Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toInt_eq_toNat_of_msb,prod]
  rw [BitVec.msb_eq_decide,prod]; simp; omega

/-- The assigned lanes' indices determine both the signed gather offsets and
the chain word. Unassigned lanes retain their counters and digest words. -/
theorem load_assigned_spec (N : Usize) (indices starts : LaneArray) (counter src : Reg) (assigned : U16)
    (sig : Slice U8) (hash : Hash) (w : Words) (count : Nat)
    (shape : N.val = 16 ∨ N.val = 24 ∨ N.val = 32) (nonempty : 0<count) (small : count ≤ 67)
    (available : N.val*count ≤ sig.length)
    (live : ∀ j : Fin 16, enabled assigned j = true → indices.val[j.val]!.bv.toNat < count) :
    loadAssigned N indices starts counter src assigned sig hash w Store.control ⦃ idx counters h words =>
      (∀ j : Fin 16, idx j = indices.val[j.val]!.bv) ∧
      (∀ j : Fin 16, counters j = if enabled assigned j then starts.val[j.val]!.bv else counter j) ∧
      (∀ k < 8, ∀ j : Fin 16, h.val[k]! j = if k<N.val/4 ∧ enabled assigned j then
        Spec.SHA256.word (bytes sig.val) (N.val*indices.val[j.val]!.bv.toNat+4*k) else hash.val[k]! j) ∧
      ∀ k < 16, ∀ j : Fin 16, words.val[k]! j = if k=4 then idx j <<< 16 else w.val[k]! j ⦄ := by
  unfold loadAssigned
  step with load_lanes_spec indices as ⟨idx,hidx⟩
  step with load_lanes_spec starts as ⟨ds,hds⟩
  simp only [_mm512_mask_mov_epi32,ChainVectorRust.core.core_arch.x86.avx512f._mm512_mask_mov_epi32,
    _mm512_set1_epi32,_mm512_mullo_epi32,DigestRust.core.core_arch.x86.avx512f._mm512_mullo_epi32,bind_ok]
  step as ⟨limit,hl⟩
  have cap : N.val ≤ sig.length := by
    have := Nat.mul_le_mul_left N.val nonempty; omega
  let base := fun j : Fin 16 => N.val*indices.val[j.val]!.bv.toNat
  have safe (j : Fin 16) (enabledJ : enabled assigned j = true) :
      (idx j * (show BitVec 32 from (UScalar.hcast .I32 N).bv)).toInt = (base j : Int) ∧ base j+4*limit.val ≤ sig.length := by
    have bound := live j enabledJ
    have total := Nat.mul_le_mul_left N.val bound
    rw [Nat.mul_succ] at total
    unfold base
    rw [hidx,stride _ _ (by omega) (by omega),Nat.mul_comm (indices.val[j.val]!.bv.toNat)]
    exact ⟨rfl,by omega⟩
  step with signature_words sig src _ assigned limit hash base (by omega) (by omega) safe as ⟨h,hh⟩
  simp only [_mm512_slli_epi32,LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,bind_ok]
  step as ⟨words,hw⟩
  refine ⟨hidx,fun j => ?_,?_,?_⟩
  · simp only [enabled,hds]; rfl
  · simpa only [hl,base] using hh
  · intro k hk j
    rw [hw,Array.set_val_eq,show (4#usize).val=4 by rfl]
    by_cases e : k=4
    · subst k; rw [Avx2.setSame _ _ _ (by simp),if_pos rfl]; rfl
    · rw [Avx2.setOther _ _ _ _ (Ne.symm e),if_neg e]

/-- Every active gather has a valid signature-element index after refill.
This ties the machine integer cast to the stable counting-sort queue. -/
theorem assigned_index {digits : Slice U32} {order : Order} {oldIx oldStarts ix starts : LaneArray}
    {oldMask mask assigned : U16} {pos next : Usize}
    (mapping : mapped digits order oldIx oldStarts oldMask pos (ix,starts,mask,next,assigned))
    (small : digits.length ≤ 67)
    (queued : ∀ q < next.val, order.val[q]!.val < digits.length)
    (j : Fin 16) (active : enabled assigned j = true) :
    ∃ q, pos.val ≤ q ∧ q < next.val ∧ ix.val[j.val]!.bv.toNat = order.val[q]!.val ∧
      ix.val[j.val]!.bv.toNat < digits.length ∧ starts.val[j.val]!.bv = digits.val[order.val[q]!.val]!.bv := by
  obtain ⟨job,_,_,lanes⟩ := mapping
  have hj := lanes j
  cases eq : job j with
  | none => rw [eq] at hj; simp only at hj; simp_all
  | some q =>
    rw [eq] at hj; simp only at hj
    obtain ⟨low,high,_,_,_,hix,hs⟩ := hj
    have valid := queued q high
    have idx : ix.val[j.val]!.bv.toNat = order.val[q]!.val := by
      rw [hix]
      change (UScalar.hcast .I32 order.val[q]!).bv.toNat = _
      rw [UScalar.hcast_bv_eq,BitVec.toNat_setWidth]
      change order.val[q]!.val % 2^32 = _
      omega
    refine ⟨q,low,high,idx,idx ▸ valid,?_⟩
    rw [hs]
    change (UScalar.hcast .I32 digits.val[order.val[q]!.val]!).bv = _
    rw [UScalar.hcast_bv_eq]; rfl

theorem refill_load_spec {digits : Slice U32} {order : Order} {oldIx oldStarts ix starts : LaneArray}
    {oldMask mask assigned : U16} {pos next : Usize}
    (mapping : mapped digits order oldIx oldStarts oldMask pos (ix,starts,mask,next,assigned))
    (queued : ∀ q < next.val, order.val[q]!.val < digits.length)
    (nonzero : assigned ≠ 0#u16) (small : digits.length ≤ 67)
    (N : Usize) (counter src : Reg) (sig : Slice U8) (hash : Hash) (w : Words)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) (available : N.val*digits.length ≤ sig.length) :
    loadAssigned N ix starts counter src assigned sig hash w Store.control ⦃ idx counters h words =>
      (∀ j : Fin 16, if enabled assigned j then
        ∃ q, pos.val ≤ q ∧ q < next.val ∧ idx j = BitVec.ofNat 32 order.val[q]!.val ∧
          counters j = digits.val[order.val[q]!.val]!.bv ∧
          ∀ k < N.val/4, h.val[k]! j = Spec.SHA256.word (bytes sig.val) (N.val*order.val[q]!.val+4*k)
        else counters j = counter j ∧ ∀ k < 8, h.val[k]! j = hash.val[k]! j) ∧
      ∀ k < 16, ∀ j : Fin 16, words.val[k]! j = if k=4 then idx j <<< 16 else w.val[k]! j ⦄ := by
  have nz : assigned.bv ≠ 0 := by
    intro e; apply nonzero; apply UScalar.eq_of_val_eq; exact congrArg BitVec.toNat e
  have lt := BitVec.ctz_lt_iff_ne_zero.mpr nz
  let witness : Fin 16 := ⟨_,lt⟩
  have on : enabled assigned witness = true := BitVec.getLsbD_true_ctz_of_ne_zero nz
  have valid (j) (enabledJ : enabled assigned j = true) : ix.val[j.val]!.bv.toNat < digits.length := by
    obtain ⟨_,_,_,_,bound,_⟩ := assigned_index mapping small queued j enabledJ
    exact bound
  have existsIndex := valid witness on
  apply WP.spec_mono (load_assigned_spec N ix starts counter src assigned sig hash w digits.length shape
    (by omega) small available valid)
  rintro ⟨idx,counters,h,words⟩ ⟨hi,hc,hh,hw⟩
  refine ⟨fun j => ?_,hw⟩
  by_cases yes : enabled assigned j = true
  · rw [if_pos yes]
    obtain ⟨q,low,high,key,_,digit⟩ := assigned_index mapping small queued j yes
    refine ⟨q,low,high,?_,?_,?_⟩
    · rw [hi,← key]; symm; rw [BitVec.ofNat_toNat]; rfl
    · rw [hc,if_pos yes,digit]
    · intro k hk
      rw [hh k (by omega),if_pos ⟨hk,yes⟩,key]
  · rw [if_neg yes]
    exact ⟨by rw [hc,if_neg yes],fun k hk => by rw [hh k hk,if_neg (fun p => yes p.2)]⟩

end slhdsa.X86.Wots
