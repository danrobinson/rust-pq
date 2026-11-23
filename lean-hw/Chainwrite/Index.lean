import Chainwrite.Walk
import Chainni.Words
open Aeneas Aeneas.Std Result ControlFlow
set_option maxHeartbeats 2000000
namespace slhdsa.X86.Chain
open ChainWriteRust.sha256.x86.avx512

abbrev firstLane (m : U16) := UScalar.cast .Usize (⟨m.bv.ctz.setWidth 32⟩ : U32)

theorem first_val (m : U16) (nz : m.bv ≠ 0) : (firstLane m).val = m.bv.ctz.toNat := by
  have small := BitVec.ctz_lt_iff_ne_zero.mpr nz
  change m.bv.ctz.toNat < 16 at small
  unfold firstLane
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
  · change (m.bv.ctz.setWidth 32).toNat = _
    simp; omega
  · scalar_tac

theorem next_mask (m v : U16) (nv : v.val = m.val - 1) (nz : m.bv ≠ 0) :
    (m &&& v).bv = (m.bv &&& (m.bv - (1 : BitVec 16))) := by
  have pos : m.val ≠ 0 := by intro e; apply nz; apply BitVec.eq_of_toNat_eq; exact e
  have eq : v.bv = m.bv - (1 : BitVec 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by change 1 ≤ m.val; omega)]
    exact nv
  change m.bv &&& v.bv = _
  rw [eq]

theorem write_index_spec (batch : Rows) (ends : Slice U32) (mask : U16)
    (hb : Covers mask batch.length) (he : Covers mask ends.length)
    (hp : ∀ j, mask.bv.getLsbD j = true → 0 < ends.val[j]!.val) :
    write_finished_loop0 batch ends mask ⦃ out => out.length = batch.length ∧
      ∀ k < batch.length, bytes out.val[k]!.val =
        if mask.bv.getLsbD k then Intel.Chain.withIndex (bytes batch.val[k]!.val) (ends.val[k]!.val-1)
        else bytes batch.val[k]!.val ⦄ := by
  unfold write_finished_loop0
  apply walk (body := write_finished_loop0.body ends) (applyRow := fun k row => Intel.Chain.withIndex row (ends.val[k]!.val-1))
  · intro b; rfl
  · intro b m len nz sub
    have selected := sub _ (BitVec.getLsbD_true_ctz_of_ne_zero nz)
    let lane := firstLane m
    have hl : lane.val = m.bv.ctz.toNat := first_val m nz
    have hi : lane.val < b.length := by rw [len,hl]; exact hb _ selected
    have hs : lane.val < ends.length := by rw [hl]; exact he _ selected
    have pos : 0 < ends.val[lane.val].val := by rw [← getElem!_pos]; simpa [hl] using hp _ selected
    have nonzero : m ≠ 0#u16 := by intro eq; subst m; exact nz rfl
    have positive : 0 < m.val := by by_contra! h; apply nz; apply BitVec.eq_of_toNat_eq; change m.val = 0; omega
    simp only [write_finished_loop0.body,bne_iff_ne,ChainWriteRust.core.num.U16.trailing_zeros,bind_ok,lift]
    rw [if_pos nonzero]
    change (do
      let (a, back) ← Slice.index_mut_usize b lane
      let (s, backA) ← core.array.Array.index_mut _ a _
      let t ← Slice.index_usize ends lane
      let idx ← t - 1#u32
      let dst ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s (Array.to_slice (core.num.U32.to_be_bytes idx))
      let v ← m - 1#u16
      ok (cont (back (backA dst), m &&& v))) ⦃ _ => _ ⦄
    step as ⟨a,back,ha,hback⟩
    step as ⟨s,backA,hsub,hslen,hba⟩
    step as ⟨t,ht⟩
    step as ⟨idx,hidx⟩
    step as ⟨dst,hd⟩
    step as ⟨v,hv⟩
    all_goals try (simp only [Slice.length] at *; omega)
    simp only [step_simps,hback,Slice.set_val_eq]
    refine ⟨_,_,rfl,by simp,next_mask _ _ hv nz,?_⟩
    intro k hk
    rw [Slice.set_val_eq]
    by_cases eq : k = lane.val
    · subst k
      rw [if_pos hl,Avx2.setSame _ _ _ hi,hd,hba,bytes_setSlice _ _ _ (by simp)]
      simp only [Array.val_to_slice,ha,← getElem!_pos,Intel.Chain.withIndex]
      have be : bytes (core.num.U32.to_be_bytes idx).val = Spec.toByte idx.val 4 := by
        simpa [core.num.U32.to_be_bytes,bytes] using Intel.Chain.big_endian idx.bv
      rw [be,hidx,ht,← getElem!_pos]
      simp
    · rw [if_neg (by rwa [← hl]),Avx2.setOther _ _ _ _ (Ne.symm eq)]
end slhdsa.X86.Chain
