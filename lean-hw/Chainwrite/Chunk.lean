import Chainwrite.Index
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain
open ChainWriteRust.sha256.x86.avx512
abbrev ChunkRows := Array (Array (Array U8 16#usize) 4#usize) 4#usize

def putChunk (rows : ChunkRows) (offset width k : Nat) (row : Spec.Bytes) :=
  row.take (22+offset) ++ (bytes rows.val[k%4]!.val[k/4]!.val).take width ++ row.drop (22+offset+width)

theorem write_chunk_spec (batch : Rows) (rows : ChunkRows) (mask : U16) (offset width : Usize)
    (hb : Covers mask batch.length) (hw : width.val ≤ 16) (hend : 22+offset.val+width.val ≤ 64) :
    write_finished_loop1_loop0 batch offset rows width mask ⦃ out => out.length = batch.length ∧
      ∀ k < batch.length, bytes out.val[k]!.val =
        if mask.bv.getLsbD k then putChunk rows offset.val width.val k (bytes batch.val[k]!.val)
        else bytes batch.val[k]!.val ⦄ := by
  unfold write_finished_loop1_loop0
  apply walk (body := write_finished_loop1_loop0.body offset rows width) (applyRow := putChunk rows offset.val width.val)
  · intro b; rfl
  · intro b m len nz sub
    have selected := sub _ (BitVec.getLsbD_true_ctz_of_ne_zero nz)
    let lane := firstLane m
    have hl : lane.val = m.bv.ctz.toNat := first_val m nz
    have small := BitVec.ctz_lt_iff_ne_zero.mpr nz
    change m.bv.ctz.toNat < 16 at small
    have hi : lane.val < b.length := by rw [len,hl]; exact hb _ selected
    have nonzero : m ≠ 0#u16 := by intro eq; subst m; exact nz rfl
    have positive : 0 < m.val := by by_contra! h; apply nz; apply BitVec.eq_of_toNat_eq; change m.val = 0; omega
    simp only [write_finished_loop1_loop0.body,bne_iff_ne,ChainWriteRust.core.num.U16.trailing_zeros,bind_ok,lift]
    rw [if_pos nonzero]
    have laneEq : UScalar.cast .Usize (⟨m.bv.ctz.setWidth 32⟩ : U32) = lane := rfl
    rw [laneEq]
    step as ⟨a,back,ha,hback⟩
    step as ⟨lo,hlo⟩
    step as ⟨lim,hlim⟩
    step as ⟨s,backA,hsub,hslen,hba⟩
    step as ⟨i,hi'⟩
    step as ⟨j,hj⟩
    step as ⟨group,hg⟩
    step as ⟨part,hpart⟩
    step as ⟨src,hsrc,hlen⟩
    step as ⟨dst,hd⟩
    all_goals try omega
    step as ⟨v,hv⟩
    all_goals try scalar_tac
    simp only [step_simps,hback]
    refine ⟨_,_,rfl,by simp,next_mask _ _ hv nz,?_⟩
    intro k hk
    rw [Slice.set_val_eq]
    by_cases eq : k = lane.val
    · subst k
      rw [if_pos hl,Avx2.setSame _ _ _ hi,hd,hba,bytes_setSlice _ _ _ (by scalar_tac)]
      simp only [ha,hsrc,hpart,hg,Array.val_to_slice,List.slice,List.drop_zero,← getElem!_pos,putChunk,bytes,List.map_take]
      simp [hlo,hi',hj, Nat.min_eq_left hw]
    · rw [if_neg (by rwa [← hl]),Avx2.setOther _ _ _ _ (Ne.symm eq)]
end slhdsa.X86.Chain
