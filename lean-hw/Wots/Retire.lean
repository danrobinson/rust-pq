import Wots.Assigned
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512

def outputKey (indices : LaneArray) (j : Fin 16) :=
  (IScalar.hcast .Usize indices.val[j.val]!).val

private theorem retire_step {N : Usize} (indices : LaneArray) (values : Staged N) (out : Buffers) (mask : U16)
    (nz : mask.bv ≠ 0) (width : N.val ≤ 32)
    (valid : ∀ j : Fin 16, enabled mask j = true → outputKey indices j < out.length) :
    recover_loop5_loop3.body indices values out mask ⦃ flow => ∃ buf rest, ∃ lane : Fin 16,
      flow = cont (buf,rest) ∧ lane.val = mask.bv.ctz.toNat ∧ rest.val < mask.val ∧
      (∀ j, enabled rest j = (enabled mask j && decide (j ≠ lane))) ∧
      piece out buf (outputKey indices lane) 22 values.val[lane.val]!.val ⦄ := by
  let l := Chain.firstLane mask
  have pos : l.val = mask.bv.ctz.toNat := Chain.first_val mask nz
  let lane : Fin 16 := ⟨l.val,by rw [pos]; exact BitVec.ctz_lt_iff_ne_zero.mpr nz⟩
  have bit : enabled mask lane = true := by
    unfold enabled; change mask.bv.getLsbD l.val = true; rw [pos]; exact BitVec.getLsbD_true_ctz_of_ne_zero nz
  have range := valid lane bit
  have nn : mask ≠ 0#u16 := by rintro rfl; exact nz rfl
  have positive : 0 < mask.val := by by_contra! h; apply nz; apply BitVec.eq_of_toNat_eq; change mask.val = 0; omega
  unfold recover_loop5_loop3.body
  simp only [bne_iff_ne,if_pos nn,WotsRust.core.num.U16.trailing_zeros,ChainWriteRust.core.num.U16.trailing_zeros,
    lift,bind_ok]
  step as ⟨idx,hidx⟩
  · rw [show indices.length=16 by simp]; exact lane.isLt
  have key : (IScalar.hcast .Usize idx).val = outputKey indices lane := by rw [hidx,← getElem!_pos]; rfl
  step as ⟨a,restore,ha,hback⟩
  step as ⟨stop,hs⟩
  step as ⟨dst,restoreBytes,hsub,hlen,hrestore⟩
  step as ⟨value,hv⟩
  all_goals try (change l.val < 16; exact lane.isLt)
  step as ⟨copy,hcopy⟩
  · rw [hlen]; simp [hs]
  step as ⟨v,hval⟩
  let rest := mask &&& v
  have clear := Chain.next_mask mask v hval nz
  have dec : rest.val < mask.val := by
    change (mask.bv &&& v.bv).toNat < mask.val
    change mask.bv &&& v.bv = _ at clear
    rw [clear,BitVec.toNat_and,BitVec.toNat_sub_of_le (by exact positive)]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by change mask.val-1 < mask.val; omega)
  refine ⟨_,rest,lane,rfl,pos,dec,?_,?_,?_,?_⟩
  · intro j
    unfold enabled
    change (mask &&& v).bv.getLsbD _ = _
    rw [clear,Chain.pop_bit mask nz]
    simp [← pos,Fin.ext_iff,lane]
  · rw [hback]; simp
  · intro j different
    rw [hback,Slice.set_val_eq,key,Avx2.setOther _ _ _ _ (Ne.symm different)]
  · rw [hback,Slice.set_val_eq,key,Avx2.setSame _ _ _ range,hrestore,hcopy]
    have fit : value.val.length ≤ a.val.length-22 := by simp; omega
    simp only [Array.val_to_slice,List.setSlice!,show (22#usize).val = 22 by rfl,Nat.min_eq_left fit,List.take_length]
    simp only [hv,ha,← getElem!_pos,key]
    rfl


def retired {N} (indices : LaneArray) (values : Staged N) (before after : Buffers) (written : Fin 16 → Prop) :=
  after.length = before.length ∧
  (∀ j, written j → let r := outputKey indices j
    after.val[r]!.val = before.val[r]!.val.take 22 ++ values.val[j.val]!.val ++ before.val[r]!.val.drop (22+N.val)) ∧
  ∀ r, (∀ j, written j → outputKey indices j ≠ r) → after.val[r]! = before.val[r]!

theorem retire_spec {N} (out : Buffers) (indices : LaneArray) (values : Staged N) (finished : U16)
    (width : N.val ≤ 32) (valid : ∀ j, enabled finished j = true → outputKey indices j < out.length)
    (uniqueKey : ∀ i j, enabled finished i = true → enabled finished j = true →
      outputKey indices i = outputKey indices j → i=j) :
    recover_loop5_loop3 out indices values finished ⦃ after =>
      retired indices values out after (fun j => enabled finished j = true) ⦄ := by
  unfold recover_loop5_loop3
  apply loop.spec_decr_nat (measure := fun p : Buffers × U16 => p.2.val)
    (inv := fun p => (∀ j, enabled p.2 j = true → enabled finished j = true) ∧
      retired indices values out p.1 (fun j => enabled finished j = true ∧ enabled p.2 j = false))
  · rintro ⟨buf,m⟩ ⟨sub,prior⟩
    simp only at sub prior
    by_cases empty : m.bv=0
    · have eq : m=0#u16 := by apply U16.bv_eq_imp_eq; exact empty
      subst m
      simp only [recover_loop5_loop3.body,bne_self_eq_false,ite_false,step_simps]
      simpa [enabled] using prior
    · apply WP.spec_mono (retire_step indices values buf m empty width (fun j hj => prior.1 ▸ valid _ (sub _ hj)))
      rintro flow ⟨b,rest,lane,rfl,hselected,decrease,bits,wrote⟩
      have here : enabled m lane = true := by unfold enabled; rw [hselected]; exact BitVec.getLsbD_true_ctz_of_ne_zero empty
      have original := sub _ here
      have previously (j) (ne : j ≠ lane) : enabled rest j = enabled m j := by simp [bits,ne]
      have gone : enabled rest lane = false := by simp [bits]
      refine ⟨⟨?_,wrote.1.trans prior.1,?_,?_⟩,decrease⟩
      · intro j h; apply sub j; rw [bits] at h; exact (Bool.and_eq_true_iff.mp h).1
      · intro j ⟨was,now⟩
        by_cases selected : j=lane
        · subst j
          have same := prior.2.2 (outputKey indices lane) (fun k hk eq => by
            have identical := uniqueKey k lane hk.1 original eq
            subst k; simp_all)
          simpa only [same,show values.val[lane.val]!.val.length = N.val by simp] using wrote.2.2
        · have ne : outputKey indices j ≠ outputKey indices lane := fun eq => selected (uniqueKey _ _ was original eq)
          dsimp only
          rw [wrote.2.1 _ ne]
          exact prior.2.1 j ⟨was,(previously j selected) ▸ now⟩
      · intro r unused
        have ne : outputKey indices lane ≠ r := unused lane ⟨original,gone⟩
        rw [wrote.2.1 _ (Ne.symm ne)]
        apply prior.2.2
        intro j hj
        by_cases same : j=lane
        · simpa only [same] using ne
        · exact unused j ⟨hj.1,(previously j same).trans hj.2⟩
  · simp [retired]

theorem retire_branch_eq {N} :
    @recover_loop5_loop5 N = @recover_loop5_loop3 N ∧ @recover_loop5_loop9 N = @recover_loop5_loop3 N ∧
    @recover_loop5_loop11 N = @recover_loop5_loop3 N := ⟨rfl,rfl,rfl⟩
end slhdsa.X86.Wots
