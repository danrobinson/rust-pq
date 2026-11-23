import Wotsapi.Top
import Chainx86.Top
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots.Api
open Wide

theorem chain_eq (N : Usize) (st : Array U32 8#usize) (blocks : Intel.Chain.Rows) (starts ends : Slice U32) :
    WotsApiRust.sha256.x86.chain_blocks N st blocks starts ends = hash.chain_blocks N st blocks starts ends := by
  by_cases bad : N.val > 32 ∨ starts.length < blocks.length ∨ ends.length < blocks.length
  · rw [show WotsApiRust.sha256.x86.chain_blocks N st blocks starts ends = _ from Dispatch.fallback_eq N st blocks starts ends bad]
    unfold hash.chain_blocks sha256.hw.chain_blocks sha256.hw.arm.available
    rcases bad with h|h|h
    · simp only [if_neg (show N ≠ 16#usize by scalar_tac),if_neg (show N ≠ 24#usize by scalar_tac),
        if_neg (show N ≠ 32#usize by scalar_tac),bind_ok,Bool.false_eq_true,ite_false]
      rfl
    · have short : starts.len < blocks.len := h
      split_ifs <;> simp_all [bind_ok]
    · have short : ends.len < blocks.len := h
      split_ifs <;> simp_all [bind_ok]
  push Not at bad
  obtain ⟨x,hx,lx,ex⟩ := spec_imp_exists (Dispatch.chains_spec N st blocks starts ends bad.1 bad.2.1 bad.2.2)
  obtain ⟨y,hy,ly,ey⟩ := spec_imp_exists (chain_blocks_spec N bad.1 st blocks starts ends bad.2.1 bad.2.2)
  unfold WotsApiRust.sha256.x86.chain_blocks
  rw [hx,hy]
  congr 1
  apply Slice.ext
  apply List.ext_getElem
  · exact lx.trans ly.symm
  · intro j hx hy
    have bound : j < blocks.length := lx ▸ hx
    apply Aeneas.Std.Array.ext
    rw [← getElem!_pos x.val j hx,← getElem!_pos y.val j hy]
    exact (bytes_inj _ _).mp ((ex j bound).trans (ey j bound).symm)

theorem fallback_fips {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (m : Array U8 N) (seed : WotsApiRust.hash.Seed N) (a : WotsApiRust.address.Adrs)
    (seedOK : SeedOk (coreSeed (WotsApiRust.wideSeed seed))) (cpu : GatherRust.avx512Available=false)
    (room : N.val*(2*N.val+3) ≤ sig.length) :
    WotsApiRust.wots.wots_pk_from_sig sig m seed a ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (paramsS p) (bytes sig.val) (bytes m.val) (bytes seed.pk_seed.val)
        (adrsS (coreAddress (WotsApiRust.wideAddress a))) ⦄ := by
  let ca := coreAddress (WotsApiRust.wideAddress a)
  unfold WotsApiRust.wots.wots_pk_from_sig
  simp only [bind_ok,WotsApiRust.sha256.x86.avx512_available,WotsX86Rust.sha256.x86.avx512_available,
    WotsX86Rust.sha256.x86.has_avx512.get,GatherRust.sha256.x86.avx512_available,cpu,Bool.false_eq_true,ite_false,chain_eq]
  have loopEq : WotsApiRust.wots.wots_pk_from_sig_loop0 N sig a = wots.wots_pk_from_sig_loop N sig ca := by
    funext l arr i
    unfold WotsApiRust.wots.wots_pk_from_sig_loop0 wots.wots_pk_from_sig_loop
    congr 1
    funext ⟨b,k⟩
    unfold WotsApiRust.wots.wots_pk_from_sig_loop0.body wots.wots_pk_from_sig_loop.body
    simp only [WotsApiRust.address.Adrs.with_word2,address.Adrs.with_word2,lift,bind_tc_eq,bind_ok]
    split <;> rfl
  rw [loopEq,show WotsApiRust.wots.wots_digits (N := N) = wots.wots_digits by with_unfolding_all rfl]
  have hn := hp.le32
  rw [show WotsApiRust.params.LEN2 = 3#usize by unfold WotsApiRust.params.LEN2; rfl]
  step as ⟨twice,ht⟩
  step as ⟨len,hl⟩
  have count : len.val = 2*N.val+3 := by rw [hl,ht]
  step with wots_digits_spec p hp m as ⟨digits,eq,dl,valid⟩
  rcases hp.nok with w|w|w <;> simp only [w,bind_ok,ite_true]
  all_goals
    step with wots_pk_from_sig_loop_spec N hn sig ca len (by omega) (hsig := by rw [count]; exact room)
    step*
  all_goals try (unfold WotsApiRust.params.W; decide)
  all_goals
    simp only [WotsApiRust.address.Adrs.with_type,WotsApiRust.address.Adrs.with_keypair,bind_ok]
    step as ⟨s4,s4_post,s4_post1⟩
    have hs4l : s4.length = 2*N.val+3 := by rw [s4_post1]; omega
    unfold WotsApiRust.hash.thash_values
    rw [thash_eq _ _ _ hp.nok hs4l]
    step with thash_values_spec (paramsS p) hp.n hp.nok _ seedOK _ s4 hs4l as ⟨r,r_post⟩
    have addr : adrsS (coreAddress (WotsApiRust.wideAddress {a with typ := WotsApiRust.address.WOTS_PK, word2 := 0#u32,word3 := 0#u32})) =
        Spec.wotsPkAdrs (adrsS ca) := by unfold WotsApiRust.address.WOTS_PK; rfl
    have hi15 : i1 = 15#u32 := by rw [i1_post]; unfold WotsApiRust.params.W; decide
    have hsl : s.val.length = len.val := by simp [s_post]; omega
    have hs3l : s3.val.length = len.val := by have := s3_post; simp only [Slice.length] at this; omega
    rw [r_post, addr, Spec.wotsPkFromSig, hs4l, ← hp.len,
      flatMap_lanes N.val s4.val _
        (fromSigStep (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS ca) (nats digits.val)),eq]
    · rfl
    · intro j hj
      rw [hp.len] at hj
      have hd := digit_le digits _ dl valid j hj
      have hblk : Spec.block (paramsS p) (bytes sig.val) j = ((bytes sig.val).drop (j * N.val)).take N.val := by
        rw [Spec.block,hp.n]
      have hbl : (((bytes sig.val).drop (j*N.val)).take N.val).length = N.val := by
        have h := Nat.mul_le_mul_left N.val (show j+1 ≤ 2*N.val+3 by omega)
        rw [Nat.mul_succ,Nat.mul_comm N.val j] at h
        change _ ≤ sig.val.length at room
        simp; omega
      rw [blkVal,s4_post,Array.val_to_slice,s_post2,back_lane _ _ _ _ (by omega) hs3l (by simp; omega),
        s3_post1 j (by simp [Slice.length]; omega),s_post,slice0_getElem! _ _ _ (by omega) (by simp; omega),
        s2_post,repeat_getElem! _ _ (by omega),hi15,
        show seed.state = (coreSeed (WotsApiRust.wideSeed seed)).state by rfl,
        lane_value p hp (coreSeed (WotsApiRust.wideSeed seed)) seedOK { adrsS ca with word2 := j } _ hbl _
          ⟨(adrsS ca).word3,blocks1_post j (by omega)⟩ _ (15#u32).val (by simpa using hd),
        fromSigStep,nats_getElem! digits.val j (by change j < digits.length; omega),vec_deref_val,hblk,w_eq]
      rfl

theorem recover_fips {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (m : Array U8 N) (seed : WotsApiRust.hash.Seed N) (a : WotsApiRust.address.Adrs)
    (seedOK : SeedOk (coreSeed (WotsApiRust.wideSeed seed))) (room : N.val*(2*N.val+3) ≤ sig.length) :
    WotsApiRust.wots.wots_pk_from_sig sig m seed a ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (paramsS p) (bytes sig.val) (bytes m.val) (bytes seed.pk_seed.val)
        (adrsS (coreAddress (WotsApiRust.wideAddress a))) ⦄ := by
  cases cpu : GatherRust.avx512Available with
  | false => exact fallback_fips p hp sig m seed a seedOK cpu room
  | true => exact avx512_fips p hp sig m seed a seedOK cpu room

end slhdsa.X86.Wots.Api
