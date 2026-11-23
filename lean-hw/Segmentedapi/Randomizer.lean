import Segmentedapi.KeyPad
import Segmentedapi.Padding
import Segmented.Instances
open Aeneas Aeneas.Std Result
namespace slhdsa.SegmentedApi
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

theorem randomizer_spec {N : Usize} (p : params.Params) (hp : PN p N) (key random : Array U8 N)
    (ctx msg : Slice U8) (context : ctx.length≤255)
    (room : Room msg.length (msgSlack N.val+257)) :
    SegmentedApiRust.slh.message.randomizer key random ctx msg ⦃ out =>
      bytes out.val = Spec.PRFmsg (paramsS p) (bytes key.val) (bytes random.val)
        (Spec.withContext (bytes msg.val) (bytes ctx.val)) ⦄ := by
  have width := hp.le32
  unfold SegmentedApiRust.slh.message.randomizer
  simp only [SegmentedApiRust.sha256.compress,SegmentedApiRust.sha512.compress,
    show SegmentedApiRust.sha256.digest = sha256.digest by with_unfolding_all rfl,
    show SegmentedApiRust.sha512.digest = sha512.digest by with_unfolding_all rfl,
    show SegmentedApiRust.sha256.H0 = sha256.H0 by with_unfolding_all rfl,
    show SegmentedApiRust.sha512.H0 = sha512.H0 by with_unfolding_all rfl]
  have cLen : ctx.len.val=ctx.length := rfl
  by_cases small : N=16#usize
  all_goals try subst N
  all_goals try simp only [if_pos rfl]
  all_goals try simp only [if_neg small]
  all_goals step*
  all_goals try rfl
  all_goals try (solve | simp [Array.repeat_val])
  all_goals try (simp only [core.clone.CloneU8,step_simps])
  all_goals try omega

  all_goals try (solve | rw [s15_post1,s16_post]; simp)
  all_goals try (solve | rw [s12_post]; simp)
  all_goals try (solve | rw [s22_post]; simp)
  all_goals try (solve | rw [s23_post1]; simp [Slice.length,s21_post])
  all_goals try (solve | simp; omega)
  all_goals try (solve | rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by simpa [Slice.length,s10_post] using s11_post),s11_post1]; simp [Slice.length,s10_post])
  · change Room msg.length (152+257) at room
    change Room (64+s9.length+msg.length) 72
    obtain ⟨left,right⟩ := room
    constructor <;> omega
  · have front : bytes (s9.val++msg.val) = bytes random.val ++ Spec.withContext (bytes msg.val) (bytes ctx.val) := by
      rw [s9_post,Array.val_to_slice,s6_post2,s7_post,s3_post2,s5_post,s4_post,s_post2,s2_post,s1_post,Array.val_to_slice]
      simp only [Array.val_to_slice,Array.repeat_val,List.slice,List.drop_zero,Nat.sub_zero]
      exact prefix_bytes random ctx msg i1 i1_post i2.val used.val i2_post (by rwa [cLen] at used_post) (by omega)
    have magnitude : i6=768#i32 := by apply IScalar.eq_of_val_eq; rw [i6_post,i5_post]; decide +kernel
    have encoded : a.val=[3#u8,0#u8] := by rw [a_post,i7_post,magnitude]; decide +kernel
    have reset : (to_slice_mut_back1 s14).val=List.replicate 64 0#u8 := by
      rw [to_slice_mut_back1_post,Array.from_slice_val _ _ (by simpa [Slice.length,s13_post] using s14_post),s14_post1]
      simp [Slice.length,s13_post]
    have finish : bytes s22.val=padFrom 64 (bytes inner.val) := by
      rw [s22_post,Array.val_to_slice,s18_post2,s20_post,s19_post,Array.val_to_slice,encoded,pad6_post,Array.set_val_eq,
        s15_post2,s17_post,s16_post,Array.val_to_slice,reset,setSlice_rep _ _ _ (by simp),i4_post]
      rw [show 64-inner.val.length=32 by simp]
      change bytes (((inner.val ++ List.replicate 32 0#u8).set 32 128#u8).setSlice! 62 [3#u8,0#u8]) = _
      have footer := finish_bytes inner.val 0#u8 3#u8 128#u8 29 (by simp)
      have footerEq : (((inner.val ++ List.replicate 32 0#u8).set 32 128#u8).setSlice! 62 [3#u8,0#u8]) =
          ((inner.val ++ List.replicate 32 0#u8).set 32 128#u8).set 62 3#u8 := by simpa using footer
      rw [footerEq]
      simpa only [bytes_set,bytes_append,bytes_replicate,Array.property,show (0#u8).bv=0#8 by decide +kernel, show (128#u8).bv=128#8 by decide +kernel, show (3#u8).bv=3#8 by decide +kernel] using fin256 (bytes inner.val) (by simp)
    rw [to_slice_mut_back2_post,Array.from_slice_val _ _ (by simpa [Slice.length,s24_post] using s23_post1),
      s24_post,s23_post,List.slice,Array.val_to_slice,List.drop_zero,Nat.sub_zero,bytes_take,a2_post,a1_post]
    rw [s12_post,Array.val_to_slice,take_drop0 _ _ (by simp),H0_eq] at outer_post
    rw [s8_post,Array.val_to_slice,take_drop0 _ _ (by simp),H0_eq] at state_post
    rw [state_post,← sha256_prefix64 _ _ (by simp),front] at inner_post
    rw [take_drop0 _ _ (by rw [s22_post]; simp),finish,outer_post,← hashFrom_one _ _ (by rw [← finish,s22_post]; simp),
      ← sha256_prefix64 _ _ (by simp),inner_post,pad1_post,pad3_post]
    simp [Spec.PRFmsg,Spec.hmacSha256,paramsS,hp.n_eq]
  · have hn : N.val≠16 := fun h => small (by scalar_tac)
    have size := room.1
    rw [msgSlack,if_neg hn] at size
    change 128+s9.length+msg.length+144≤Usize.max
    omega
  · have front : bytes (s9.val++msg.val) = bytes random.val ++ Spec.withContext (bytes msg.val) (bytes ctx.val) := by
      rw [s9_post,Array.val_to_slice,s6_post2,s7_post,s3_post2,s5_post,s4_post,s_post2,s2_post,s1_post,Array.val_to_slice]
      simp only [Array.val_to_slice,Array.repeat_val,List.slice,List.drop_zero,Nat.sub_zero]
      exact prefix_bytes random ctx msg i1 i1_post i2.val used.val i2_post (by rwa [cLen] at used_post) (by omega)
    have magnitude : i6=1536#i32 := by apply IScalar.eq_of_val_eq; rw [i6_post,i5_post]; decide +kernel
    have encoded : a.val=[6#u8,0#u8] := by rw [a_post,i7_post,magnitude]; decide +kernel
    have reset : (to_slice_mut_back1 s14).val=List.replicate 128 0#u8 := by
      rw [to_slice_mut_back1_post,Array.from_slice_val _ _ (by simpa [Slice.length,s13_post] using s14_post),s14_post1]
      simp [Slice.length,s13_post]
    have finish : bytes s22.val=S512.padFrom 128 (bytes inner.val) := by
      rw [s22_post,Array.val_to_slice,s18_post2,s20_post,s19_post,Array.val_to_slice,encoded,pad6_post,Array.set_val_eq,
        s15_post2,s17_post,s16_post,Array.val_to_slice,reset,setSlice_rep _ _ _ (by simp),i4_post]
      rw [show 128-inner.val.length=64 by simp]
      change bytes (((inner.val ++ List.replicate 64 0#u8).set 64 128#u8).setSlice! 126 [6#u8,0#u8]) = _
      have footer := finish_bytes inner.val 0#u8 6#u8 128#u8 61 (by simp)
      have footerEq : (((inner.val ++ List.replicate 64 0#u8).set 64 128#u8).setSlice! 126 [6#u8,0#u8]) =
          ((inner.val ++ List.replicate 64 0#u8).set 64 128#u8).set 126 6#u8 := by simpa using footer
      rw [footerEq]
      simpa only [bytes_set,bytes_append,bytes_replicate,Array.property,show (0#u8).bv=0#8 by decide +kernel, show (128#u8).bv=128#8 by decide +kernel, show (6#u8).bv=6#8 by decide +kernel] using fin512 (bytes inner.val) (by simp)
    rw [to_slice_mut_back2_post,Array.from_slice_val _ _ (by simpa [Slice.length,s24_post] using s23_post1),
      s24_post,s23_post,List.slice,Array.val_to_slice,List.drop_zero,Nat.sub_zero,bytes_take,a2_post,a1_post]
    rw [s12_post,Array.val_to_slice,take_drop0 _ _ (by simp),S512.H0_eq] at outer_post
    rw [s8_post,Array.val_to_slice,take_drop0 _ _ (by simp),S512.H0_eq] at state_post
    rw [state_post,← S512.sha512_prefix128 _ _ (by simp),front] at inner_post
    rw [take_drop0 _ _ (by rw [s22_post]; simp),finish,outer_post,← hashFrom512_one _ _ (by rw [← finish,s22_post]; simp),
      ← S512.sha512_prefix128 _ _ (by simp),inner_post,pad1_post,pad3_post]
    have hn : N.val≠16 := fun h => small (UScalar.eq_of_val_eq h)
    simp [Spec.PRFmsg,Spec.hmacSha512,paramsS,hp.n_eq,hn,show ¬128<N.val by omega]
end slhdsa.SegmentedApi
