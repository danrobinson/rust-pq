import Segmented.Instances
import Slhdsa.Proofs.HashMsg
open Aeneas Aeneas.Std Result
namespace slhdsa.Segmented

private theorem prefix_write {α} (z a b : List α) (i : Nat) (hi : i=a.length)
    (room : a.length+b.length≤z.length) :
    (a++z.drop a.length).setSlice! i b = (a++b)++z.drop (a++b).length := by
  rw [setSlice_gen a _ b i hi (by simp; omega)]
  simp [List.drop_drop]

private theorem five_writes {α} (z r p k d c : List α) (i j l u : Nat)
    (hi : i=r.length) (hj : j=i+p.length) (hl : l=j+k.length) (hu : u=l+d.length)
    (room : u+c.length≤z.length) :
    (((((z.setSlice! 0 r).setSlice! i p).setSlice! j k).setSlice! l d).setSlice! u c).take (u+c.length)
      = r++p++k++d++c := by
  have n0 := prefix_write z [] r 0 rfl (by simp; omega)
  simp only [List.length_nil,List.drop_zero,List.nil_append] at n0
  rw [n0,prefix_write z r p i hi (by omega),
    prefix_write z (r++p) k j (by simp; omega) (by simp; omega),
    prefix_write z (r++p++k) d l (by simp; omega) (by simp; omega),
    prefix_write z (r++p++k++d) c u (by simp; omega) (by simp; omega)]
  rw [show u+c.length=(r++p++k++d++c).length by simp; omega]
  exact List.take_left

attribute [local step] hash_extend_from_slice_u8_spec

set_option maxHeartbeats 1000000 in
theorem digest_spec {N : Usize} (p : params.Params) (hv : (paramsS p).Valid) (hPN : p.n=N)
    (r pk root : Std.Array U8 N) (ctx msg : Slice U8) (hc : ctx.length≤255)
    (hm : Room (2+ctx.length+msg.length) (msgSlack N.val)) :
    SegmentedApiRust.slh.message.digest p r pk root ctx msg ⦃ out =>
      bytes out.val = Spec.Hmsg (paramsS p) (bytes r.val) (bytes pk.val) (bytes root.val)
        (Spec.withContext (bytes msg.val) (bytes ctx.val)) ∧ out.length=p.m.val ⦄ := by
  unfold SegmentedApiRust.slh.message.digest
  have hN := nok_of_valid p hv hPN
  have hN32 := hN.le32
  have max := valid_m_le p hv
  have hR := hm
  simp only [Room,msgSlack] at hR
  step*
  all_goals try (subst_vars; scalar_tac)
  all_goals try (simp [s14_post, alloc.vec.Vec.with_capacity,alloc.vec.Vec.length]; scalar_tac)
  all_goals try (simp [seed1_post1,s15_post,s14_post,alloc.vec.Vec.with_capacity,alloc.vec.Vec.length]; scalar_tac)
  all_goals try (simp [seed2_post1,seed1_post1,s15_post,s14_post,s17_post,alloc.vec.Vec.with_capacity,alloc.vec.Vec.length]; scalar_tac)
  all_goals try (simp [Room,vec_deref_length,seed3_post1,seed2_post1,seed1_post1,s15_post,s14_post,s17_post,alloc.vec.Vec.with_capacity]; constructor <;> scalar_tac)
  all_goals try (simp [vec_deref_length,seed3_post1,seed2_post1,seed1_post1,s15_post,s14_post,s17_post,alloc.vec.Vec.with_capacity]; scalar_tac)
  all_goals try (simp only [Room] at *; split at hR <;> constructor <;> scalar_tac)
  all_goals
    refine ⟨?_,out_post1⟩
    have input : s16.val = r.val++pk.val++root.val++[0#u8,i1]++ctx.val := by
      rw [s16_post]
      simp only [List.slice,List.drop_zero,Nat.sub_zero,Array.val_to_slice,
        s12_post2,s13_post,s9_post2,s11_post,s10_post,s6_post2,s8_post,s7_post,
        s3_post2,s5_post,s4_post,s_post2,s2_post,s1_post,Array.make_val]
      have h : used.val=i7.val+ctx.val.length := by rw [used_post,i7_post,i5_post]; rfl
      rw [h]
      apply five_writes
      · simp
      · simpa using (show i2.val=N.val+N.val by omega)
      · simpa using (show i3.val=i2.val+N.val by omega)
      · simpa using i7_post
      · change i7.val+ctx.length≤(Array.repeat 353#usize 0#u8).val.length
        rw [Array.length_eq]
        change i7.val+ctx.length≤353
        omega
    have dom : bytes ([0#u8,i1]++ctx.val++msg.val) = Spec.withContext (bytes msg.val) (bytes ctx.val) := by
      simp [bytes,Spec.withContext,Spec.toByte,List.range,List.range.loop,i1_post]
      apply BitVec.eq_of_toNat_eq
      simp
    rw [out_post]
    simp only [vec_deref_val,seed3_post,seed2_post,seed1_post,s14_post,s15_post,s17_post,
      Array.val_to_slice,alloc.vec.Vec.with_capacity,bytes_append,d_post,input]
  · have eq : SegmentedApiRust.sha256.H0=sha256.H0 := by unfold SegmentedApiRust.sha256.H0 sha256.H0; rfl
    have hn : N.val=16 := by scalar_tac
    simp [eq,H0_eq,padFrom_zero,ser,hashFrom,Spec.SHA256.sha256,Spec.Hmsg,paramsS,hPN,hn,←dom]
  · have eq : SegmentedApiRust.sha512.H0=sha512.H0 := by unfold SegmentedApiRust.sha512.H0 sha512.H0; rfl
    have hn : N.val≠16 := by
      intro h
      have eqN : N=16#usize := by scalar_tac
      contradiction
    simp [eq,S512.H0_eq,S512.padFrom_zero,S512.ser,S512.hashFrom,Spec.SHA512.sha512,Spec.Hmsg,paramsS,hPN,hn,←dom]
end slhdsa.Segmented
