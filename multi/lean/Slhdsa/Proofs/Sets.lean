import Slhdsa.Proofs.Slh
open Aeneas Aeneas.Std Result

/-! The six parameter sets with fixed-size key types: the functions of
`sets.rs` are the generic ones at each row of Table 2. The array types fix the
key and seed lengths, so no length hypotheses remain. -/

namespace slhdsa

theorem n_128s : params.SHA2_128S.n.val = 16 := by simp [global_simps]
theorem n_128f : params.SHA2_128F.n.val = 16 := by simp [global_simps]
theorem n_192s : params.SHA2_192S.n.val = 24 := by simp [global_simps]
theorem n_192f : params.SHA2_192F.n.val = 24 := by simp [global_simps]
theorem n_256s : params.SHA2_256S.n.val = 32 := by simp [global_simps]
theorem n_256f : params.SHA2_256F.n.val = 32 := by simp [global_simps]

/-- Copying a vector of the right length into a zeroed array gives its bytes. -/
theorem from_slice_repeat_val {n : Usize} (s : Slice U8) (h : s.length = n.val) :
    (Array.from_slice (Array.repeat n 0#u8) s).val = s.val :=
  Array.from_slice_val _ _ (by scalar_tac)

/-! ## SLH-DSA-SHA2-128s -/

@[step]
theorem sha2_128s.slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.sha2_128s (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) ⦄ := by
  unfold sets.sha2_128s.slh_keygen_internal
  have hn := n_128s
  have hv := valid_128s
  step*
  have h1 : (Array.from_slice (Array.repeat 64#usize 0#u8) s5).val = s5.val :=
    from_slice_repeat_val _ (by scalar_tac)
  have h2 : (Array.from_slice (Array.repeat 32#usize 0#u8) s8).val = s8.val :=
    from_slice_repeat_val _ (by scalar_tac)
  simp_all [paramsS_128s]

@[step]
theorem sha2_128s.slh_sign_internal_spec (m : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 304) :
    sets.sha2_128s.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.sha2_128s (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_128s.slh_sign_internal
  have hn := n_128s
  have hv := valid_128s
  step*
  simp_all [paramsS_128s]

@[step]
theorem sha2_128s.slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 304) :
    sets.sha2_128s.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.sha2_128s (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.sha2_128s.slh_verify_internal
  have hn := n_128s
  have hv := valid_128s
  step*
  simp_all [paramsS_128s]

@[step]
theorem sha2_128s.slh_sign_spec (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 561) :
    sets.sha2_128s.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_128s.slh_sign
  have hn := n_128s
  have hv := valid_128s
  step*
  simp_all [paramsS_128s]

@[step]
theorem sha2_128s.slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 561) :
    sets.sha2_128s.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.sha2_128s (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val) ⦄ := by
  unfold sets.sha2_128s.slh_verify
  have hn := n_128s
  have hv := valid_128s
  step*
  simp_all [paramsS_128s]

/-! ## SLH-DSA-SHA2-128f -/

@[step]
theorem sha2_128f.slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    sets.sha2_128f.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.sha2_128f (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) ⦄ := by
  unfold sets.sha2_128f.slh_keygen_internal
  have hn := n_128f
  have hv := valid_128f
  step*
  have h1 : (Array.from_slice (Array.repeat 64#usize 0#u8) s5).val = s5.val :=
    from_slice_repeat_val _ (by scalar_tac)
  have h2 : (Array.from_slice (Array.repeat 32#usize 0#u8) s8).val = s8.val :=
    from_slice_repeat_val _ (by scalar_tac)
  simp_all [paramsS_128f]

@[step]
theorem sha2_128f.slh_sign_internal_spec (m : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 304) :
    sets.sha2_128f.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.sha2_128f (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_128f.slh_sign_internal
  have hn := n_128f
  have hv := valid_128f
  step*
  simp_all [paramsS_128f]

@[step]
theorem sha2_128f.slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 304) :
    sets.sha2_128f.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.sha2_128f (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.sha2_128f.slh_verify_internal
  have hn := n_128f
  have hv := valid_128f
  step*
  simp_all [paramsS_128f]

@[step]
theorem sha2_128f.slh_sign_spec (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 561) :
    sets.sha2_128f.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_128f.slh_sign
  have hn := n_128f
  have hv := valid_128f
  step*
  simp_all [paramsS_128f]

@[step]
theorem sha2_128f.slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 561) :
    sets.sha2_128f.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.sha2_128f (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val) ⦄ := by
  unfold sets.sha2_128f.slh_verify
  have hn := n_128f
  have hv := valid_128f
  step*
  simp_all [paramsS_128f]

/-! ## SLH-DSA-SHA2-192s -/

@[step]
theorem sha2_192s.slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 24#usize) :
    sets.sha2_192s.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.sha2_192s (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) ⦄ := by
  unfold sets.sha2_192s.slh_keygen_internal
  have hn := n_192s
  have hv := valid_192s
  step*
  have h1 : (Array.from_slice (Array.repeat 96#usize 0#u8) s5).val = s5.val :=
    from_slice_repeat_val _ (by scalar_tac)
  have h2 : (Array.from_slice (Array.repeat 48#usize 0#u8) s8).val = s8.val :=
    from_slice_repeat_val _ (by scalar_tac)
  simp_all [paramsS_192s]

@[step]
theorem sha2_192s.slh_sign_internal_spec (m : Slice U8) (sk : Array U8 96#usize)
    (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    sets.sha2_192s.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.sha2_192s (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_192s.slh_sign_internal
  have hn := n_192s
  have hv := valid_192s
  step*
  simp_all [paramsS_192s]

@[step]
theorem sha2_192s.slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 48#usize)
    (hm : Room m.length 304) :
    sets.sha2_192s.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.sha2_192s (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.sha2_192s.slh_verify_internal
  have hn := n_192s
  have hv := valid_192s
  step*
  simp_all [paramsS_192s]

@[step]
theorem sha2_192s.slh_sign_spec (m ctx : Slice U8) (sk : Array U8 96#usize)
    (addrnd : Array U8 24#usize) (hm : Room m.length 561) :
    sets.sha2_192s.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_192s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_192s.slh_sign
  have hn := n_192s
  have hv := valid_192s
  step*
  simp_all [paramsS_192s]

@[step]
theorem sha2_192s.slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 48#usize)
    (hm : Room m.length 561) :
    sets.sha2_192s.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.sha2_192s (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val) ⦄ := by
  unfold sets.sha2_192s.slh_verify
  have hn := n_192s
  have hv := valid_192s
  step*
  simp_all [paramsS_192s]

/-! ## SLH-DSA-SHA2-192f -/

@[step]
theorem sha2_192f.slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 24#usize) :
    sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.sha2_192f (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) ⦄ := by
  unfold sets.sha2_192f.slh_keygen_internal
  have hn := n_192f
  have hv := valid_192f
  step*
  have h1 : (Array.from_slice (Array.repeat 96#usize 0#u8) s5).val = s5.val :=
    from_slice_repeat_val _ (by scalar_tac)
  have h2 : (Array.from_slice (Array.repeat 48#usize 0#u8) s8).val = s8.val :=
    from_slice_repeat_val _ (by scalar_tac)
  simp_all [paramsS_192f]

@[step]
theorem sha2_192f.slh_sign_internal_spec (m : Slice U8) (sk : Array U8 96#usize)
    (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    sets.sha2_192f.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.sha2_192f (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_192f.slh_sign_internal
  have hn := n_192f
  have hv := valid_192f
  step*
  simp_all [paramsS_192f]

@[step]
theorem sha2_192f.slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 48#usize)
    (hm : Room m.length 304) :
    sets.sha2_192f.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.sha2_192f (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.sha2_192f.slh_verify_internal
  have hn := n_192f
  have hv := valid_192f
  step*
  simp_all [paramsS_192f]

@[step]
theorem sha2_192f.slh_sign_spec (m ctx : Slice U8) (sk : Array U8 96#usize)
    (addrnd : Array U8 24#usize) (hm : Room m.length 561) :
    sets.sha2_192f.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_192f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_192f.slh_sign
  have hn := n_192f
  have hv := valid_192f
  step*
  simp_all [paramsS_192f]

@[step]
theorem sha2_192f.slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 48#usize)
    (hm : Room m.length 561) :
    sets.sha2_192f.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.sha2_192f (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val) ⦄ := by
  unfold sets.sha2_192f.slh_verify
  have hn := n_192f
  have hv := valid_192f
  step*
  simp_all [paramsS_192f]

/-! ## SLH-DSA-SHA2-256s -/

@[step]
theorem sha2_256s.slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 32#usize) :
    sets.sha2_256s.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.sha2_256s (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) ⦄ := by
  unfold sets.sha2_256s.slh_keygen_internal
  have hn := n_256s
  have hv := valid_256s
  step*
  have h1 : (Array.from_slice (Array.repeat 128#usize 0#u8) s5).val = s5.val :=
    from_slice_repeat_val _ (by scalar_tac)
  have h2 : (Array.from_slice (Array.repeat 64#usize 0#u8) s8).val = s8.val :=
    from_slice_repeat_val _ (by scalar_tac)
  simp_all [paramsS_256s]

@[step]
theorem sha2_256s.slh_sign_internal_spec (m : Slice U8) (sk : Array U8 128#usize)
    (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    sets.sha2_256s.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.sha2_256s (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_256s.slh_sign_internal
  have hn := n_256s
  have hv := valid_256s
  step*
  simp_all [paramsS_256s]

@[step]
theorem sha2_256s.slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 64#usize)
    (hm : Room m.length 304) :
    sets.sha2_256s.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.sha2_256s (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.sha2_256s.slh_verify_internal
  have hn := n_256s
  have hv := valid_256s
  step*
  simp_all [paramsS_256s]

@[step]
theorem sha2_256s.slh_sign_spec (m ctx : Slice U8) (sk : Array U8 128#usize)
    (addrnd : Array U8 32#usize) (hm : Room m.length 561) :
    sets.sha2_256s.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_256s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_256s.slh_sign
  have hn := n_256s
  have hv := valid_256s
  step*
  simp_all [paramsS_256s]

@[step]
theorem sha2_256s.slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 64#usize)
    (hm : Room m.length 561) :
    sets.sha2_256s.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.sha2_256s (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val) ⦄ := by
  unfold sets.sha2_256s.slh_verify
  have hn := n_256s
  have hv := valid_256s
  step*
  simp_all [paramsS_256s]

/-! ## SLH-DSA-SHA2-256f -/

@[step]
theorem sha2_256f.slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 32#usize) :
    sets.sha2_256f.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.sha2_256f (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) ⦄ := by
  unfold sets.sha2_256f.slh_keygen_internal
  have hn := n_256f
  have hv := valid_256f
  step*
  have h1 : (Array.from_slice (Array.repeat 128#usize 0#u8) s5).val = s5.val :=
    from_slice_repeat_val _ (by scalar_tac)
  have h2 : (Array.from_slice (Array.repeat 64#usize 0#u8) s8).val = s8.val :=
    from_slice_repeat_val _ (by scalar_tac)
  simp_all [paramsS_256f]

@[step]
theorem sha2_256f.slh_sign_internal_spec (m : Slice U8) (sk : Array U8 128#usize)
    (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    sets.sha2_256f.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.sha2_256f (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_256f.slh_sign_internal
  have hn := n_256f
  have hv := valid_256f
  step*
  simp_all [paramsS_256f]

@[step]
theorem sha2_256f.slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 64#usize)
    (hm : Room m.length 304) :
    sets.sha2_256f.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.sha2_256f (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.sha2_256f.slh_verify_internal
  have hn := n_256f
  have hv := valid_256f
  step*
  simp_all [paramsS_256f]

@[step]
theorem sha2_256f.slh_sign_spec (m ctx : Slice U8) (sk : Array U8 128#usize)
    (addrnd : Array U8 32#usize) (hm : Room m.length 561) :
    sets.sha2_256f.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_256f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) ⦄ := by
  unfold sets.sha2_256f.slh_sign
  have hn := n_256f
  have hv := valid_256f
  step*
  simp_all [paramsS_256f]

@[step]
theorem sha2_256f.slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 64#usize)
    (hm : Room m.length 561) :
    sets.sha2_256f.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.sha2_256f (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val) ⦄ := by
  unfold sets.sha2_256f.slh_verify
  have hn := n_256f
  have hv := valid_256f
  step*
  simp_all [paramsS_256f]

end slhdsa
