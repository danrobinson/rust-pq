import Slhdsa.Proofs.Checked
open Aeneas Aeneas.Std Result

/-! The crate's interface, module `api`. -/

namespace slhdsa

theorem api_copy_val {n : Usize} (a : Array U8 n) (s : Slice U8) (h : s.length = n.val) :
    (Array.from_slice a s).val = s.val := Array.from_slice_val _ _ (by simpa using h)

@[step]
theorem api_keygen_spec (seeds : Array U8 48#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize) :
    api.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (Spec.block (bytes seeds.val) 0) (Spec.block (bytes seeds.val) 1)
          (Spec.block (bytes seeds.val) 2) ⦄ := by
  unfold api.keygen
  step*
  rw [to_slice_mut_back_post, to_slice_mut_back1_post, api_copy_val _ _ (by simp [s6_post, s5_post]),
    api_copy_val _ _ (by simp [s9_post, s8_post]), s6_post, s5_post, s9_post, s8_post]
  simp only [Array.val_to_slice]
  rw [s3_post, sk_seed_post1, sk_prf_post1, pk_seed_post1, s_post, s1_post, s2_post]
  simp

@[step]
theorem api_public_key_spec (sk : Array U8 64#usize) :
    api.public_key sk ⦃ r => bytes r.val = Spec.skPk (bytes sk.val) ⦄ := by
  unfold api.public_key
  simp only [global_simps]
  step*
  rw [to_slice_mut_back_post, api_copy_val _ _ (by simp [s2_post, s1_post]; scalar_tac), s2_post, s1_post]
  simp [List.slice, Spec.skPk, Spec.n, i_post, i1_post, List.take_of_length_le]

/-- `api.sign` is the plain signer `slh_sign`. -/
@[step]
theorem api_sign_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    api.sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold api.sign
  exact slh_sign_spec m ctx sk addrnd hm

@[step]
theorem api_sign_deterministic_spec (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) :
    api.sign_deterministic m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block (bytes sk.val) 2) ⦄ := by
  unfold api.sign_deterministic
  step*
  apply WP.spec_mono (slh_sign_spec m ctx sk pk_seed hm)
  intro r hr
  rw [hr, pk_seed_post1, s_post, Array.val_to_slice]

@[step]
theorem api_sign_checked_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    api.sign_checked m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSignChecked (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold api.sign_checked
  exact slh_sign_checked_spec m ctx sk addrnd hm

@[step]
theorem api_sign_deterministic_checked_spec (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) :
    api.sign_deterministic_checked m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSignChecked (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (Spec.block (bytes sk.val) 2) ⦄ := by
  unfold api.sign_deterministic_checked
  step*

@[step]
theorem api_verify_spec (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    api.verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold api.verify
  exact slh_verify_spec m sig ctx pk hm

end slhdsa
