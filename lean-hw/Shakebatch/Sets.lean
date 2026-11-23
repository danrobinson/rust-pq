import Facade.Suite
open Aeneas Aeneas.Std Result
namespace slhdsa

/-! Fixed-size SHAKE SDK calls, specialized to the six FIPS 205 parameter sets. -/

namespace shake_128s

private theorem fips : Shake.params sets.shake_128s.params.PARAMS=Spec.shake_128s := hP

@[step]
theorem slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    sets.shake_128s.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_128s (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold sets.shake_128s.slh_keygen_internal
  let* ⟨ s, back, s_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s1, back1, s1_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, s3, h1, h2, h3 ⟩ ← Shake.slh_keygen_internal_spec _ pn sk_seed sk_prf pk_seed s s1
    (by simp [Slice.length, s_post]) (by simp [Slice.length, s1_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    ← fips]
  exact h1

@[step]
theorem slh_sign_internal_spec (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    sets.shake_128s.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.shake_128s (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_128s.slh_sign_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_internal_spec _ pn m s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  rintro r ⟨h1, -⟩
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 32#usize) (hm : Room m.length 152) :
    sets.shake_128s.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.shake_128s (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_128s.slh_verify_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_internal_spec _ pn m sig s (by simp [s_post])
    (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_sign_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    sets.shake_128s.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_128s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_128s.slh_sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 32#usize) (hm : Room m.length 409) :
    sets.shake_128s.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_128s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_128s.slh_verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem keygen_spec (seeds : Array U8 48#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize) :
    sets.shake_128s.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_128s (Spec.block Spec.shake_128s (bytes seeds.val) 0)
          (Spec.block Spec.shake_128s (bytes seeds.val) 1) (Spec.block Spec.shake_128s (bytes seeds.val) 2) ⦄ := by
  unfold sets.shake_128s.keygen
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, back1, s2_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s3, s4, h1, h2, h3 ⟩ ← Shake.api_keygen_spec _ pn s s1 s2 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post]) (by simp [Slice.length, s2_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem public_key_spec (sk : Array U8 64#usize) :
    sets.shake_128s.public_key sk ⦃ r => bytes r.val = Spec.skPk Spec.shake_128s (bytes sk.val) ⦄ := by
  unfold sets.shake_128s.public_key
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, h1, h2 ⟩ ← Shake.api_public_key_spec _ pn s s1 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post])
  rw [back_post, from_slice_eq _ _ (by rw [h2]; rfl), h1, s_post, Array.val_to_slice, shape]
  rfl

@[step]
theorem sign_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    sets.shake_128s.sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_128s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_128s.sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem sign_deterministic_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (hm : Room m.length 409) :
    sets.shake_128s.sign_deterministic m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_128s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (Spec.block Spec.shake_128s (bytes sk.val) 2) ⦄ := by
  unfold sets.shake_128s.sign_deterministic
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_deterministic_spec _ pn m ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem verify_spec (m sig ctx : Slice U8) (pk : Array U8 32#usize) (hm : Room m.length 409) :
    sets.shake_128s.verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_128s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_128s.verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

end shake_128s

namespace shake_128f

private theorem fips : Shake.params sets.shake_128f.params.PARAMS=Spec.shake_128f := hP

@[step]
theorem slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    sets.shake_128f.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_128f (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold sets.shake_128f.slh_keygen_internal
  let* ⟨ s, back, s_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s1, back1, s1_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, s3, h1, h2, h3 ⟩ ← Shake.slh_keygen_internal_spec _ pn sk_seed sk_prf pk_seed s s1
    (by simp [Slice.length, s_post]) (by simp [Slice.length, s1_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    ← fips]
  exact h1

@[step]
theorem slh_sign_internal_spec (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    sets.shake_128f.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.shake_128f (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_128f.slh_sign_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_internal_spec _ pn m s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  rintro r ⟨h1, -⟩
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 32#usize) (hm : Room m.length 152) :
    sets.shake_128f.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.shake_128f (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_128f.slh_verify_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_internal_spec _ pn m sig s (by simp [s_post])
    (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_sign_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    sets.shake_128f.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_128f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_128f.slh_sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 32#usize) (hm : Room m.length 409) :
    sets.shake_128f.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_128f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_128f.slh_verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem keygen_spec (seeds : Array U8 48#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize) :
    sets.shake_128f.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_128f (Spec.block Spec.shake_128f (bytes seeds.val) 0)
          (Spec.block Spec.shake_128f (bytes seeds.val) 1) (Spec.block Spec.shake_128f (bytes seeds.val) 2) ⦄ := by
  unfold sets.shake_128f.keygen
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, back1, s2_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s3, s4, h1, h2, h3 ⟩ ← Shake.api_keygen_spec _ pn s s1 s2 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post]) (by simp [Slice.length, s2_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem public_key_spec (sk : Array U8 64#usize) :
    sets.shake_128f.public_key sk ⦃ r => bytes r.val = Spec.skPk Spec.shake_128f (bytes sk.val) ⦄ := by
  unfold sets.shake_128f.public_key
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, h1, h2 ⟩ ← Shake.api_public_key_spec _ pn s s1 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post])
  rw [back_post, from_slice_eq _ _ (by rw [h2]; rfl), h1, s_post, Array.val_to_slice, shape]
  rfl

@[step]
theorem sign_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    sets.shake_128f.sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_128f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_128f.sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem sign_deterministic_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (hm : Room m.length 409) :
    sets.shake_128f.sign_deterministic m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_128f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (Spec.block Spec.shake_128f (bytes sk.val) 2) ⦄ := by
  unfold sets.shake_128f.sign_deterministic
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_deterministic_spec _ pn m ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem verify_spec (m sig ctx : Slice U8) (pk : Array U8 32#usize) (hm : Room m.length 409) :
    sets.shake_128f.verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_128f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_128f.verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

end shake_128f

namespace shake_192s

private theorem fips : Shake.params sets.shake_192s.params.PARAMS=Spec.shake_192s := hP

@[step]
theorem slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 24#usize) :
    sets.shake_192s.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_192s (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold sets.shake_192s.slh_keygen_internal
  let* ⟨ s, back, s_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s1, back1, s1_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, s3, h1, h2, h3 ⟩ ← Shake.slh_keygen_internal_spec _ pn sk_seed sk_prf pk_seed s s1
    (by simp [Slice.length, s_post]) (by simp [Slice.length, s1_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    ← fips]
  exact h1

@[step]
theorem slh_sign_internal_spec (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 304) :
    sets.shake_192s.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.shake_192s (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_192s.slh_sign_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_internal_spec _ pn m s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  rintro r ⟨h1, -⟩
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 48#usize) (hm : Room m.length 304) :
    sets.shake_192s.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.shake_192s (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_192s.slh_verify_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_internal_spec _ pn m sig s (by simp [s_post])
    (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_sign_spec (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    sets.shake_192s.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_192s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_192s.slh_sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 48#usize) (hm : Room m.length 561) :
    sets.shake_192s.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_192s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_192s.slh_verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem keygen_spec (seeds : Array U8 72#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize) :
    sets.shake_192s.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_192s (Spec.block Spec.shake_192s (bytes seeds.val) 0)
          (Spec.block Spec.shake_192s (bytes seeds.val) 1) (Spec.block Spec.shake_192s (bytes seeds.val) 2) ⦄ := by
  unfold sets.shake_192s.keygen
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, back1, s2_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s3, s4, h1, h2, h3 ⟩ ← Shake.api_keygen_spec _ pn s s1 s2 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post]) (by simp [Slice.length, s2_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem public_key_spec (sk : Array U8 96#usize) :
    sets.shake_192s.public_key sk ⦃ r => bytes r.val = Spec.skPk Spec.shake_192s (bytes sk.val) ⦄ := by
  unfold sets.shake_192s.public_key
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, h1, h2 ⟩ ← Shake.api_public_key_spec _ pn s s1 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post])
  rw [back_post, from_slice_eq _ _ (by rw [h2]; rfl), h1, s_post, Array.val_to_slice, shape]
  rfl

@[step]
theorem sign_spec (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    sets.shake_192s.sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_192s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_192s.sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem sign_deterministic_spec (m ctx : Slice U8) (sk : Array U8 96#usize) (hm : Room m.length 561) :
    sets.shake_192s.sign_deterministic m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_192s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (Spec.block Spec.shake_192s (bytes sk.val) 2) ⦄ := by
  unfold sets.shake_192s.sign_deterministic
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_deterministic_spec _ pn m ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem verify_spec (m sig ctx : Slice U8) (pk : Array U8 48#usize) (hm : Room m.length 561) :
    sets.shake_192s.verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_192s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_192s.verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

end shake_192s

namespace shake_192f

private theorem fips : Shake.params sets.shake_192f.params.PARAMS=Spec.shake_192f := hP

@[step]
theorem slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 24#usize) :
    sets.shake_192f.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_192f (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold sets.shake_192f.slh_keygen_internal
  let* ⟨ s, back, s_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s1, back1, s1_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, s3, h1, h2, h3 ⟩ ← Shake.slh_keygen_internal_spec _ pn sk_seed sk_prf pk_seed s s1
    (by simp [Slice.length, s_post]) (by simp [Slice.length, s1_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    ← fips]
  exact h1

@[step]
theorem slh_sign_internal_spec (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 304) :
    sets.shake_192f.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.shake_192f (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_192f.slh_sign_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_internal_spec _ pn m s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  rintro r ⟨h1, -⟩
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 48#usize) (hm : Room m.length 304) :
    sets.shake_192f.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.shake_192f (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_192f.slh_verify_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_internal_spec _ pn m sig s (by simp [s_post])
    (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_sign_spec (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    sets.shake_192f.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_192f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_192f.slh_sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 48#usize) (hm : Room m.length 561) :
    sets.shake_192f.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_192f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_192f.slh_verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem keygen_spec (seeds : Array U8 72#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize) :
    sets.shake_192f.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_192f (Spec.block Spec.shake_192f (bytes seeds.val) 0)
          (Spec.block Spec.shake_192f (bytes seeds.val) 1) (Spec.block Spec.shake_192f (bytes seeds.val) 2) ⦄ := by
  unfold sets.shake_192f.keygen
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, back1, s2_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s3, s4, h1, h2, h3 ⟩ ← Shake.api_keygen_spec _ pn s s1 s2 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post]) (by simp [Slice.length, s2_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem public_key_spec (sk : Array U8 96#usize) :
    sets.shake_192f.public_key sk ⦃ r => bytes r.val = Spec.skPk Spec.shake_192f (bytes sk.val) ⦄ := by
  unfold sets.shake_192f.public_key
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, h1, h2 ⟩ ← Shake.api_public_key_spec _ pn s s1 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post])
  rw [back_post, from_slice_eq _ _ (by rw [h2]; rfl), h1, s_post, Array.val_to_slice, shape]
  rfl

@[step]
theorem sign_spec (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    sets.shake_192f.sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_192f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_192f.sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem sign_deterministic_spec (m ctx : Slice U8) (sk : Array U8 96#usize) (hm : Room m.length 561) :
    sets.shake_192f.sign_deterministic m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_192f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (Spec.block Spec.shake_192f (bytes sk.val) 2) ⦄ := by
  unfold sets.shake_192f.sign_deterministic
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_deterministic_spec _ pn m ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem verify_spec (m sig ctx : Slice U8) (pk : Array U8 48#usize) (hm : Room m.length 561) :
    sets.shake_192f.verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_192f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_192f.verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

end shake_192f

namespace shake_256s

private theorem fips : Shake.params sets.shake_256s.params.PARAMS=Spec.shake_256s := hP

@[step]
theorem slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 32#usize) :
    sets.shake_256s.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_256s (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold sets.shake_256s.slh_keygen_internal
  let* ⟨ s, back, s_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s1, back1, s1_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, s3, h1, h2, h3 ⟩ ← Shake.slh_keygen_internal_spec _ pn sk_seed sk_prf pk_seed s s1
    (by simp [Slice.length, s_post]) (by simp [Slice.length, s1_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    ← fips]
  exact h1

@[step]
theorem slh_sign_internal_spec (m : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 304) :
    sets.shake_256s.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.shake_256s (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_256s.slh_sign_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_internal_spec _ pn m s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  rintro r ⟨h1, -⟩
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 64#usize) (hm : Room m.length 304) :
    sets.shake_256s.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.shake_256s (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_256s.slh_verify_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_internal_spec _ pn m sig s (by simp [s_post])
    (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_sign_spec (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    sets.shake_256s.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_256s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_256s.slh_sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 64#usize) (hm : Room m.length 561) :
    sets.shake_256s.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_256s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_256s.slh_verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem keygen_spec (seeds : Array U8 96#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize) :
    sets.shake_256s.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_256s (Spec.block Spec.shake_256s (bytes seeds.val) 0)
          (Spec.block Spec.shake_256s (bytes seeds.val) 1) (Spec.block Spec.shake_256s (bytes seeds.val) 2) ⦄ := by
  unfold sets.shake_256s.keygen
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, back1, s2_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s3, s4, h1, h2, h3 ⟩ ← Shake.api_keygen_spec _ pn s s1 s2 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post]) (by simp [Slice.length, s2_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem public_key_spec (sk : Array U8 128#usize) :
    sets.shake_256s.public_key sk ⦃ r => bytes r.val = Spec.skPk Spec.shake_256s (bytes sk.val) ⦄ := by
  unfold sets.shake_256s.public_key
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, h1, h2 ⟩ ← Shake.api_public_key_spec _ pn s s1 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post])
  rw [back_post, from_slice_eq _ _ (by rw [h2]; rfl), h1, s_post, Array.val_to_slice, shape]
  rfl

@[step]
theorem sign_spec (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    sets.shake_256s.sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_256s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_256s.sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem sign_deterministic_spec (m ctx : Slice U8) (sk : Array U8 128#usize) (hm : Room m.length 561) :
    sets.shake_256s.sign_deterministic m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_256s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (Spec.block Spec.shake_256s (bytes sk.val) 2) ⦄ := by
  unfold sets.shake_256s.sign_deterministic
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_deterministic_spec _ pn m ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem verify_spec (m sig ctx : Slice U8) (pk : Array U8 64#usize) (hm : Room m.length 561) :
    sets.shake_256s.verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_256s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_256s.verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

end shake_256s

namespace shake_256f

private theorem fips : Shake.params sets.shake_256f.params.PARAMS=Spec.shake_256f := hP

@[step]
theorem slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 32#usize) :
    sets.shake_256f.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_256f (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold sets.shake_256f.slh_keygen_internal
  let* ⟨ s, back, s_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s1, back1, s1_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, s3, h1, h2, h3 ⟩ ← Shake.slh_keygen_internal_spec _ pn sk_seed sk_prf pk_seed s s1
    (by simp [Slice.length, s_post]) (by simp [Slice.length, s1_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    ← fips]
  exact h1

@[step]
theorem slh_sign_internal_spec (m : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 304) :
    sets.shake_256f.slh_sign_internal m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal Spec.shake_256f (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_256f.slh_sign_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_internal_spec _ pn m s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  rintro r ⟨h1, -⟩
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 64#usize) (hm : Room m.length 304) :
    sets.shake_256f.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal Spec.shake_256f (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_256f.slh_verify_internal
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_internal_spec _ pn m sig s (by simp [s_post])
    (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_sign_spec (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    sets.shake_256f.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_256f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_256f.slh_sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 64#usize) (hm : Room m.length 561) :
    sets.shake_256f.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_256f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_256f.slh_verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.slh_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem keygen_spec (seeds : Array U8 96#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize) :
    sets.shake_256f.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal Spec.shake_256f (Spec.block Spec.shake_256f (bytes seeds.val) 0)
          (Spec.block Spec.shake_256f (bytes seeds.val) 1) (Spec.block Spec.shake_256f (bytes seeds.val) 2) ⦄ := by
  unfold sets.shake_256f.keygen
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, back1, s2_post, back1_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s3, s4, h1, h2, h3 ⟩ ← Shake.api_keygen_spec _ pn s s1 s2 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post]) (by simp [Slice.length, s2_post])
  rw [back_post, back1_post, from_slice_eq _ _ (by rw [h2]; rfl), from_slice_eq _ _ (by rw [h3]; rfl),
    h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem public_key_spec (sk : Array U8 128#usize) :
    sets.shake_256f.public_key sk ⦃ r => bytes r.val = Spec.skPk Spec.shake_256f (bytes sk.val) ⦄ := by
  unfold sets.shake_256f.public_key
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, h1, h2 ⟩ ← Shake.api_public_key_spec _ pn s s1 (by simp [Slice.length, s_post])
    (by simp [Slice.length, s1_post])
  rw [back_post, from_slice_eq _ _ (by rw [h2]; rfl), h1, s_post, Array.val_to_slice, shape]
  rfl

@[step]
theorem sign_spec (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    sets.shake_256f.sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_256f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold sets.shake_256f.sign
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_spec _ pn m ctx s addrnd (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

@[step]
theorem sign_deterministic_spec (m ctx : Slice U8) (sk : Array U8 128#usize) (hm : Room m.length 561) :
    sets.shake_256f.sign_deterministic m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.shake_256f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (Spec.block Spec.shake_256f (bytes sk.val) 2) ⦄ := by
  unfold sets.shake_256f.sign_deterministic
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_sign_deterministic_spec _ pn m ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips, shape, block_shape]

@[step]
theorem verify_spec (m sig ctx : Slice U8) (pk : Array U8 64#usize) (hm : Room m.length 561) :
    sets.shake_256f.verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify Spec.shake_256f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold sets.shake_256f.verify
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  apply WP.spec_mono (Shake.api_verify_spec _ pn m sig ctx s (by simp [s_post]) (by rw [slack]; exact hm))
  intro r h1
  rw [h1, s_post, Array.val_to_slice, fips]

end shake_256f

end slhdsa
