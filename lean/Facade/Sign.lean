import Facade.Suite
import Facade.Multipart
import Slhdsa.Proofs.Adapter
import Slhdsa.Proofs.Sets

open Aeneas Aeneas.Std Result
open slhdsa (bytes paramsS PN Room msgSlack)
namespace slh_dsa

theorem scrub_returns : scrub.scrub_stack = ok () := by
  unfold scrub.scrub_stack Array.Insts.ZeroizeZeroize.zeroize
  have h := List.mapM_with_length_spec (post := fun _ (_ : U8) => True)
    (l := (Array.repeat 65536#usize 0#u8).val)
    (f := (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes).zeroize)
    (by intro i hi; change ok 0#u8 ⦃ _ => True ⦄; simp)
  obtain ⟨xs, hx, _⟩ := _root_.slhdsa.spec_imp_exists h
  simp [hx]

def signatureBytes {P Sk Vk : Type} {Sig : Usize}
    (r : Std.core.result.Result (signature_encoding.Signature P Sk Vk (Array U8 Sig)) signature.error.Error) :
    Option Spec.Bytes :=
  match r with
  | .Ok sig => some (bytes sig.bytes.val)
  | .Err _ => none

private theorem raw_sign_spec (family : Spec.HashFamily) {P Vk : Type} {Sk Sig N : Usize}
    (C : params.Core P (Array U8 Sk) Vk (Array U8 Sig))
    (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (hsk : Sk.val = 4 * N.val) (hsig : Sig.val = (paramsS p).sigBytes)
    (fresh : C.SignatureStorageInst.BufferInst.zeroed = ok (Array.repeat Sig 0#u8))
    (getKey : C.SigningKeyStorageInst.BufferInst.as_slice = fun a => ok (Array.to_slice a))
    (getSig : C.SignatureStorageInst.BufferInst.as_mut_slice = fun a => ok (Array.to_slice_mut a))
    (sk : signing_key.SigningKey P (Array U8 Sk) Vk (Array U8 Sig))
    (parts : Slice (Slice U8)) (ctx : Slice U8) (rnd : Option (Slice U8))
    (has : Bool) (rand : Slice U8)
    (dispatch : ∀ m ctx key dest, C.sign m ctx key rnd dest =
      _root_.slhdsa.Suite.sign_into family N p m ctx key has rand dest)
    (goodRand : has = true → rand.length = N.val)
    (hm : Room (parts.val.flatMap (fun part => part.val)).length (msgSlack N.val + 257)) :
    signing_key.SigningKey.raw_try_sign_with_context C sk parts ctx rnd ⦃ r =>
      signatureBytes r =
      Spec.slhSign (_root_.slhdsa.Suite.view family p) (bytes (parts.val.flatMap (fun part => part.val)))
        (bytes ctx.val) (bytes sk.bytes.val) (_root_.slhdsa.randS (paramsS p) (bytes sk.bytes.val) has rand) ⦄ := by
  unfold signing_key.SigningKey.raw_try_sign_with_context
  have fits : (parts.val.flatMap (fun part => part.val)).length ≤ Usize.max := by
    unfold Room at hm; omega
  obtain ⟨m, hjoin, hm'⟩ := _root_.slhdsa.spec_imp_exists (multipart.join_spec parts fits)
  rw [hjoin]
  simp only [bind_ok, fresh, getKey, getSig, Array.to_slice_mut, dispatch]
  let dest := Array.repeat Sig 0#u8
  obtain ⟨⟨b, buf⟩, hs, okIff, success, _⟩ := _root_.slhdsa.spec_imp_exists
    (_root_.slhdsa.Suite.adapter_sign_into_spec family p hp (alloc.vec.Vec.deref m) ctx sk.bytes.to_slice has rand dest.to_slice
      (by simpa [Slice.length] using hsk) (by simpa [Slice.length] using hsig) goodRand
      (by simpa only [Slice.length, _root_.slhdsa.vec_deref_val, hm'] using hm))
  simp only [uncurry]
  rw [hs]
  simp only [_root_.slhdsa.vec_deref_val, hm', Array.val_to_slice] at success
  cases b with
  | false =>
    have long : (bytes ctx.val).length > 255 := by simp at okIff; simpa [Slice.length] using okIff
    simp only [bind_ok, uncurry, Bool.false_eq_true, ↓reduceIte, signature.error.Error.new, WP.spec_ok, signatureBytes, Spec.slhSign, long]
  | true =>
    have eqn := success rfl
    have short : ¬ (bytes ctx.val).length > 255 := by
      have h := okIff.mp rfl
      simpa [Slice.length] using h
    have sized : buf.val.length = Sig.val := by
      simp only [Spec.slhSign, short, ↓reduceIte, Option.some.injEq] at eqn
      have h := congrArg List.length eqn
      simpa [_root_.slhdsa.bytes_length, Spec.slhSignInternal_length _ (_root_.slhdsa.Suite.valid family hp), _root_.slhdsa.Suite.sigBytes_view, hsig] using h.symm
    simp only [bind_ok, uncurry, ↓reduceIte, WP.spec_ok, signatureBytes]
    rw [Array.from_slice_val _ _ sized]
    exact eqn.symm

-- Per-set specializations of the deterministic RustCrypto Signer implementation.

theorem sha2_128s_sign (sk : signing_key.SigningKey params.Sha2_128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize))
    (m : Slice U8) (hm : Room m.length 409) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.sha2_128s (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.sha2_128s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .sha2 params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 _ _root_.slhdsa.sha2_128s.pn
    (by decide) (by rw [_root_.slhdsa.sha2_128s.hP]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.sha2_128s.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.sha2_128s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_128s.hP, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_128s_sign

theorem sha2_128f_sign (sk : signing_key.SigningKey params.Sha2_128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize))
    (m : Slice U8) (hm : Room m.length 409) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.sha2_128f (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.sha2_128f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .sha2 params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 _ _root_.slhdsa.sha2_128f.pn
    (by decide) (by rw [_root_.slhdsa.sha2_128f.hP]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.sha2_128f.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.sha2_128f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_128f.hP, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_128f_sign

theorem sha2_192s_sign (sk : signing_key.SigningKey params.Sha2_192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize))
    (m : Slice U8) (hm : Room m.length 561) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.sha2_192s (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.sha2_192s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .sha2 params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 _ _root_.slhdsa.sha2_192s.pn
    (by decide) (by rw [_root_.slhdsa.sha2_192s.hP]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.sha2_192s.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.sha2_192s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_192s.hP, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_192s_sign

theorem sha2_192f_sign (sk : signing_key.SigningKey params.Sha2_192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize))
    (m : Slice U8) (hm : Room m.length 561) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.sha2_192f (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.sha2_192f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .sha2 params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 _ _root_.slhdsa.sha2_192f.pn
    (by decide) (by rw [_root_.slhdsa.sha2_192f.hP]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.sha2_192f.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.sha2_192f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_192f.hP, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_192f_sign

theorem sha2_256s_sign (sk : signing_key.SigningKey params.Sha2_256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize))
    (m : Slice U8) (hm : Room m.length 561) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.sha2_256s (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.sha2_256s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .sha2 params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 _ _root_.slhdsa.sha2_256s.pn
    (by decide) (by rw [_root_.slhdsa.sha2_256s.hP]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.sha2_256s.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.sha2_256s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_256s.hP, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_256s_sign

theorem sha2_256f_sign (sk : signing_key.SigningKey params.Sha2_256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize))
    (m : Slice U8) (hm : Room m.length 561) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.sha2_256f (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.sha2_256f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .sha2 params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 _ _root_.slhdsa.sha2_256f.pn
    (by decide) (by rw [_root_.slhdsa.sha2_256f.hP]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.sha2_256f.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.sha2_256f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_256f.hP, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_256f_sign
-- Public context-string APIs.

theorem sha2_128s_sign_with_context (sk : signing_key.SigningKey params.Sha2_128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 16)
    (hm : Room m.length 409) :
    signing_key.SigningKey.try_sign_with_context params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.sha2_128s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .sha2 params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 _ _root_.slhdsa.sha2_128s.pn
    (by decide) (by rw [_root_.slhdsa.sha2_128s.hP]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.sha2_128s.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.sha2_128s.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_128s.hP, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_128s_sign_with_context

theorem sha2_128f_sign_with_context (sk : signing_key.SigningKey params.Sha2_128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 16)
    (hm : Room m.length 409) :
    signing_key.SigningKey.try_sign_with_context params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.sha2_128f (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.sha2_128f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .sha2 params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 _ _root_.slhdsa.sha2_128f.pn
    (by decide) (by rw [_root_.slhdsa.sha2_128f.hP]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.sha2_128f.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.sha2_128f.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_128f.hP, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_128f_sign_with_context

theorem sha2_192s_sign_with_context (sk : signing_key.SigningKey params.Sha2_192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 24)
    (hm : Room m.length 561) :
    signing_key.SigningKey.try_sign_with_context params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.sha2_192s (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.sha2_192s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .sha2 params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 _ _root_.slhdsa.sha2_192s.pn
    (by decide) (by rw [_root_.slhdsa.sha2_192s.hP]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.sha2_192s.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.sha2_192s.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_192s.hP, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_192s_sign_with_context

theorem sha2_192f_sign_with_context (sk : signing_key.SigningKey params.Sha2_192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 24)
    (hm : Room m.length 561) :
    signing_key.SigningKey.try_sign_with_context params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.sha2_192f (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.sha2_192f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .sha2 params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 _ _root_.slhdsa.sha2_192f.pn
    (by decide) (by rw [_root_.slhdsa.sha2_192f.hP]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.sha2_192f.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.sha2_192f.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_192f.hP, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_192f_sign_with_context

theorem sha2_256s_sign_with_context (sk : signing_key.SigningKey params.Sha2_256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 32)
    (hm : Room m.length 561) :
    signing_key.SigningKey.try_sign_with_context params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.sha2_256s (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.sha2_256s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .sha2 params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 _ _root_.slhdsa.sha2_256s.pn
    (by decide) (by rw [_root_.slhdsa.sha2_256s.hP]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.sha2_256s.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.sha2_256s.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_256s.hP, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_256s_sign_with_context

theorem sha2_256f_sign_with_context (sk : signing_key.SigningKey params.Sha2_256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 32)
    (hm : Room m.length 561) :
    signing_key.SigningKey.try_sign_with_context params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.sha2_256f (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.sha2_256f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .sha2 params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 _ _root_.slhdsa.sha2_256f.pn
    (by decide) (by rw [_root_.slhdsa.sha2_256f.hP]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.sha2_256f.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.sha2_256f.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_256f.hP, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms sha2_256f_sign_with_context
theorem shake_128s_sign (sk : signing_key.SigningKey params.Shake128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize))
    (m : Slice U8) (hm : Room m.length 409) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.shake_128s (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.shake_128s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .shake params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 _ _root_.slhdsa.shake_128s.pn
    (by decide) (by rw [_root_.slhdsa.shake_128s.shape]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.shake_128s.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.shake_128s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_128s.block_shape, _root_.slhdsa.shake_128s.hP, _root_.slhdsa.shake_128s.shape, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_128s_sign

theorem shake_128f_sign (sk : signing_key.SigningKey params.Shake128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize))
    (m : Slice U8) (hm : Room m.length 409) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.shake_128f (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.shake_128f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .shake params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 _ _root_.slhdsa.shake_128f.pn
    (by decide) (by rw [_root_.slhdsa.shake_128f.shape]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.shake_128f.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.shake_128f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_128f.block_shape, _root_.slhdsa.shake_128f.hP, _root_.slhdsa.shake_128f.shape, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_128f_sign

theorem shake_192s_sign (sk : signing_key.SigningKey params.Shake192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize))
    (m : Slice U8) (hm : Room m.length 561) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.shake_192s (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.shake_192s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .shake params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 _ _root_.slhdsa.shake_192s.pn
    (by decide) (by rw [_root_.slhdsa.shake_192s.shape]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.shake_192s.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.shake_192s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_192s.block_shape, _root_.slhdsa.shake_192s.hP, _root_.slhdsa.shake_192s.shape, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_192s_sign

theorem shake_192f_sign (sk : signing_key.SigningKey params.Shake192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize))
    (m : Slice U8) (hm : Room m.length 561) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.shake_192f (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.shake_192f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .shake params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 _ _root_.slhdsa.shake_192f.pn
    (by decide) (by rw [_root_.slhdsa.shake_192f.shape]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.shake_192f.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.shake_192f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_192f.block_shape, _root_.slhdsa.shake_192f.hP, _root_.slhdsa.shake_192f.shape, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_192f_sign

theorem shake_256s_sign (sk : signing_key.SigningKey params.Shake256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize))
    (m : Slice U8) (hm : Room m.length 561) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.shake_256s (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.shake_256s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .shake params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 _ _root_.slhdsa.shake_256s.pn
    (by decide) (by rw [_root_.slhdsa.shake_256s.shape]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.shake_256s.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.shake_256s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_256s.block_shape, _root_.slhdsa.shake_256s.hP, _root_.slhdsa.shake_256s.shape, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_256s_sign

theorem shake_256f_sign (sk : signing_key.SigningKey params.Shake256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize))
    (m : Slice U8) (hm : Room m.length 561) :
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
      params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 sk m ⦃ r =>
      signatureBytes r =
      Spec.slhSign Spec.shake_256f (bytes m.val) [] (bytes sk.bytes.val)
        (Spec.block Spec.shake_256f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_sign_spec .shake params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 _ _root_.slhdsa.shake_256f.pn
    (by decide) (by rw [_root_.slhdsa.shake_256f.shape]; decide) rfl rfl rfl sk parts ctx none false ctx
    (by
      intro msg context key dest
      simp only [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.sign, params.split, lift, bind_ok,
        uncurry, slhdsa.sets.shake_256f.params.PARAMS, scrub_returns]
      exact Std.bind_pure _)
    (by simp) (by rw [joined, _root_.slhdsa.shake_256f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_256f.block_shape, _root_.slhdsa.shake_256f.hP, _root_.slhdsa.shake_256f.shape, joined, empty, _root_.slhdsa.randS, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_256f_sign
-- Public context-string APIs.

theorem shake_128s_sign_with_context (sk : signing_key.SigningKey params.Shake128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 16)
    (hm : Room m.length 409) :
    signing_key.SigningKey.try_sign_with_context params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.shake_128s (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.shake_128s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .shake params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 _ _root_.slhdsa.shake_128s.pn
    (by decide) (by rw [_root_.slhdsa.shake_128s.shape]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.shake_128s.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.shake_128s.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.shake_128s.block_shape, _root_.slhdsa.shake_128s.hP, _root_.slhdsa.shake_128s.shape, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_128s_sign_with_context

theorem shake_128f_sign_with_context (sk : signing_key.SigningKey params.Shake128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 16)
    (hm : Room m.length 409) :
    signing_key.SigningKey.try_sign_with_context params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.shake_128f (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.shake_128f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .shake params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 _ _root_.slhdsa.shake_128f.pn
    (by decide) (by rw [_root_.slhdsa.shake_128f.shape]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.shake_128f.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.shake_128f.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.shake_128f.block_shape, _root_.slhdsa.shake_128f.hP, _root_.slhdsa.shake_128f.shape, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_128f_sign_with_context

theorem shake_192s_sign_with_context (sk : signing_key.SigningKey params.Shake192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 24)
    (hm : Room m.length 561) :
    signing_key.SigningKey.try_sign_with_context params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.shake_192s (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.shake_192s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .shake params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 _ _root_.slhdsa.shake_192s.pn
    (by decide) (by rw [_root_.slhdsa.shake_192s.shape]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.shake_192s.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.shake_192s.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.shake_192s.block_shape, _root_.slhdsa.shake_192s.hP, _root_.slhdsa.shake_192s.shape, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_192s_sign_with_context

theorem shake_192f_sign_with_context (sk : signing_key.SigningKey params.Shake192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 24)
    (hm : Room m.length 561) :
    signing_key.SigningKey.try_sign_with_context params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.shake_192f (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.shake_192f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .shake params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 _ _root_.slhdsa.shake_192f.pn
    (by decide) (by rw [_root_.slhdsa.shake_192f.shape]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.shake_192f.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.shake_192f.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.shake_192f.block_shape, _root_.slhdsa.shake_192f.hP, _root_.slhdsa.shake_192f.shape, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_192f_sign_with_context

theorem shake_256s_sign_with_context (sk : signing_key.SigningKey params.Shake256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 32)
    (hm : Room m.length 561) :
    signing_key.SigningKey.try_sign_with_context params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.shake_256s (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.shake_256s (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .shake params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 _ _root_.slhdsa.shake_256s.pn
    (by decide) (by rw [_root_.slhdsa.shake_256s.shape]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.shake_256s.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.shake_256s.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.shake_256s.block_shape, _root_.slhdsa.shake_256s.hP, _root_.slhdsa.shake_256s.shape, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_256s_sign_with_context

theorem shake_256f_sign_with_context (sk : signing_key.SigningKey params.Shake256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize)) (m ctx : Slice U8)
    (rnd : Option (Slice U8)) (hr : ∀ r ∈ rnd, r.length = 32)
    (hm : Room m.length 561) :
    signing_key.SigningKey.try_sign_with_context params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 sk m ctx rnd ⦃ ret =>
      signatureBytes ret = Spec.slhSign Spec.shake_256f (bytes m.val) (bytes ctx.val) (bytes sk.bytes.val)
        (match rnd with
         | some r => bytes r.val
         | none => Spec.block Spec.shake_256f (bytes sk.bytes.val) 2) ⦄ := by
  unfold signing_key.SigningKey.try_sign_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  let empty := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_sign_spec .shake params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 _ _root_.slhdsa.shake_256f.pn
    (by decide) (by rw [_root_.slhdsa.shake_256f.shape]; decide) rfl rfl rfl sk parts ctx rnd rnd.isSome (rnd.getD empty)
    (by
      intro msg context key dest
      cases rnd <;> simp only [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.sign, params.split, lift, bind_ok, uncurry,
        slhdsa.sets.shake_256f.params.PARAMS, scrub_returns, Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _)
    (by cases rnd with | none => simp | some r => simpa using hr r (by simp))
    (by rw [joined, _root_.slhdsa.shake_256f.slack]; exact hm)
  cases rnd <;> simpa only [_root_.slhdsa.shake_256f.block_shape, _root_.slhdsa.shake_256f.hP, _root_.slhdsa.shake_256f.shape, joined, _root_.slhdsa.randS,
    Option.isSome, Option.getD, Bool.false_eq_true, ↓reduceIte] using h
#print axioms shake_256f_sign_with_context
end slh_dsa
