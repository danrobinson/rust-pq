import Facade.Suite
import Facade.Multipart
import Slhdsa.Proofs.Sets
open Aeneas Aeneas.Std Result
open slhdsa (bytes paramsS PN Room msgSlack)

namespace slh_dsa

private theorem raw_verify_spec (family : Spec.HashFamily) {P Sk : Type} {Vk Sig N : Usize}
    (C : params.Core P Sk (Array U8 Vk) (Array U8 Sig))
    (p : _root_.slhdsa.params.Params) (hp : PN p N) (hvk : Vk.val = 2 * N.val)
    (getSig : C.SignatureStorageInst.BufferInst.as_slice = fun a => ok (Array.to_slice a))
    (getKey : C.VerifyingKeyStorageInst.BufferInst.as_slice = fun a => ok (Array.to_slice a))
    (dispatch : C.verify = _root_.slhdsa.Suite.verify family N p)
    (vk : verifying_key.VerifyingKey P Sk (Array U8 Vk) (Array U8 Sig))
    (parts : Slice (Slice U8)) (ctx : Slice U8)
    (sig : signature_encoding.Signature P Sk (Array U8 Vk) (Array U8 Sig))
    (hm : Room (parts.val.flatMap (fun part => part.val)).length (msgSlack N.val + 257)) :
    verifying_key.VerifyingKey.raw_try_verify_with_context C vk parts ctx sig ⦃ r =>
      r = if Spec.slhVerify (_root_.slhdsa.Suite.view family p) (bytes (parts.val.flatMap (fun part => part.val)))
            (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.raw_try_verify_with_context
  have fits : (parts.val.flatMap (fun part => part.val)).length ≤ Usize.max := by
    unfold Room at hm; omega
  obtain ⟨m, hjoin, hm'⟩ := _root_.slhdsa.spec_imp_exists (multipart.join_spec parts fits)
  rw [hjoin]
  simp only [bind_ok]
  rw [getSig, getKey]
  simp only [bind_ok]
  rw [dispatch]
  obtain ⟨b, hverify, hb⟩ := _root_.slhdsa.spec_imp_exists (_root_.slhdsa.Suite.api_verify_spec family p hp (alloc.vec.Vec.deref m) (Array.to_slice sig.bytes) ctx (Array.to_slice vk.bytes)
    (by simpa [Slice.length] using hvk)
    (by simpa only [Slice.length, _root_.slhdsa.vec_deref_val, hm'] using hm))
  rw [hverify]
  simp only [_root_.slhdsa.vec_deref_val, Array.val_to_slice, hm'] at hb
  rw [← hb]
  cases b <;> simp [core.bool.Bool.then_some, signature.error.Error.new, Std.core.option.Option.ok_or]

-- Per-set specializations of the RustCrypto Verifier implementation.

theorem sha2_128s_verify (vk : verifying_key.VerifyingKey params.Sha2_128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Sha2_128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize))
    (hm : Room m.length 409) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_128s (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .sha2 params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 _ _root_.slhdsa.sha2_128s.pn (by decide) rfl rfl (by funext a b c d; simp [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.verify, slhdsa.sets.sha2_128s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_128s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_128s.hP, joined, empty] using h
#print axioms sha2_128s_verify

theorem sha2_128f_verify (vk : verifying_key.VerifyingKey params.Sha2_128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Sha2_128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize))
    (hm : Room m.length 409) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_128f (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .sha2 params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 _ _root_.slhdsa.sha2_128f.pn (by decide) rfl rfl (by funext a b c d; simp [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.verify, slhdsa.sets.sha2_128f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_128f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_128f.hP, joined, empty] using h
#print axioms sha2_128f_verify

theorem sha2_192s_verify (vk : verifying_key.VerifyingKey params.Sha2_192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Sha2_192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize))
    (hm : Room m.length 561) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_192s (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .sha2 params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 _ _root_.slhdsa.sha2_192s.pn (by decide) rfl rfl (by funext a b c d; simp [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.verify, slhdsa.sets.sha2_192s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_192s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_192s.hP, joined, empty] using h
#print axioms sha2_192s_verify

theorem sha2_192f_verify (vk : verifying_key.VerifyingKey params.Sha2_192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Sha2_192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize))
    (hm : Room m.length 561) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_192f (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .sha2 params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 _ _root_.slhdsa.sha2_192f.pn (by decide) rfl rfl (by funext a b c d; simp [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.verify, slhdsa.sets.sha2_192f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_192f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_192f.hP, joined, empty] using h
#print axioms sha2_192f_verify

theorem sha2_256s_verify (vk : verifying_key.VerifyingKey params.Sha2_256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Sha2_256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize))
    (hm : Room m.length 561) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_256s (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .sha2 params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 _ _root_.slhdsa.sha2_256s.pn (by decide) rfl rfl (by funext a b c d; simp [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.verify, slhdsa.sets.sha2_256s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_256s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_256s.hP, joined, empty] using h
#print axioms sha2_256s_verify

theorem sha2_256f_verify (vk : verifying_key.VerifyingKey params.Sha2_256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Sha2_256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize))
    (hm : Room m.length 561) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_256f (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .sha2 params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 _ _root_.slhdsa.sha2_256f.pn (by decide) rfl rfl (by funext a b c d; simp [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.verify, slhdsa.sets.sha2_256f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_256f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_256f.hP, joined, empty] using h
#print axioms sha2_256f_verify
-- Public context-string APIs.

theorem sha2_128s_verify_with_context (vk : verifying_key.VerifyingKey params.Sha2_128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Sha2_128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize)) (hm : Room m.length 409) :
    verifying_key.VerifyingKey.try_verify_with_context params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_128s (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .sha2 params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 _ _root_.slhdsa.sha2_128s.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.verify, slhdsa.sets.sha2_128s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_128s.slack]; exact hm)
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_128s.hP, joined] using h
#print axioms sha2_128s_verify_with_context

theorem sha2_128f_verify_with_context (vk : verifying_key.VerifyingKey params.Sha2_128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Sha2_128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize)) (hm : Room m.length 409) :
    verifying_key.VerifyingKey.try_verify_with_context params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_128f (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .sha2 params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 _ _root_.slhdsa.sha2_128f.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.verify, slhdsa.sets.sha2_128f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_128f.slack]; exact hm)
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_128f.hP, joined] using h
#print axioms sha2_128f_verify_with_context

theorem sha2_192s_verify_with_context (vk : verifying_key.VerifyingKey params.Sha2_192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Sha2_192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize)) (hm : Room m.length 561) :
    verifying_key.VerifyingKey.try_verify_with_context params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_192s (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .sha2 params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 _ _root_.slhdsa.sha2_192s.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.verify, slhdsa.sets.sha2_192s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_192s.slack]; exact hm)
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_192s.hP, joined] using h
#print axioms sha2_192s_verify_with_context

theorem sha2_192f_verify_with_context (vk : verifying_key.VerifyingKey params.Sha2_192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Sha2_192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize)) (hm : Room m.length 561) :
    verifying_key.VerifyingKey.try_verify_with_context params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_192f (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .sha2 params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 _ _root_.slhdsa.sha2_192f.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.verify, slhdsa.sets.sha2_192f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_192f.slack]; exact hm)
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_192f.hP, joined] using h
#print axioms sha2_192f_verify_with_context

theorem sha2_256s_verify_with_context (vk : verifying_key.VerifyingKey params.Sha2_256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Sha2_256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize)) (hm : Room m.length 561) :
    verifying_key.VerifyingKey.try_verify_with_context params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_256s (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .sha2 params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 _ _root_.slhdsa.sha2_256s.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.verify, slhdsa.sets.sha2_256s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_256s.slack]; exact hm)
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_256s.hP, joined] using h
#print axioms sha2_256s_verify_with_context

theorem sha2_256f_verify_with_context (vk : verifying_key.VerifyingKey params.Sha2_256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Sha2_256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize)) (hm : Room m.length 561) :
    verifying_key.VerifyingKey.try_verify_with_context params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.sha2_256f (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .sha2 params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 _ _root_.slhdsa.sha2_256f.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.verify, slhdsa.sets.sha2_256f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.sha2_256f.slack]; exact hm)
  simpa only [_root_.slhdsa.Suite.view_sha2, _root_.slhdsa.sha2_256f.hP, joined] using h
#print axioms sha2_256f_verify_with_context
theorem shake_128s_verify (vk : verifying_key.VerifyingKey params.Shake128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Shake128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize))
    (hm : Room m.length 409) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_128s (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .shake params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 _ _root_.slhdsa.shake_128s.pn (by decide) rfl rfl (by funext a b c d; simp [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.verify, slhdsa.sets.shake_128s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_128s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_128s.block_shape, _root_.slhdsa.shake_128s.hP, _root_.slhdsa.shake_128s.shape, joined, empty] using h
#print axioms shake_128s_verify

theorem shake_128f_verify (vk : verifying_key.VerifyingKey params.Shake128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Shake128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize))
    (hm : Room m.length 409) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_128f (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .shake params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 _ _root_.slhdsa.shake_128f.pn (by decide) rfl rfl (by funext a b c d; simp [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.verify, slhdsa.sets.shake_128f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_128f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_128f.block_shape, _root_.slhdsa.shake_128f.hP, _root_.slhdsa.shake_128f.shape, joined, empty] using h
#print axioms shake_128f_verify

theorem shake_192s_verify (vk : verifying_key.VerifyingKey params.Shake192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Shake192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize))
    (hm : Room m.length 561) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_192s (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .shake params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 _ _root_.slhdsa.shake_192s.pn (by decide) rfl rfl (by funext a b c d; simp [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.verify, slhdsa.sets.shake_192s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_192s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_192s.block_shape, _root_.slhdsa.shake_192s.hP, _root_.slhdsa.shake_192s.shape, joined, empty] using h
#print axioms shake_192s_verify

theorem shake_192f_verify (vk : verifying_key.VerifyingKey params.Shake192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Shake192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize))
    (hm : Room m.length 561) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_192f (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .shake params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 _ _root_.slhdsa.shake_192f.pn (by decide) rfl rfl (by funext a b c d; simp [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.verify, slhdsa.sets.shake_192f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_192f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_192f.block_shape, _root_.slhdsa.shake_192f.hP, _root_.slhdsa.shake_192f.shape, joined, empty] using h
#print axioms shake_192f_verify

theorem shake_256s_verify (vk : verifying_key.VerifyingKey params.Shake256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Shake256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize))
    (hm : Room m.length 561) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_256s (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .shake params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 _ _root_.slhdsa.shake_256s.pn (by decide) rfl rfl (by funext a b c d; simp [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.verify, slhdsa.sets.shake_256s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_256s.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_256s.block_shape, _root_.slhdsa.shake_256s.hP, _root_.slhdsa.shake_256s.shape, joined, empty] using h
#print axioms shake_256s_verify

theorem shake_256f_verify (vk : verifying_key.VerifyingKey params.Shake256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize))
    (m : Slice U8) (sig : signature_encoding.Signature params.Shake256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize))
    (hm : Room m.length 561) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
      params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 vk m sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_256f (bytes m.val) (bytes sig.bytes.val) [] (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify
  let parts := Array.to_slice (Array.make 1#usize [m])
  let ctx := Array.to_slice (Std.Array.empty U8)
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have empty : bytes ctx.val = [] := by simp [ctx, Std.Array.empty, bytes]
  have h := raw_verify_spec .shake params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 _ _root_.slhdsa.shake_256f.pn (by decide) rfl rfl (by funext a b c d; simp [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.verify, slhdsa.sets.shake_256f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_256f.slack]; exact hm)
  simp only [lift, bind_ok]
  simpa only [_root_.slhdsa.shake_256f.block_shape, _root_.slhdsa.shake_256f.hP, _root_.slhdsa.shake_256f.shape, joined, empty] using h
#print axioms shake_256f_verify
-- Public context-string APIs.

theorem shake_128s_verify_with_context (vk : verifying_key.VerifyingKey params.Shake128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Shake128s (Array U8 64#usize) (Array U8 32#usize) (Array U8 7856#usize)) (hm : Room m.length 409) :
    verifying_key.VerifyingKey.try_verify_with_context params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_128s (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .shake params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 _ _root_.slhdsa.shake_128s.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.verify, slhdsa.sets.shake_128s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_128s.slack]; exact hm)
  simpa only [_root_.slhdsa.shake_128s.block_shape, _root_.slhdsa.shake_128s.hP, _root_.slhdsa.shake_128s.shape, joined] using h
#print axioms shake_128s_verify_with_context

theorem shake_128f_verify_with_context (vk : verifying_key.VerifyingKey params.Shake128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Shake128f (Array U8 64#usize) (Array U8 32#usize) (Array U8 17088#usize)) (hm : Room m.length 409) :
    verifying_key.VerifyingKey.try_verify_with_context params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_128f (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .shake params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 _ _root_.slhdsa.shake_128f.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.verify, slhdsa.sets.shake_128f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_128f.slack]; exact hm)
  simpa only [_root_.slhdsa.shake_128f.block_shape, _root_.slhdsa.shake_128f.hP, _root_.slhdsa.shake_128f.shape, joined] using h
#print axioms shake_128f_verify_with_context

theorem shake_192s_verify_with_context (vk : verifying_key.VerifyingKey params.Shake192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Shake192s (Array U8 96#usize) (Array U8 48#usize) (Array U8 16224#usize)) (hm : Room m.length 561) :
    verifying_key.VerifyingKey.try_verify_with_context params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_192s (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .shake params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 _ _root_.slhdsa.shake_192s.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.verify, slhdsa.sets.shake_192s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_192s.slack]; exact hm)
  simpa only [_root_.slhdsa.shake_192s.block_shape, _root_.slhdsa.shake_192s.hP, _root_.slhdsa.shake_192s.shape, joined] using h
#print axioms shake_192s_verify_with_context

theorem shake_192f_verify_with_context (vk : verifying_key.VerifyingKey params.Shake192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Shake192f (Array U8 96#usize) (Array U8 48#usize) (Array U8 35664#usize)) (hm : Room m.length 561) :
    verifying_key.VerifyingKey.try_verify_with_context params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_192f (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .shake params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 _ _root_.slhdsa.shake_192f.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.verify, slhdsa.sets.shake_192f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_192f.slack]; exact hm)
  simpa only [_root_.slhdsa.shake_192f.block_shape, _root_.slhdsa.shake_192f.hP, _root_.slhdsa.shake_192f.shape, joined] using h
#print axioms shake_192f_verify_with_context

theorem shake_256s_verify_with_context (vk : verifying_key.VerifyingKey params.Shake256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Shake256s (Array U8 128#usize) (Array U8 64#usize) (Array U8 29792#usize)) (hm : Room m.length 561) :
    verifying_key.VerifyingKey.try_verify_with_context params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_256s (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .shake params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 _ _root_.slhdsa.shake_256s.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.verify, slhdsa.sets.shake_256s.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_256s.slack]; exact hm)
  simpa only [_root_.slhdsa.shake_256s.block_shape, _root_.slhdsa.shake_256s.hP, _root_.slhdsa.shake_256s.shape, joined] using h
#print axioms shake_256s_verify_with_context

theorem shake_256f_verify_with_context (vk : verifying_key.VerifyingKey params.Shake256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize))
    (m ctx : Slice U8) (sig : signature_encoding.Signature params.Shake256f (Array U8 128#usize) (Array U8 64#usize) (Array U8 49856#usize)) (hm : Room m.length 561) :
    verifying_key.VerifyingKey.try_verify_with_context params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 vk m ctx sig ⦃ r =>
      r = if Spec.slhVerify Spec.shake_256f (bytes m.val) (bytes sig.bytes.val) (bytes ctx.val) (bytes vk.bytes.val)
          then .Ok () else .Err () ⦄ := by
  unfold verifying_key.VerifyingKey.try_verify_with_context
  simp only [lift, bind_ok]
  let parts := Array.to_slice (Array.make 1#usize [m])
  have joined : parts.val.flatMap (fun part => part.val) = m.val := by simp [parts, Array.make]
  have h := raw_verify_spec .shake params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 _ _root_.slhdsa.shake_256f.pn (by decide) rfl rfl
    (by funext a b c d; simp [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.verify, slhdsa.sets.shake_256f.params.PARAMS])
    vk parts ctx sig (by rw [joined, _root_.slhdsa.shake_256f.slack]; exact hm)
  simpa only [_root_.slhdsa.shake_256f.block_shape, _root_.slhdsa.shake_256f.hP, _root_.slhdsa.shake_256f.shape, joined] using h
#print axioms shake_256f_verify_with_context
end slh_dsa
