import Facade.Keygen
open Aeneas Aeneas.Std Result
open slhdsa (bytes paramsS PN)
namespace slh_dsa

def observed {α β ε : Type} (f : α → β) : Std.core.result.Result α ε → Option β
  | .Ok a => some (f a)
  | .Err _ => none

/-- Each public byte parser checks the exact length and returns the input bytes.
The private key parser also reconstructs the embedded public key. -/
def ParsersCorrect {P : Type} {Sk Vk Sig : Usize}
    (C : params.Core P (Array U8 Sk) (Array U8 Vk) (Array U8 Sig)) (p : Spec.Params) : Prop :=
  ∀ b : Slice U8,
    (signing_key.SigningKey.Insts.CoreConvertTryFromShared0SliceU8Error.try_from C b ⦃ r =>
      observed keyBytes r = if b.length = 4*p.n then some (bytes b.val, Spec.skPk p (bytes b.val)) else none ⦄) ∧
    (verifying_key.VerifyingKey.Insts.CoreConvertTryFromShared0SliceU8Error.try_from C b ⦃ r =>
      observed (fun k => bytes k.bytes.val) r = if b.length = 2*p.n then some (bytes b.val) else none ⦄) ∧
    (signature_encoding.Signature.Insts.CoreConvertTryFromShared0SliceU8Error.try_from C b ⦃ r =>
      signatureBytes r = if b.length = p.sigBytes then some (bytes b.val) else none ⦄)

private theorem parsers_spec {P : Type} {Sk Vk Sig N : Usize}
    (C : params.Core P (Array U8 Sk) (Array U8 Vk) (Array U8 Sig))
    (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (hsk : Sk.val = 4*N.val) (hvk : Vk.val = 2*N.val) (hsig : Sig.val = (paramsS p).sigBytes)
    (storeSk : C.SigningKeyStorageInst.BufferInst = ArrayU8N.Insts.Slh_dsaParamsBuffer Sk)
    (storeVk : C.VerifyingKeyStorageInst.BufferInst = ArrayU8N.Insts.Slh_dsaParamsBuffer Vk)
    (storeSig : C.SignatureStorageInst.BufferInst = ArrayU8N.Insts.Slh_dsaParamsBuffer Sig)
    (parseSk : C.sk_from = _root_.slhdsa.adapter.signing_key_from N)
    (parseVk : C.pk_from = _root_.slhdsa.encoding.public_key_from)
    (parseSig : C.sig_from = _root_.slhdsa.adapter.signature_from p) : ParsersCorrect C (paramsS p) := by
  intro b
  constructor
  · unfold signing_key.SigningKey.Insts.CoreConvertTryFromShared0SliceU8Error.try_from
    simp only [storeSk, storeVk, parseSk, ArrayU8N.Insts.Slh_dsaParamsBuffer.zeroed,
      ArrayU8N.Insts.Slh_dsaParamsBuffer.as_mut_slice, Array.to_slice_mut, bind_ok, uncurry]
    let* ⟨flag, sk, vk, h, success, _⟩ ← _root_.slhdsa.adapter_signing_key_from_spec p hp b (Array.repeat Sk 0#u8).to_slice (Array.repeat Vk 0#u8).to_slice
      (hsk := by simpa [Slice.length] using hsk) (hpk := by simpa [Slice.length] using hvk)
    rw [hp.n]
    cases flag with
    | false =>
      have bad : b.val.length ≠ 4*N.val := by simpa using h.symm
      simp [Slice.length, bad, signature.error.Error.new, observed]
    | true =>
      have good := h.mp rfl
      obtain ⟨hs, hv⟩ := success rfl
      have sklen : sk.val.length = Sk.val := by simpa [hs, hsk, Slice.length] using good
      have vklen := congrArg List.length hv
      simp only [Spec.skPk, List.length_drop, _root_.slhdsa.bytes_length, hp.n] at vklen
      change b.val.length = _ at good
      have vklen' : vk.val.length = Vk.val := by omega
      simp [observed, keyBytes, hp.n, Slice.length, good, Array.from_slice_val _ _ sklen,
        Array.from_slice_val _ _ vklen', hs, hv]
  constructor
  · unfold verifying_key.VerifyingKey.Insts.CoreConvertTryFromShared0SliceU8Error.try_from
    simp only [storeVk, parseVk, ArrayU8N.Insts.Slh_dsaParamsBuffer.zeroed,
      ArrayU8N.Insts.Slh_dsaParamsBuffer.as_mut_slice, Array.to_slice_mut, bind_ok, uncurry]
    let* ⟨flag, vk, h, success, _⟩ ← _root_.slhdsa.enc_public_key_from_spec
    simp [Slice.length, hvk] at h
    rw [hp.n]
    cases flag with
    | false =>
      have bad : b.val.length ≠ 2*N.val := by simpa using h.symm
      simp [Slice.length, hp.n, bad, signature.error.Error.new, observed]
    | true =>
      have good : b.val.length = 2*N.val := by simpa using h.symm
      have hv := success rfl
      have len : vk.val.length = Vk.val := by rw [hv, good, hvk]
      simp [observed, hp.n, Slice.length, good, Array.from_slice_val _ _ len, hv]
  · unfold signature_encoding.Signature.Insts.CoreConvertTryFromShared0SliceU8Error.try_from
    simp only [storeSig, parseSig, ArrayU8N.Insts.Slh_dsaParamsBuffer.zeroed,
      ArrayU8N.Insts.Slh_dsaParamsBuffer.as_mut_slice, Array.to_slice_mut, bind_ok, uncurry]
    let* ⟨flag, sig, h, success, _⟩ ← _root_.slhdsa.adapter_signature_from_spec p hp.1 b (Array.repeat Sig 0#u8).to_slice
      (hsig := by simpa [Slice.length] using hsig)
    cases flag with
    | false =>
      have bad : b.length ≠ (paramsS p).sigBytes := by simpa using h.symm
      simp [bad, signature.error.Error.new, signatureBytes]
    | true =>
      have good := h.mp rfl
      have hs := success rfl
      have len : sig.val.length = Sig.val := by simpa [hs, hsig, Slice.length] using good
      simp [good, signatureBytes, Array.from_slice_val _ _ len, hs]

theorem sha2_128s_parsers : ParsersCorrect
    params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.sha2_128s := by
  rw [← _root_.slhdsa.sha2_128s.hP]
  apply parsers_spec _ _ _root_.slhdsa.sha2_128s.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.sha2_128s.hP]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.sig_from, slhdsa.sets.sha2_128s.params.PARAMS])
  funext b sk pk
  simp only [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms sha2_128s_parsers

theorem sha2_128f_parsers : ParsersCorrect
    params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.sha2_128f := by
  rw [← _root_.slhdsa.sha2_128f.hP]
  apply parsers_spec _ _ _root_.slhdsa.sha2_128f.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.sha2_128f.hP]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.sig_from, slhdsa.sets.sha2_128f.params.PARAMS])
  funext b sk pk
  simp only [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms sha2_128f_parsers

theorem sha2_192s_parsers : ParsersCorrect
    params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.sha2_192s := by
  rw [← _root_.slhdsa.sha2_192s.hP]
  apply parsers_spec _ _ _root_.slhdsa.sha2_192s.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.sha2_192s.hP]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.sig_from, slhdsa.sets.sha2_192s.params.PARAMS])
  funext b sk pk
  simp only [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms sha2_192s_parsers

theorem sha2_192f_parsers : ParsersCorrect
    params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.sha2_192f := by
  rw [← _root_.slhdsa.sha2_192f.hP]
  apply parsers_spec _ _ _root_.slhdsa.sha2_192f.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.sha2_192f.hP]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.sig_from, slhdsa.sets.sha2_192f.params.PARAMS])
  funext b sk pk
  simp only [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms sha2_192f_parsers

theorem sha2_256s_parsers : ParsersCorrect
    params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.sha2_256s := by
  rw [← _root_.slhdsa.sha2_256s.hP]
  apply parsers_spec _ _ _root_.slhdsa.sha2_256s.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.sha2_256s.hP]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.sig_from, slhdsa.sets.sha2_256s.params.PARAMS])
  funext b sk pk
  simp only [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms sha2_256s_parsers

theorem sha2_256f_parsers : ParsersCorrect
    params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.sha2_256f := by
  rw [← _root_.slhdsa.sha2_256f.hP]
  apply parsers_spec _ _ _root_.slhdsa.sha2_256f.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.sha2_256f.hP]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.sig_from, slhdsa.sets.sha2_256f.params.PARAMS])
  funext b sk pk
  simp only [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms sha2_256f_parsers

theorem shake_128s_parsers : ParsersCorrect
    params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.shake_128s := by
  change ParsersCorrect _ Spec.sha2_128s
  rw [← _root_.slhdsa.shake_128s.shape]
  apply parsers_spec _ _ _root_.slhdsa.shake_128s.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.shake_128s.shape]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.sig_from, slhdsa.sets.shake_128s.params.PARAMS])
  funext b sk pk
  simp only [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms shake_128s_parsers

theorem shake_128f_parsers : ParsersCorrect
    params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.shake_128f := by
  change ParsersCorrect _ Spec.sha2_128f
  rw [← _root_.slhdsa.shake_128f.shape]
  apply parsers_spec _ _ _root_.slhdsa.shake_128f.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.shake_128f.shape]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.sig_from, slhdsa.sets.shake_128f.params.PARAMS])
  funext b sk pk
  simp only [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms shake_128f_parsers

theorem shake_192s_parsers : ParsersCorrect
    params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.shake_192s := by
  change ParsersCorrect _ Spec.sha2_192s
  rw [← _root_.slhdsa.shake_192s.shape]
  apply parsers_spec _ _ _root_.slhdsa.shake_192s.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.shake_192s.shape]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.sig_from, slhdsa.sets.shake_192s.params.PARAMS])
  funext b sk pk
  simp only [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms shake_192s_parsers

theorem shake_192f_parsers : ParsersCorrect
    params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.shake_192f := by
  change ParsersCorrect _ Spec.sha2_192f
  rw [← _root_.slhdsa.shake_192f.shape]
  apply parsers_spec _ _ _root_.slhdsa.shake_192f.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.shake_192f.shape]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.sig_from, slhdsa.sets.shake_192f.params.PARAMS])
  funext b sk pk
  simp only [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms shake_192f_parsers

theorem shake_256s_parsers : ParsersCorrect
    params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.shake_256s := by
  change ParsersCorrect _ Spec.sha2_256s
  rw [← _root_.slhdsa.shake_256s.shape]
  apply parsers_spec _ _ _root_.slhdsa.shake_256s.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.shake_256s.shape]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.sig_from, slhdsa.sets.shake_256s.params.PARAMS])
  funext b sk pk
  simp only [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms shake_256s_parsers

theorem shake_256f_parsers : ParsersCorrect
    params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.shake_256f := by
  change ParsersCorrect _ Spec.sha2_256f
  rw [← _root_.slhdsa.shake_256f.shape]
  apply parsers_spec _ _ _root_.slhdsa.shake_256f.pn (by decide) (by decide)
    (by rw [_root_.slhdsa.shake_256f.shape]; decide) rfl rfl rfl _ rfl (by funext b s; simp [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.sig_from, slhdsa.sets.shake_256f.params.PARAMS])
  funext b sk pk
  simp only [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.sk_from, scrub_returns, bind_ok]
  exact Std.bind_pure _
#print axioms shake_256f_parsers

end slh_dsa
