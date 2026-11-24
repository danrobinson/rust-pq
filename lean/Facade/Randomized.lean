import Facade.Keygen

open Aeneas Aeneas.Std Result
open slhdsa (bytes Room)
namespace slh_dsa

/-- A successful draw supplies the FIPS 205 randomizer. A failed draw yields a
signature error, and both branches return the state reached by the RNG call. -/
def RandomizedSignCorrect {P Vk : Type} {Sk Sig : Usize}
    (C : params.Core P (Array U8 Sk) Vk (Array U8 Sig)) (p : Spec.Params) (slack : Nat) : Prop :=
  ∀ {R E : Type} (rng : rand_core.TryCryptoRng R E) (r0 r1 : R)
    (status : Std.core.result.Result Unit E) (written : Slice U8)
    (sk : signing_key.SigningKey P (Array U8 Sk) Vk (Array U8 Sig)) (m : Slice U8),
    Room m.length slack → written.length = p.n →
    (∀ buf : Slice U8, buf.val = List.replicate p.n 0#u8 →
      rng.TryRngInst.try_fill_bytes r0 buf = ok (status, r1, written)) →
    signing_key.SigningKey.Insts.SignatureSignerRandomizedSignerSignature.try_sign_with_rng
      C rng sk r0 m ⦃ result => result.2 = r1 ∧ signatureBytes result.1 =
        match status with
        | .Err _ => none
        | .Ok _ => Spec.slhSign p (bytes m.val) [] (bytes sk.bytes.val) (bytes written.val) ⦄

private theorem randomized_spec {P Vk : Type} {Sk Sig N : Usize}
    (C : params.Core P (Array U8 Sk) Vk (Array U8 Sig)) (p : Spec.Params) (slack : Nat)
    (cn : C.N = ok N) (hn : N.val = p.n) (hN : N.val ≤ 32)
    (signs : ∀ sk m (w : Slice U8), w.length = p.n → Room m.length slack →
      signing_key.SigningKey.try_sign_with_context C sk m (Array.to_slice (Std.Array.empty U8)) (some w)
        ⦃ ret => signatureBytes ret = Spec.slhSign p (bytes m.val) [] (bytes sk.bytes.val) (bytes w.val) ⦄) :
    RandomizedSignCorrect C p slack := by
  intro R E rng r0 r1 status written sk m hm hw draw
  unfold signing_key.SigningKey.Insts.SignatureSignerRandomizedSignerSignature.try_sign_with_rng
    signing_key.SigningKey.Insts.SignatureSignerRandomizedMultipartSignerSignature.try_multipart_sign_with_rng
    signing_key.SigningKey.raw_try_sign_with_rng
  simp only [lift, cn, bind_ok]
  let* ⟨s, back, es, _, _⟩ ← Array.index_mut_SliceIndexRangeToUsizeSlice
  have initial : (Array.repeat 32#usize 0#u8).val.slice 0 N = List.replicate p.n 0#u8 := by
    rw [← hn, Array.repeat_val]
    change ((List.replicate 32 0#u8).drop 0).take N.val = _
    rw [List.drop_zero, List.take_replicate, Nat.min_eq_left hN]
  unfold signing_key.SigningKey.sign_with_rng_buffer
  rw [draw s (es.trans initial)]
  simp only [bind_ok, uncurry]
  cases status with
  | Err err =>
    simp only [signature.error.Error.new, bind_ok, uncurry]
    step with wipe_bytes_spec
    simp [signatureBytes]
  | Ok u =>
    obtain ⟨sig, hs, hout⟩ := _root_.slhdsa.spec_imp_exists (signs sk m written hw hm)
    unfold signing_key.SigningKey.try_sign_with_context at hs
    simp only [lift, bind_ok] at hs
    rw [hs]
    simp only [bind_ok, uncurry]
    step with wipe_bytes_spec
    simpa using hout

theorem sha2_128s_randomized_sign : RandomizedSignCorrect
    params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.sha2_128s 409 := by
  apply randomized_spec (N := 16#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact sha2_128s_sign_with_context sk m _ (some w) (by simpa [Spec.sha2_128s] using hw) hm
  · simp [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.N, slhdsa.sets.sha2_128s.params.N, _root_.slhdsa.sets.sha2_128s.params.N]
#print axioms sha2_128s_randomized_sign

theorem sha2_128f_randomized_sign : RandomizedSignCorrect
    params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.sha2_128f 409 := by
  apply randomized_spec (N := 16#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact sha2_128f_sign_with_context sk m _ (some w) (by simpa [Spec.sha2_128f] using hw) hm
  · simp [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.N, slhdsa.sets.sha2_128f.params.N, _root_.slhdsa.sets.sha2_128f.params.N]
#print axioms sha2_128f_randomized_sign

theorem sha2_192s_randomized_sign : RandomizedSignCorrect
    params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.sha2_192s 561 := by
  apply randomized_spec (N := 24#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact sha2_192s_sign_with_context sk m _ (some w) (by simpa [Spec.sha2_192s] using hw) hm
  · simp [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.N, slhdsa.sets.sha2_192s.params.N, _root_.slhdsa.sets.sha2_192s.params.N]
#print axioms sha2_192s_randomized_sign

theorem sha2_192f_randomized_sign : RandomizedSignCorrect
    params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.sha2_192f 561 := by
  apply randomized_spec (N := 24#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact sha2_192f_sign_with_context sk m _ (some w) (by simpa [Spec.sha2_192f] using hw) hm
  · simp [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.N, slhdsa.sets.sha2_192f.params.N, _root_.slhdsa.sets.sha2_192f.params.N]
#print axioms sha2_192f_randomized_sign

theorem sha2_256s_randomized_sign : RandomizedSignCorrect
    params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.sha2_256s 561 := by
  apply randomized_spec (N := 32#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact sha2_256s_sign_with_context sk m _ (some w) (by simpa [Spec.sha2_256s] using hw) hm
  · simp [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.N, slhdsa.sets.sha2_256s.params.N, _root_.slhdsa.sets.sha2_256s.params.N]
#print axioms sha2_256s_randomized_sign

theorem sha2_256f_randomized_sign : RandomizedSignCorrect
    params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.sha2_256f 561 := by
  apply randomized_spec (N := 32#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact sha2_256f_sign_with_context sk m _ (some w) (by simpa [Spec.sha2_256f] using hw) hm
  · simp [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.N, slhdsa.sets.sha2_256f.params.N, _root_.slhdsa.sets.sha2_256f.params.N]
#print axioms sha2_256f_randomized_sign

theorem shake_128s_randomized_sign : RandomizedSignCorrect
    params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.shake_128s 409 := by
  apply randomized_spec (N := 16#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact shake_128s_sign_with_context sk m _ (some w) (by simpa [Spec.shake_128s, Spec.sha2_128s] using hw) hm
  · simp [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.N, slhdsa.sets.shake_128s.params.N, _root_.slhdsa.sets.shake_128s.params.N]
#print axioms shake_128s_randomized_sign

theorem shake_128f_randomized_sign : RandomizedSignCorrect
    params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.shake_128f 409 := by
  apply randomized_spec (N := 16#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact shake_128f_sign_with_context sk m _ (some w) (by simpa [Spec.shake_128f, Spec.sha2_128f] using hw) hm
  · simp [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.N, slhdsa.sets.shake_128f.params.N, _root_.slhdsa.sets.shake_128f.params.N]
#print axioms shake_128f_randomized_sign

theorem shake_192s_randomized_sign : RandomizedSignCorrect
    params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.shake_192s 561 := by
  apply randomized_spec (N := 24#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact shake_192s_sign_with_context sk m _ (some w) (by simpa [Spec.shake_192s, Spec.sha2_192s] using hw) hm
  · simp [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.N, slhdsa.sets.shake_192s.params.N, _root_.slhdsa.sets.shake_192s.params.N]
#print axioms shake_192s_randomized_sign

theorem shake_192f_randomized_sign : RandomizedSignCorrect
    params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.shake_192f 561 := by
  apply randomized_spec (N := 24#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact shake_192f_sign_with_context sk m _ (some w) (by simpa [Spec.shake_192f, Spec.sha2_192f] using hw) hm
  · simp [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.N, slhdsa.sets.shake_192f.params.N, _root_.slhdsa.sets.shake_192f.params.N]
#print axioms shake_192f_randomized_sign

theorem shake_256s_randomized_sign : RandomizedSignCorrect
    params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.shake_256s 561 := by
  apply randomized_spec (N := 32#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact shake_256s_sign_with_context sk m _ (some w) (by simpa [Spec.shake_256s, Spec.sha2_256s] using hw) hm
  · simp [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.N, slhdsa.sets.shake_256s.params.N, _root_.slhdsa.sets.shake_256s.params.N]
#print axioms shake_256s_randomized_sign

theorem shake_256f_randomized_sign : RandomizedSignCorrect
    params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.shake_256f 561 := by
  apply randomized_spec (N := 32#usize) _ _ _ _ (by decide) (by decide)
  · intro sk m w hw hm
    exact shake_256f_sign_with_context sk m _ (some w) (by simpa [Spec.shake_256f, Spec.sha2_256f] using hw) hm
  · simp [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.N, slhdsa.sets.shake_256f.params.N, _root_.slhdsa.sets.shake_256f.params.N]
#print axioms shake_256f_randomized_sign

end slh_dsa
