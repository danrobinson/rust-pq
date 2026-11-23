import Facade.Suite
import Facade.Sign
open Aeneas Aeneas.Std Result
open slhdsa (bytes paramsS PN)

namespace slh_dsa

/-- Private and public key bytes visible after key generation. -/
def keyBytes {P Sig : Type} {Sk Vk : Usize}
    (k : signing_key.SigningKey P (Array U8 Sk) (Array U8 Vk) Sig) :=
  (bytes k.bytes.val, bytes k.verifying_key.bytes.val)

theorem seeded_spec (family : Spec.HashFamily) {P Sig : Type} {Sk Vk N : Usize}
    (C : params.Core P (Array U8 Sk) (Array U8 Vk) Sig)
    (p : _root_.slhdsa.params.Params) (hp : PN p N) (hsk : Sk.val = 4 * N.val) (hvk : Vk.val = 2 * N.val)
    (storeSk : C.SigningKeyStorageInst.BufferInst = ArrayU8N.Insts.Slh_dsaParamsBuffer Sk)
    (storeVk : C.VerifyingKeyStorageInst.BufferInst = ArrayU8N.Insts.Slh_dsaParamsBuffer Vk)
    (dispatch : C.keygen_seeds = _root_.slhdsa.Suite.keygen_seeds family N p)
    (a b c : Slice U8) (ha : a.length = N.val) (hb : b.length = N.val) (hc : c.length = N.val) :
    signing_key.SigningKey.slh_keygen_internal C a b c ⦃ key =>
      keyBytes key = Spec.slhKeygenInternal (_root_.slhdsa.Suite.view family p) (bytes a.val) (bytes b.val) (bytes c.val) ⦄ := by
  unfold signing_key.SigningKey.slh_keygen_internal
  rw [storeSk, storeVk, dispatch]
  simp only [ArrayU8N.Insts.Slh_dsaParamsBuffer.zeroed,
    ArrayU8N.Insts.Slh_dsaParamsBuffer.as_mut_slice, Array.to_slice_mut, bind_ok, uncurry]
  obtain ⟨⟨sk, vk⟩, hgen, hbytes⟩ := _root_.slhdsa.spec_imp_exists
    (_root_.slhdsa.Suite.adapter_keygen_seeds_spec family p hp a b c (Array.repeat Sk 0#u8).to_slice
      (Array.repeat Vk 0#u8).to_slice ha hb hc
      (by simpa [Slice.length] using hsk) (by simpa [Slice.length] using hvk))
  rw [hgen]
  have lengths := congrArg (fun (x : Spec.Bytes × Spec.Bytes) => (x.1.length, x.2.length)) hbytes
  simp only [Spec.slhKeygenInternal, List.length_append, Spec.xmssNode_length _ (_root_.slhdsa.Suite.valid family hp),
    _root_.slhdsa.bytes_length, Prod.mk.injEq] at lengths
  change a.val.length = N.val at ha
  change b.val.length = N.val at hb
  change c.val.length = N.val at hc
  have hn : (_root_.slhdsa.Suite.view family p).n = N.val := hp.n
  have h1 : sk.val.length = Sk.val := by omega
  have h2 : vk.val.length = Vk.val := by omega
  simpa only [bind_ok, uncurry, WP.spec_ok, keyBytes, Array.from_slice_val _ _ h1, Array.from_slice_val _ _ h2] using hbytes

@[local step] theorem wipe_bytes_spec {n : Usize} (a : Array U8 n) :
    Array.Insts.ZeroizeZeroize.zeroize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a
      ⦃ _ => True ⦄ := by
  unfold Array.Insts.ZeroizeZeroize.zeroize
  apply WP.spec_bind (List.mapM_with_length_spec (post := fun _ (_ : U8) => True)
    (l := a.val) (f := (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes).zeroize)
    (by intro i hi; change ok 0#u8 ⦃ _ => True ⦄; simp))
  simp

/-- The RNG is a parameter of the theorem. Each draw returns the next state and
the bytes it supplied. Only the three n-byte calls in Algorithm 21 are needed. -/
private theorem new_spec (family : Spec.HashFamily) {P R E Sig : Type} {Sk Vk N : Usize}
    (C : params.Core P (Array U8 Sk) (Array U8 Vk) Sig) (p : _root_.slhdsa.params.Params)
    (hp : PN p N) (cn : C.N = ok N)
    (seeded : ∀ a b c : Slice U8, a.length = N.val → b.length = N.val → c.length = N.val →
      signing_key.SigningKey.slh_keygen_internal C a b c ⦃ key =>
        keyBytes key = Spec.slhKeygenInternal (_root_.slhdsa.Suite.view family p) (bytes a.val) (bytes b.val) (bytes c.val) ⦄)
    (rng : rand_core.CryptoRng R E) (r0 r1 r2 r3 : R) (a b c : Slice U8)
    (ha : a.length = N.val) (hb : b.length = N.val) (hc : c.length = N.val)
    (draw1 : ∀ buf : Slice U8, buf.val = List.replicate N.val 0#u8 → rng.RngInst.fill_bytes r0 buf = ok (r1, a))
    (draw2 : ∀ buf : Slice U8, buf.val = List.replicate N.val 0#u8 → rng.RngInst.fill_bytes r1 buf = ok (r2, b))
    (draw3 : ∀ buf : Slice U8, buf.val = List.replicate N.val 0#u8 → rng.RngInst.fill_bytes r2 buf = ok (r3, c)) :
    signing_key.SigningKey.new C rng r0 ⦃ result =>
      keyBytes result.1 = Spec.slhKeygenInternal (_root_.slhdsa.Suite.view family p) (bytes a.val) (bytes b.val) (bytes c.val) ∧ result.2 = r3 ⦄ := by
  unfold signing_key.SigningKey.new
  rw [cn]
  simp only [bind_ok]
  have hN := hp.le32
  let* ⟨s1, back1, e1, _, _⟩ ← Array.index_mut_SliceIndexRangeToUsizeSlice
  let* ⟨s2, back2, e2, _, _⟩ ← Array.index_mut_SliceIndexRangeToUsizeSlice
  let* ⟨s3, back3, e3, _, _⟩ ← Array.index_mut_SliceIndexRangeToUsizeSlice
  unfold signing_key.SigningKey.key_from_rng_parts
  have initial : (Array.repeat 32#usize 0#u8).val.slice 0 N = List.replicate N.val 0#u8 := by
    rw [Array.repeat_val]
    change ((List.replicate 32 0#u8).drop 0).take N.val = _
    rw [List.drop_zero, List.take_replicate, Nat.min_eq_left hN]
  rw [draw1 s1 (e1.trans initial)]
  simp only [bind_ok, uncurry]
  rw [draw2 s2 (e2.trans initial)]
  simp only [bind_ok, uncurry]
  rw [draw3 s3 (e3.trans initial)]
  simp only [bind_ok, uncurry]
  obtain ⟨key, hkey, out⟩ := _root_.slhdsa.spec_imp_exists (seeded a b c ha hb hc)
  rw [hkey]
  simp only [bind_ok, uncurry]
  step*

/-- The public constructor refines FIPS 205 seeded key generation under the
observed RNG draws. The RNG implementation supplies both bytes and next state. -/
def KeygenCorrect {P Sig : Type} {Sk Vk : Usize}
    (C : params.Core P (Array U8 Sk) (Array U8 Vk) Sig) (p : Spec.Params) : Prop :=
  ∀ {R E : Type} (rng : rand_core.CryptoRng R E) (r0 r1 r2 r3 : R) (a b c : Slice U8),
    a.length = p.n → b.length = p.n → c.length = p.n →
    (∀ buf : Slice U8, buf.val = List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r0 buf = ok (r1, a)) →
    (∀ buf : Slice U8, buf.val = List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r1 buf = ok (r2, b)) →
    (∀ buf : Slice U8, buf.val = List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r2 buf = ok (r3, c)) →
    signing_key.SigningKey.new C rng r0 ⦃ result =>
      keyBytes result.1 = Spec.slhKeygenInternal p (bytes a.val) (bytes b.val) (bytes c.val) ∧ result.2 = r3 ⦄

theorem sha2_128s_new : KeygenCorrect
    params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.sha2_128s := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.sha2_128s.hP]
  apply new_spec .sha2 _ _ _root_.slhdsa.sha2_128s.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.N, slhdsa.sets.sha2_128s.params.N, _root_.slhdsa.sets.sha2_128s.params.N]
  · apply seeded_spec .sha2 _ _ _root_.slhdsa.sha2_128s.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.keygen_seeds, slhdsa.sets.sha2_128s.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms sha2_128s_new

theorem sha2_128f_new : KeygenCorrect
    params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.sha2_128f := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.sha2_128f.hP]
  apply new_spec .sha2 _ _ _root_.slhdsa.sha2_128f.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.N, slhdsa.sets.sha2_128f.params.N, _root_.slhdsa.sets.sha2_128f.params.N]
  · apply seeded_spec .sha2 _ _ _root_.slhdsa.sha2_128f.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.keygen_seeds, slhdsa.sets.sha2_128f.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms sha2_128f_new

theorem sha2_192s_new : KeygenCorrect
    params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.sha2_192s := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.sha2_192s.hP]
  apply new_spec .sha2 _ _ _root_.slhdsa.sha2_192s.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.N, slhdsa.sets.sha2_192s.params.N, _root_.slhdsa.sets.sha2_192s.params.N]
  · apply seeded_spec .sha2 _ _ _root_.slhdsa.sha2_192s.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.keygen_seeds, slhdsa.sets.sha2_192s.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms sha2_192s_new

theorem sha2_192f_new : KeygenCorrect
    params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.sha2_192f := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.sha2_192f.hP]
  apply new_spec .sha2 _ _ _root_.slhdsa.sha2_192f.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.N, slhdsa.sets.sha2_192f.params.N, _root_.slhdsa.sets.sha2_192f.params.N]
  · apply seeded_spec .sha2 _ _ _root_.slhdsa.sha2_192f.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.keygen_seeds, slhdsa.sets.sha2_192f.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms sha2_192f_new

theorem sha2_256s_new : KeygenCorrect
    params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.sha2_256s := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.sha2_256s.hP]
  apply new_spec .sha2 _ _ _root_.slhdsa.sha2_256s.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.N, slhdsa.sets.sha2_256s.params.N, _root_.slhdsa.sets.sha2_256s.params.N]
  · apply seeded_spec .sha2 _ _ _root_.slhdsa.sha2_256s.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.keygen_seeds, slhdsa.sets.sha2_256s.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms sha2_256s_new

theorem sha2_256f_new : KeygenCorrect
    params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.sha2_256f := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.sha2_256f.hP]
  apply new_spec .sha2 _ _ _root_.slhdsa.sha2_256f.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.N, slhdsa.sets.sha2_256f.params.N, _root_.slhdsa.sets.sha2_256f.params.N]
  · apply seeded_spec .sha2 _ _ _root_.slhdsa.sha2_256f.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.keygen_seeds, slhdsa.sets.sha2_256f.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms sha2_256f_new

theorem shake_128s_new : KeygenCorrect
    params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.shake_128s := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.shake_128s.hP]
  apply new_spec .shake _ _ _root_.slhdsa.shake_128s.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.N, slhdsa.sets.shake_128s.params.N, _root_.slhdsa.sets.shake_128s.params.N]
  · apply seeded_spec .shake _ _ _root_.slhdsa.shake_128s.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856.keygen_seeds, slhdsa.sets.shake_128s.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms shake_128s_new

theorem shake_128f_new : KeygenCorrect
    params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.shake_128f := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.shake_128f.hP]
  apply new_spec .shake _ _ _root_.slhdsa.shake_128f.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.N, slhdsa.sets.shake_128f.params.N, _root_.slhdsa.sets.shake_128f.params.N]
  · apply seeded_spec .shake _ _ _root_.slhdsa.shake_128f.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088.keygen_seeds, slhdsa.sets.shake_128f.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms shake_128f_new

theorem shake_192s_new : KeygenCorrect
    params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.shake_192s := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.shake_192s.hP]
  apply new_spec .shake _ _ _root_.slhdsa.shake_192s.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.N, slhdsa.sets.shake_192s.params.N, _root_.slhdsa.sets.shake_192s.params.N]
  · apply seeded_spec .shake _ _ _root_.slhdsa.shake_192s.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224.keygen_seeds, slhdsa.sets.shake_192s.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms shake_192s_new

theorem shake_192f_new : KeygenCorrect
    params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.shake_192f := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.shake_192f.hP]
  apply new_spec .shake _ _ _root_.slhdsa.shake_192f.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.N, slhdsa.sets.shake_192f.params.N, _root_.slhdsa.sets.shake_192f.params.N]
  · apply seeded_spec .shake _ _ _root_.slhdsa.shake_192f.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664.keygen_seeds, slhdsa.sets.shake_192f.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms shake_192f_new

theorem shake_256s_new : KeygenCorrect
    params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.shake_256s := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.shake_256s.hP]
  apply new_spec .shake _ _ _root_.slhdsa.shake_256s.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.N, slhdsa.sets.shake_256s.params.N, _root_.slhdsa.sets.shake_256s.params.N]
  · apply seeded_spec .shake _ _ _root_.slhdsa.shake_256s.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792.keygen_seeds, slhdsa.sets.shake_256s.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms shake_256s_new

theorem shake_256f_new : KeygenCorrect
    params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.shake_256f := by
  intro R E rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  rw [← _root_.slhdsa.shake_256f.hP]
  apply new_spec .shake _ _ _root_.slhdsa.shake_256f.pn _ _ rng r0 r1 r2 r3 a b c ha hb hc d1 d2 d3
  · simp [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.N, slhdsa.sets.shake_256f.params.N, _root_.slhdsa.sets.shake_256f.params.N]
  · apply seeded_spec .shake _ _ _root_.slhdsa.shake_256f.pn (by decide) (by decide) rfl rfl
    funext a b c sk pk
    simp only [params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856.keygen_seeds, slhdsa.sets.shake_256f.params.PARAMS, bind_ok, scrub_returns]
    exact Std.bind_pure _
#print axioms shake_256f_new

end slh_dsa
