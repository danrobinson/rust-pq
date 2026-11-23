import PeerEquality.CallerApi
import Facade.Keygen
import Facade.Sign
import Facade.Verify

open Aeneas Aeneas.Std Result
namespace slhdsa.PeerCall
open Spec slh_dsa
set_option maxRecDepth 8192
attribute [local irreducible] slhSign slhVerify slhKeygenInternal

abbrev Core {P : Type} (sk vk sig : Usize) :=
  slh_dsa.params.Core P (Array U8 sk) (Array U8 vk) (Array U8 sig)

section
variable {P : Type} {sk vk sig : Usize} (C : @Core P sk vk sig) (p : Spec.Params) (slack : Nat)
include C

/-- Equality of secret and public key bytes, serialized signatures and public
verification results for matching input bytes and random draws. -/
structure Facades : Prop where
  keys : ∀ (c : Children) (_ : c.xmss.node = xmssNode p)
    {R E : Type} (rng : rand_core.CryptoRng R E) (r0 r1 r2 r3 : R) (a b d : Slice U8),
    a.length=p.n → b.length=p.n → d.length=p.n →
    (∀ buf : Slice U8, buf.val=List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r0 buf=ok (r1,a)) →
    (∀ buf : Slice U8, buf.val=List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r1 buf=ok (r2,b)) →
    (∀ buf : Slice U8, buf.val=List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r2 buf=ok (r3,d)) →
    signing_key.SigningKey.new C rng r0 ⦃ result =>
      let peer := keygen c p (bytes a.val) (bytes b.val) (bytes d.val)
      keyBytes result.1=(peer.bytes,peer.public.bytes) ∧ result.2=r3 ⦄
  sign : ∀ (c : Children) (_ : ChildLaws c p) (k : Key) (_ : k.Shape p)
    (ours : signing_key.SigningKey P (Array U8 sk) (Array U8 vk) (Array U8 sig)),
    bytes ours.bytes.val=k.bytes → ∀ (m ctx : Slice U8) (rnd : Option (Slice U8)),
    (∀ r ∈ rnd, r.length=p.n) → Room m.length slack →
    signing_key.SigningKey.try_sign_with_context C ours m ctx rnd ⦃ ret =>
      signatureBytes ret=(signCtx c p k [bytes m.val] (bytes ctx.val) (rnd.map fun x => bytes x.val)).map Signature.bytes ⦄
  verify : ∀ (c : Children) (_ : ChildLaws c p) (k : PublicKey) (_ : k.Shape p)
    (ours : verifying_key.VerifyingKey P (Array U8 sk) (Array U8 vk) (Array U8 sig)),
    bytes ours.bytes.val=k.bytes → ∀ (m ctx : Slice U8) (s : Signature) (_ : s.Shape p)
    (parsed : signature_encoding.Signature P (Array U8 sk) (Array U8 vk) (Array U8 sig)),
    bytes parsed.bytes.val=s.bytes → Room m.length slack →
    verifying_key.VerifyingKey.try_verify_with_context C ours m ctx parsed ⦃ ret =>
      ret = if verifyCtx c p k [bytes m.val] (bytes ctx.val) s then .Ok () else .Err () ⦄

private theorem facades (positive : 0<p.d) (new : KeygenCorrect C p)
    (sign : ∀ (k : signing_key.SigningKey P (Array U8 sk) (Array U8 vk) (Array U8 sig)) (m ctx : Slice U8)
      (rnd : Option (Slice U8)), (∀ r ∈ rnd, r.length=p.n) → Room m.length slack →
      signing_key.SigningKey.try_sign_with_context C k m ctx rnd ⦃ ret =>
        signatureBytes ret=Spec.slhSign p (bytes m.val) (bytes ctx.val) (bytes k.bytes.val)
          (match rnd with | some r => bytes r.val | none => block p (bytes k.bytes.val) 2) ⦄)
    (verify : ∀ (k : verifying_key.VerifyingKey P (Array U8 sk) (Array U8 vk) (Array U8 sig)) (m ctx : Slice U8)
      (s : signature_encoding.Signature P (Array U8 sk) (Array U8 vk) (Array U8 sig)), Room m.length slack →
      verifying_key.VerifyingKey.try_verify_with_context C k m ctx s ⦃ ret =>
        ret = if slhVerify p (bytes m.val) (bytes s.bytes.val) (bytes ctx.val) (bytes k.bytes.val)
          then .Ok () else .Err () ⦄) : Facades C p slack := by
  constructor
  · intro c node R E rng r0 r1 r2 r3 a b d ha hb hd d1 d2 d3
    apply WP.spec_mono (new rng r0 r1 r2 r3 a b d ha hb hd d1 d2 d3)
    intro out eq
    exact ⟨eq.1.trans (keygen_fips c p node _ _ _).symm,eq.2⟩
  · intro c laws k shape ours same m ctx rnd hr room
    apply WP.spec_mono (sign ours m ctx rnd hr room)
    intro out eq
    rw [sign_context c p laws positive k shape,eq,same]
    cases rnd <;> simp [key_public_block p k shape]
  · intro c laws k shape ours same m ctx s valid parsed sameSig room
    apply WP.spec_mono (verify ours m ctx parsed room)
    intro out eq
    simpa [verify_context c p laws positive k shape _ _ s valid,←sameSig,←same] using eq

end

theorem sha2_128s_facades : Facades params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.sha2_128s 409 :=
  facades _ _ _ (by decide) sha2_128s_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact sha2_128s_sign_with_context _ _ _ _ hr hm) sha2_128s_verify_with_context

theorem sha2_128f_facades : Facades params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.sha2_128f 409 :=
  facades _ _ _ (by decide) sha2_128f_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact sha2_128f_sign_with_context _ _ _ _ hr hm) sha2_128f_verify_with_context

theorem sha2_192s_facades : Facades params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.sha2_192s 561 :=
  facades _ _ _ (by decide) sha2_192s_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact sha2_192s_sign_with_context _ _ _ _ hr hm) sha2_192s_verify_with_context

theorem sha2_192f_facades : Facades params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.sha2_192f 561 :=
  facades _ _ _ (by decide) sha2_192f_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact sha2_192f_sign_with_context _ _ _ _ hr hm) sha2_192f_verify_with_context

theorem sha2_256s_facades : Facades params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.sha2_256s 561 :=
  facades _ _ _ (by decide) sha2_256s_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact sha2_256s_sign_with_context _ _ _ _ hr hm) sha2_256s_verify_with_context

theorem sha2_256f_facades : Facades params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.sha2_256f 561 :=
  facades _ _ _ (by decide) sha2_256f_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact sha2_256f_sign_with_context _ _ _ _ hr hm) sha2_256f_verify_with_context

theorem shake_128s_facades : Facades params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.shake_128s 409 :=
  facades _ _ _ (by decide) shake_128s_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact shake_128s_sign_with_context _ _ _ _ hr hm) shake_128s_verify_with_context

theorem shake_128f_facades : Facades params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.shake_128f 409 :=
  facades _ _ _ (by decide) shake_128f_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact shake_128f_sign_with_context _ _ _ _ hr hm) shake_128f_verify_with_context

theorem shake_192s_facades : Facades params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.shake_192s 561 :=
  facades _ _ _ (by decide) shake_192s_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact shake_192s_sign_with_context _ _ _ _ hr hm) shake_192s_verify_with_context

theorem shake_192f_facades : Facades params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.shake_192f 561 :=
  facades _ _ _ (by decide) shake_192f_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact shake_192f_sign_with_context _ _ _ _ hr hm) shake_192f_verify_with_context

theorem shake_256s_facades : Facades params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.shake_256s 561 :=
  facades _ _ _ (by decide) shake_256s_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact shake_256s_sign_with_context _ _ _ _ hr hm) shake_256s_verify_with_context

theorem shake_256f_facades : Facades params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.shake_256f 561 :=
  facades _ _ _ (by decide) shake_256f_new (by
    intro k m ctx rnd hr hm; cases rnd <;> exact shake_256f_sign_with_context _ _ _ _ hr hm) shake_256f_verify_with_context

end slhdsa.PeerCall
