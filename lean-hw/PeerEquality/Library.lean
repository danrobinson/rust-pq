import PeerEquality.Providers
import PeerEquality.CallerFacade

open Aeneas Aeneas.Std Result
namespace slhdsa.PeerCall
open Spec slh_dsa

section
variable {P : Type} {sk vk sig : Usize} (C : @Core P sk vk sig) (p : Spec.Params) (slack : Nat)

/-- The peer suite is fixed. No hash, WOTS, XMSS, FORS or hypertree contract is a premise. -/
structure SameFacade (c : Children) : Prop where
  keys : ∀
    {R E : Type} (rng : rand_core.CryptoRng R E) (r0 r1 r2 r3 : R) (a b d : Slice U8),
    a.length=p.n → b.length=p.n → d.length=p.n →
    (∀ buf : Slice U8, buf.val=List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r0 buf=ok (r1,a)) →
    (∀ buf : Slice U8, buf.val=List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r1 buf=ok (r2,b)) →
    (∀ buf : Slice U8, buf.val=List.replicate p.n 0#u8 → rng.RngInst.fill_bytes r2 buf=ok (r3,d)) →
    signing_key.SigningKey.new C rng r0 ⦃ result =>
      let peer := keygen c p (bytes a.val) (bytes b.val) (bytes d.val)
      keyBytes result.1=(peer.bytes,peer.public.bytes) ∧ result.2=r3 ⦄
  sign : ∀ (k : Key) (_ : k.Shape p)
    (ours : signing_key.SigningKey P (Array U8 sk) (Array U8 vk) (Array U8 sig)),
    bytes ours.bytes.val=k.bytes → ∀ (m ctx : Slice U8) (rnd : Option (Slice U8)),
    (∀ r ∈ rnd, r.length=p.n) → Room m.length slack →
    signing_key.SigningKey.try_sign_with_context C ours m ctx rnd ⦃ ret =>
      signatureBytes ret=(signCtx c p k [bytes m.val] (bytes ctx.val) (rnd.map fun x => bytes x.val)).map Signature.bytes ⦄
  verify : ∀ (k : PublicKey) (_ : k.Shape p)
    (ours : verifying_key.VerifyingKey P (Array U8 sk) (Array U8 vk) (Array U8 sig)),
    bytes ours.bytes.val=k.bytes → ∀ (m ctx : Slice U8) (s : Signature) (_ : s.Shape p)
    (parsed : signature_encoding.Signature P (Array U8 sk) (Array U8 vk) (Array U8 sig)),
    bytes parsed.bytes.val=s.bytes → Room m.length slack →
    verifying_key.VerifyingKey.try_verify_with_context C ours m ctx parsed ⦃ ret =>
      ret = if verifyCtx c p k [bytes m.val] (bytes ctx.val) s then .Ok () else .Err () ⦄

private theorem specialize {c : Children} (api : Facades C p slack) (laws : ChildLaws c p) :
    SameFacade C p slack c := ⟨api.keys c laws,api.sign c laws,api.verify c laws⟩

end

private theorem sha2_link {P : Type} {sk vk sig : Usize} {C : @Core P sk vk sig} {slack : Nat}
    (s : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing) (api : Facades C (RcSlhSha2.params s) slack) :
    RcSlhSha2.Observed route RcSlhSha2.nativeAlgorithms ∧
      SameFacade C (RcSlhSha2.params s) slack (Providers.sha2 s RcSlhSha2.nativeAlgorithms) := by
  have obs := (RcSlhSha2.observed_iff route RcSlhSha2.nativeAlgorithms).mpr rfl
  exact ⟨obs,specialize _ _ _ api (Providers.sha2_laws s route _ obs)⟩

private theorem shake_link {P : Type} {sk vk sig : Usize} {C : @Core P sk vk sig}
    {slack : Nat} {p : Spec.Params} (v : p.Valid) (family : p.family=.shake) (api : Facades C p slack) :
    SameFacade C p slack (Providers.shake p) :=
  specialize _ _ _ api (Providers.shake_laws p v family)

theorem sha2_128s_peer (route : RcSlhSha2.Routing) :
    RcSlhSha2.Observed route RcSlhSha2.nativeAlgorithms ∧
    SameFacade params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.sha2_128s 409
      (Providers.sha2 .s128 RcSlhSha2.nativeAlgorithms) :=
  sha2_link .s128 route sha2_128s_facades

theorem sha2_128f_peer (route : RcSlhSha2.Routing) :
    RcSlhSha2.Observed route RcSlhSha2.nativeAlgorithms ∧
    SameFacade params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.sha2_128f 409
      (Providers.sha2 .f128 RcSlhSha2.nativeAlgorithms) :=
  sha2_link .f128 route sha2_128f_facades

theorem sha2_192s_peer (route : RcSlhSha2.Routing) :
    RcSlhSha2.Observed route RcSlhSha2.nativeAlgorithms ∧
    SameFacade params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.sha2_192s 561
      (Providers.sha2 .s192 RcSlhSha2.nativeAlgorithms) :=
  sha2_link .s192 route sha2_192s_facades

theorem sha2_192f_peer (route : RcSlhSha2.Routing) :
    RcSlhSha2.Observed route RcSlhSha2.nativeAlgorithms ∧
    SameFacade params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.sha2_192f 561
      (Providers.sha2 .f192 RcSlhSha2.nativeAlgorithms) :=
  sha2_link .f192 route sha2_192f_facades

theorem sha2_256s_peer (route : RcSlhSha2.Routing) :
    RcSlhSha2.Observed route RcSlhSha2.nativeAlgorithms ∧
    SameFacade params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.sha2_256s 561
      (Providers.sha2 .s256 RcSlhSha2.nativeAlgorithms) :=
  sha2_link .s256 route sha2_256s_facades

theorem sha2_256f_peer (route : RcSlhSha2.Routing) :
    RcSlhSha2.Observed route RcSlhSha2.nativeAlgorithms ∧
    SameFacade params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.sha2_256f 561
      (Providers.sha2 .f256 RcSlhSha2.nativeAlgorithms) :=
  sha2_link .f256 route sha2_256f_facades

theorem shake_128s_peer : SameFacade params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.shake_128s 409 (Providers.shake Spec.shake_128s) :=
  shake_link (by constructor <;> decide) rfl shake_128s_facades

theorem shake_128f_peer : SameFacade params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.shake_128f 409 (Providers.shake Spec.shake_128f) :=
  shake_link (by constructor <;> decide) rfl shake_128f_facades

theorem shake_192s_peer : SameFacade params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.shake_192s 561 (Providers.shake Spec.shake_192s) :=
  shake_link (by constructor <;> decide) rfl shake_192s_facades

theorem shake_192f_peer : SameFacade params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.shake_192f 561 (Providers.shake Spec.shake_192f) :=
  shake_link (by constructor <;> decide) rfl shake_192f_facades

theorem shake_256s_peer : SameFacade params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.shake_256s 561 (Providers.shake Spec.shake_256s) :=
  shake_link (by constructor <;> decide) rfl shake_256s_facades

theorem shake_256f_peer : SameFacade params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.shake_256f 561 (Providers.shake Spec.shake_256f) :=
  shake_link (by constructor <;> decide) rfl shake_256f_facades

end slhdsa.PeerCall
