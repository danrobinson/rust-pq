import Spec.ApplePureNativeSession
import Spec.AppleSha2NativeSession
import Spec.AppleSha2PublicSignWitness

/-! Public SHA-2 key generation, signing and verification on the measured Apple
binary. The dispatcher selects the contiguous SHA-2 internal signer through 1023
message bytes, and the segmented entry from 1024 bytes. The long signer and the
public verifier are explicit interfaces so their binary proofs can be supplied
independently. -/
namespace LinkedArm.Sha2PureNativeSession
open Spec NativeSession
open PureNativeSession (Signing Allocation)
abbrev Set := PureNativeSession.Set

def params : Set → Params
  | .s128 => Spec.sha2_128s
  | .f128 => Spec.sha2_128f
  | .s192 => Spec.sha2_192s
  | .f192 => Spec.sha2_192f
  | .s256 => Spec.sha2_256s
  | .f256 => Spec.sha2_256f

def entries : (s : Set) → Entries (params s)
  | .s128 => NativeSession.sha2_128s_entries
  | .f128 => NativeSession.sha2_128f_entries
  | .s192 => NativeSession.sha2_192s_entries
  | .f192 => NativeSession.sha2_192f_entries
  | .s256 => NativeSession.sha2_256s_entries
  | .f256 => NativeSession.sha2_256f_entries

def segment : Set → ArmSegmentedFrame.Image
  | .s128 => LinkedSegmentedFrame.sha2_128s
  | .f128 => LinkedSegmentedFrame.sha2_128f
  | .s192 => LinkedSegmentedFrame.sha2_192s
  | .f192 => LinkedSegmentedFrame.sha2_192f
  | .s256 => LinkedSegmentedFrame.sha2_256s
  | .f256 => LinkedSegmentedFrame.sha2_256f

def signer : Set → Signing → ArmSha2PublicSign.Image
  | .s128, .sign => LinkedAppleSha2PublicSign.sha2_128s_sign
  | .s128, .alias => LinkedAppleSha2PublicSign.sha2_128s_slh_sign
  | .s128, .deterministic => LinkedAppleSha2PublicSign.sha2_128s_sign_deterministic
  | .f128, .sign => LinkedAppleSha2PublicSign.sha2_128f_sign
  | .f128, .alias => LinkedAppleSha2PublicSign.sha2_128f_slh_sign
  | .f128, .deterministic => LinkedAppleSha2PublicSign.sha2_128f_sign_deterministic
  | .s192, .sign => LinkedAppleSha2PublicSign.sha2_192s_sign
  | .s192, .alias => LinkedAppleSha2PublicSign.sha2_192s_slh_sign
  | .s192, .deterministic => LinkedAppleSha2PublicSign.sha2_192s_sign_deterministic
  | .f192, .sign => LinkedAppleSha2PublicSign.sha2_192f_sign
  | .f192, .alias => LinkedAppleSha2PublicSign.sha2_192f_slh_sign
  | .f192, .deterministic => LinkedAppleSha2PublicSign.sha2_192f_sign_deterministic
  | .s256, .sign => LinkedAppleSha2PublicSign.sha2_256s_sign
  | .s256, .alias => LinkedAppleSha2PublicSign.sha2_256s_slh_sign
  | .s256, .deterministic => LinkedAppleSha2PublicSign.sha2_256s_sign_deterministic
  | .f256, .sign => LinkedAppleSha2PublicSign.sha2_256f_sign
  | .f256, .alias => LinkedAppleSha2PublicSign.sha2_256f_slh_sign
  | .f256, .deterministic => LinkedAppleSha2PublicSign.sha2_256f_sign_deterministic
theorem signerChecked (set : Set) (m : Signing) (vc short : Bool) :
    ArmSha2PublicSign.run (signer set m) vc short = some (ArmSha2PublicSign.expected vc short) := by
  cases set <;> cases m
  · exact LinkedAppleSha2PublicSign.sha2_128s_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_128s_slh_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_128s_sign_deterministic_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_128f_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_128f_slh_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_128f_sign_deterministic_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_192s_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_192s_slh_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_192s_sign_deterministic_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_192f_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_192f_slh_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_192f_sign_deterministic_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_256s_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_256s_slh_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_256s_sign_deterministic_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_256f_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_256f_slh_sign_checked vc short
  · exact LinkedAppleSha2PublicSign.sha2_256f_sign_deterministic_checked vc short

def wired (set : Set) (m : Signing) : Bool :=
  let a := signer set m
  let e := entries set
  a.n == (params set).n && a.deterministic == decide (m = .deterministic) &&
    a.core == e.signing.body && a.param == e.signing.cfg.param &&
    a.frame == LinkedApplePureFrame.image.entry &&
    a.segmented == (segment set).entry && a.param == (segment set).param

theorem wiring (set : Set) (m : Signing) : wired set m = true := by cases set <;> cases m <;> rfl

/-- Verified implementations can instantiate this interface with their actual
segmented signer result and public verifier result. The handshake fixes the
parameter set, both caller slices, the exact returned signature and key. -/
structure OuterCalls (s : Set) where
  longSign : Fin 4 → (msg ctx key rnd : Bytes) → Option Bytes
  longEq : ∀ prof msg ctx key rnd, ctx.length ≤ 255 → 1024 ≤ msg.length →
    key.length = 4*(params s).n → rnd.length = (params s).n →
    longSign prof msg ctx key rnd = slhSign (params s) msg ctx key rnd
  verify : Bool → Fin 8 → (msg ctx sig pk : Bytes) → Option Bool
  verifyEq : ∀ useAlias prof msg ctx sig pk, ctx.length ≤ 255 → sig.length = (params s).sigBytes →
    pk.length = 2*(params s).n → verify useAlias prof msg ctx sig pk = some (slhVerify (params s) msg sig ctx pk)

def sign (s : Set) (m : Signing) (a : Allocation) (prof : Fin 4) (calls : OuterCalls s)
    (msg ctx key supplied : Bytes) : Option (Option Bytes) := do
  guard (wired s m)
  let route ← ArmSha2PublicSign.execute (signer s m) msg ctx
  let rnd := PureNativeSession.randomness m (params s) key supplied
  match route with
  | .rejected => return none
  | .segmented => return calls.longSign prof msg ctx key rnd
  | .contiguous =>
    let frame ← PureNativeSession.frame a msg ctx
    let e := entries s
    if h : key.length = 4*(params s).n ∧ rnd.length = (params s).n then
      let obs ← ArmInternalSigner.run e.signing prof
      let c := e.model.reference frame key rnd h.1 h.2
      return some (e.model.result c obs)
    else none

theorem sign_eq (s : Set) (m : Signing) (a : Allocation) (prof : Fin 4) (calls : OuterCalls s)
    (msg ctx key supplied : Bytes) (valid : ctx.length ≤ 255) (size : key.length = 4*(params s).n)
    (rnd : (PureNativeSession.randomness m (params s) key supplied).length = (params s).n) :
    sign s m a prof calls msg ctx key supplied =
      some (slhSign (params s) msg ctx key (PureNativeSession.randomness m (params s) key supplied)) := by
  let e := entries s
  let random := PureNativeSession.randomness m (params s) key supplied
  have h : key.length = 4*(params s).n ∧ random.length = (params s).n := ⟨size,rnd⟩
  by_cases small : msg.length ≤ 1023
  · simp [sign,wiring,ArmSha2PublicSign.execute,signerChecked,ArmSha2PublicSign.expected,valid,small,
      PureNativeSession.frame_eq,slhSign,show ¬ctx.length > 255 by omega,size,rnd,(entries s).signChecked,
      (entries s).signEq prof ((entries s).signChecked prof)]
  · simp [sign,wiring,ArmSha2PublicSign.execute,signerChecked,ArmSha2PublicSign.expected,valid,small,
      calls.longEq prof msg ctx key _ valid (by omega) size rnd]

theorem sign_rejects (s : Set) (m : Signing) (a : Allocation) (prof : Fin 4) (calls : OuterCalls s)
    (msg ctx key supplied : Bytes) (invalid : 255 < ctx.length) :
    sign s m a prof calls msg ctx key supplied = some none := by
  simp [sign,wiring,ArmSha2PublicSign.execute,signerChecked,ArmSha2PublicSign.expected,show ¬ctx.length ≤ 255 by omega]

def run (s : Set) (m : Signing) (useAlias : Bool) (a : Allocation) (prof : Fin 4) (vp : Fin 8)
    (calls : OuterCalls s) (secret prf seed msg ctx supplied : Bytes) : Option ((Bytes × Bytes) × Option Bytes × Bool) := do
  guard (decide (2 + ctx.length + msg.length < 2^63))
  let e := entries s
  let keys ← ArmKeygen.run e.kg e.path
  let src := keySources (params s) secret prf seed
  let sk := readKey src keys.1
  let pk := readKey src keys.2
  let result ← sign s m a prof calls msg ctx sk supplied
  let sig ← result
  let v ← calls.verify useAlias vp msg ctx sig pk
  return ((sk,pk),result,v)

theorem run_eq (s : Set) (m : Signing) (useAlias : Bool) (a : Allocation) (prof : Fin 4) (vp : Fin 8)
    (calls : OuterCalls s) (sec prf seed msg ctx supplied : Bytes)
    (sizes : sec.length = (params s).n ∧ prf.length = (params s).n ∧ seed.length = (params s).n)
    (rnd : m ≠ .deterministic → supplied.length = (params s).n)
    (valid : ctx.length ≤ 255) (fits : 2 + ctx.length + msg.length < 2^63) :
    let p := params s
    let keys := slhKeygenInternal p sec prf seed
    run s m useAlias a prof vp calls sec prf seed msg ctx supplied =
      some (keys,slhSign p msg ctx keys.1 (PureNativeSession.randomness m p keys.1 supplied),true) := by
  let p := params s
  let e := entries s
  let src := keySources p sec prf seed
  let sk := readKey src (ArmKeygen.secret p.n)
  let pk := readKey src (ArmKeygen.publicKey p.n)
  let keys := slhKeygenInternal p sec prf seed
  change sec.length = p.n ∧ prf.length = p.n ∧ seed.length = p.n at sizes
  have sized (i : Nat) (hi : i < 4) : (src i).length = p.n := by
    interval_cases i
    · exact sizes.1
    · exact sizes.2.1
    · exact sizes.2.2
    · exact xmssNode_length p e.valid _ _ _ _ _
  have key : (sk,pk) = keys := (ArmKeygen.concreteKeyGeneration e.keyChecked e.keyChecked src sized e.keyWidth.1
    e.keyWidth.2 (Signer.referenceNode _ _ _ _ _ _)).eq_spec
  have kl : sk.length = 4*p.n ∧ pk.length = 2*p.n := by
    have len := congrArg (fun (x : Bytes × Bytes) => (x.1.length,x.2.length)) key
    simp only [keys,slhKeygenInternal,List.length_append,xmssNode_length p e.valid,sizes.1,sizes.2.1,sizes.2.2,Prod.mk.injEq] at len
    omega
  let random := PureNativeSession.randomness m p sk supplied
  have rl : random.length = p.n := by
    by_cases hm : m = .deterministic
    · simp [random,PureNativeSession.randomness,hm,Spec.block,kl.1]; omega
    · simpa [random,PureNativeSession.randomness,hm] using rnd hm
  let sig := slhSignInternal p (withContext msg ctx) sk random
  have sl : sig.length = p.sigBytes := slhSignInternal_length p e.valid _ _ _
  have ok := keygen_keyOk p e.valid sec prf seed sizes.1 sizes.2.1 sizes.2.2
  change KeyOk p keys.1 ∧ keys.2 = skPk p keys.1 at ok
  rw [← key] at ok
  have accepts := slh_complete_internal p e.valid (withContext msg ctx) sk random ok.1
  have pkEq : pk = skPk p sk := ok.2
  have verify : slhVerify p msg sig ctx pk = true := by
    simp only [slhVerify,show ¬ctx.length > 255 by omega,ite_false]
    rw [pkEq]
    exact accepts
  have signOk := sign_eq s m a prof calls msg ctx sk supplied valid kl.1 rl
  have sigOk : slhSign p msg ctx sk random = some sig := by simp [slhSign,show ¬ctx.length > 255 by omega,sig]
  change sign s m a prof calls msg ctx sk supplied = some (slhSign p msg ctx sk random) at signOk
  rw [sigOk] at signOk
  have vr := calls.verifyEq useAlias vp msg ctx sig pk valid sl kl.2
  rw [verify] at vr
  unfold run
  simp only [fits,decide_true,show ArmKeygen.run (entries s).kg (entries s).path = _ from e.keyChecked]
  change (do let result ← sign s m a prof calls msg ctx sk supplied; let out ← result; let v ← calls.verify useAlias vp msg ctx out pk; return ((sk,pk),result,v)) = _
  rw [signOk]
  change (do let v ← calls.verify useAlias vp msg ctx sig pk; return ((sk,pk),some sig,v)) = _
  rw [vr]
  change some ((sk,pk),some sig,true) = some (keys,slhSign p msg ctx keys.1 (PureNativeSession.randomness m p keys.1 supplied),true)
  rw [← key]
  exact congrArg (fun z => some ((sk,pk),z,true)) sigOk.symm

#print axioms run_eq
end LinkedArm.Sha2PureNativeSession
