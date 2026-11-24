import Spec.AppleNativeSession
import Spec.ApplePureWrapperWitness

/-! Successful public keygen → pure sign → pure verify on the measured Apple
image. The two callers independently construct their frame, with independent
successful allocation decisions. The signer reads its key from the keygen
return and the verifier reads its signature from the public signing return.
Cryptographic calls use the reference implementations of their contracts. -/
namespace LinkedArm.PureNativeSession
open Spec NativeSession

inductive Set | s128 | f128 | s192 | f192 | s256 | f256 deriving DecidableEq, Repr
inductive Signing | sign | alias | deterministic deriving DecidableEq, Repr
structure Wrappers where
  sign : Signing → ArmPureWrapper.Image
  verify : Bool → ArmPureWrapper.Image
  signChecked : ∀ m, ArmPureWrapper.run (sign m) true = some .forwarded
  verifyChecked : ∀ b, ArmPureWrapper.run (verify b) true = some .forwarded

def params : Set → Params
  | .s128 => Spec.shake_128s
  | .f128 => Spec.shake_128f
  | .s192 => Spec.shake_192s
  | .f192 => Spec.shake_192f
  | .s256 => Spec.shake_256s
  | .f256 => Spec.shake_256f

def entries : (s : Set) → Entries (params s)
  | .s128 => NativeSession.shake_128s_entries
  | .f128 => NativeSession.shake_128f_entries
  | .s192 => NativeSession.shake_192s_entries
  | .f192 => NativeSession.shake_192f_entries
  | .s256 => NativeSession.shake_256s_entries
  | .f256 => NativeSession.shake_256f_entries

open LinkedApplePure in
def wrappers : Set → Wrappers
  | .s128 => ⟨(fun | .sign => shake_128s_sign | .alias => shake_128s_slh_sign | .deterministic => shake_128s_sign_deterministic),
      (fun | false => shake_128s_verify | true => shake_128s_slh_verify),
      (fun | .sign => shake_128s_sign_valid | .alias => shake_128s_slh_sign_valid | .deterministic => shake_128s_sign_deterministic_valid),
      (fun | false => shake_128s_verify_valid | true => shake_128s_slh_verify_valid)⟩
  | .f128 => ⟨(fun | .sign => shake_128f_sign | .alias => shake_128f_slh_sign | .deterministic => shake_128f_sign_deterministic),
      (fun | false => shake_128f_verify | true => shake_128f_slh_verify),
      (fun | .sign => shake_128f_sign_valid | .alias => shake_128f_slh_sign_valid | .deterministic => shake_128f_sign_deterministic_valid),
      (fun | false => shake_128f_verify_valid | true => shake_128f_slh_verify_valid)⟩
  | .s192 => ⟨(fun | .sign => shake_192s_sign | .alias => shake_192s_slh_sign | .deterministic => shake_192s_sign_deterministic),
      (fun | false => shake_192s_verify | true => shake_192s_slh_verify),
      (fun | .sign => shake_192s_sign_valid | .alias => shake_192s_slh_sign_valid | .deterministic => shake_192s_sign_deterministic_valid),
      (fun | false => shake_192s_verify_valid | true => shake_192s_slh_verify_valid)⟩
  | .f192 => ⟨(fun | .sign => shake_192f_sign | .alias => shake_192f_slh_sign | .deterministic => shake_192f_sign_deterministic),
      (fun | false => shake_192f_verify | true => shake_192f_slh_verify),
      (fun | .sign => shake_192f_sign_valid | .alias => shake_192f_slh_sign_valid | .deterministic => shake_192f_sign_deterministic_valid),
      (fun | false => shake_192f_verify_valid | true => shake_192f_slh_verify_valid)⟩
  | .s256 => ⟨(fun | .sign => shake_256s_sign | .alias => shake_256s_slh_sign | .deterministic => shake_256s_sign_deterministic),
      (fun | false => shake_256s_verify | true => shake_256s_slh_verify),
      (fun | .sign => shake_256s_sign_valid | .alias => shake_256s_slh_sign_valid | .deterministic => shake_256s_sign_deterministic_valid),
      (fun | false => shake_256s_verify_valid | true => shake_256s_slh_verify_valid)⟩
  | .f256 => ⟨(fun | .sign => shake_256f_sign | .alias => shake_256f_slh_sign | .deterministic => shake_256f_sign_deterministic),
      (fun | false => shake_256f_verify | true => shake_256f_slh_verify),
      (fun | .sign => shake_256f_sign_valid | .alias => shake_256f_slh_sign_valid | .deterministic => shake_256f_sign_deterministic_valid),
      (fun | false => shake_256f_verify_valid | true => shake_256f_slh_verify_valid)⟩

def verifyImage : Set → ArmVerifyBody.Image
  | .s128 => LinkedAppleVerifyBody.shake_128s_image
  | .f128 => LinkedAppleVerifyBody.shake_128f_image
  | .s192 => LinkedAppleVerifyBody.shake_192s_image
  | .f192 => LinkedAppleVerifyBody.shake_192f_image
  | .s256 => LinkedAppleVerifyBody.shake_256s_image
  | .f256 => LinkedAppleVerifyBody.shake_256f_image

def wired (set : Set) (m : Signing) (useAlias : Bool) : Bool :=
  let e := entries set
  let sw := (wrappers set).sign m
  let vw := (wrappers set).verify useAlias
  let v := verifyImage set
  sw.core == e.signing.body && sw.param == e.signing.cfg.param && sw.frame == LinkedApplePureFrame.image.entry &&
    sw.mode == (if m = .deterministic then .deterministic else .sign) && sw.n == (params set).n &&
    vw.core == v.body && vw.param == v.gate.param && vw.frame == LinkedApplePureFrame.image.entry &&
    vw.mode == .verify && vw.n == (params set).n

theorem wiring (set : Set) (m : Signing) (useAlias : Bool) : wired set m useAlias = true := by
  cases set <;> cases m <;> cases useAlias <;> rfl

theorem verifyTarget (set : Set) : (entries set).verifyRun = ArmVerifyBody.run (verifyImage set) := by
  cases set <;> rfl

structure Allocation where
  one : Bool
  contextReserve : Bool
  messageReserve : Bool

def frame (a : Allocation) (msg ctx : Bytes) : Option Bytes := do
  let b : ArmPureFrame.Choices := ⟨a.one,a.contextReserve,a.messageReserve,decide (ctx = []),decide (msg = [])⟩
  let parts ← ArmPureFrame.run LinkedApplePureFrame.image b
  return parts.flatMap (ArmPureFrame.bytes msg ctx)

theorem frame_eq (a : Allocation) (msg ctx : Bytes) :
    frame a msg ctx = some (withContext msg ctx) := by
  simp only [frame,LinkedApplePureFrame.checked]
  change some _ = some _
  exact congrArg some (ArmPureFrame.expected_bytes _ msg ctx rfl rfl)

def randomness (m : Signing) (p : Params) (sk supplied : Bytes) :=
  if m = .deterministic then Spec.block p sk 2 else supplied

/-- Return the owned signature option alongside the keys and the verification Boolean.
The public verifier receives the exact Some payload. Its hash calls read its own
frame. Each frame can move on different grow/reserve branches. -/
def run (set : Set) (m : Signing) (useAlias : Bool) (a b : Allocation) (prof : Fin 4)
    (secret prf seed msg ctx supplied : Bytes) : Option ((Bytes × Bytes) × Option Bytes × Bool) := do
  guard (wired set m useAlias && decide (2 + ctx.length + msg.length < 2^63))
  let p := params set
  let e := entries set
  let keys ← ArmKeygen.run e.kg e.path
  let src := keySources p secret prf seed
  let sk := readKey src keys.1
  let pk := readKey src keys.2
  let rand := randomness m p sk supplied
  let sw ← ArmPureWrapper.execute ((wrappers set).sign m) ctx
  let sf ← frame a msg ctx
  if h : sk.length = 4*p.n ∧ pk.length = 2*p.n ∧ rand.length = p.n then
    let obs ← ArmInternalSigner.run e.signing prof
    let s := e.model.reference sf sk rand h.1 h.2.2
    let sig := ArmPureWrapper.signReturn sw (e.model.result s obs)
    let bytes ← sig
    let vw ← ArmPureWrapper.execute ((wrappers set).verify useAlias) ctx
    let vf ← frame b msg ctx
    if hs : bytes.length = p.sigBytes then
      let events ← ArmVerifyBody.run (verifyImage set)
      let v := referenceVerifier e.valid vf bytes pk hs h.2.1
      return ((sk,pk),sig,ArmPureWrapper.verifyReturn vw (ArmVerifyBody.returned v events))
    else none
  else none

private theorem observedKeys {p} (e : Entries p) (sec prf seed : Bytes)
    (sizes : sec.length = p.n ∧ prf.length = p.n ∧ seed.length = p.n) :
    let src := keySources p sec prf seed
    (readKey src (ArmKeygen.secret p.n), readKey src (ArmKeygen.publicKey p.n)) = slhKeygenInternal p sec prf seed := by
  let src := keySources p sec prf seed
  have sized (i : Nat) (hi : i < 4) : (src i).length = p.n := by
    interval_cases i
    · exact sizes.1
    · exact sizes.2.1
    · exact sizes.2.2
    · exact xmssNode_length p e.valid _ _ _ _ _
  exact (ArmKeygen.concreteKeyGeneration e.keyChecked e.keyChecked src sized e.keyWidth.1
    e.keyWidth.2 (Signer.referenceNode _ _ _ _ _ _)).eq_spec

/-- For each measured public set and alias, replay the returns of the actual
wrappers and frame builders and run the cryptographic callees by reference.
The result contains the generated keys, the public signature option and true. -/
theorem run_eq (set : Set) (m : Signing) (useAlias : Bool) (a b : Allocation) (prof : Fin 4)
    (sec prf seed msg ctx supplied : Bytes)
    (sizes : sec.length = (params set).n ∧ prf.length = (params set).n ∧ seed.length = (params set).n)
    (rnd : m ≠ .deterministic → supplied.length = (params set).n)
    (short : ctx.length ≤ 255) (fits : 2 + ctx.length + msg.length < 2^63) :
    let p := params set
    let keys := slhKeygenInternal p sec prf seed
    run set m useAlias a b prof sec prf seed msg ctx supplied =
      some (keys, slhSign p msg ctx keys.1 (randomness m p keys.1 supplied),true) := by
  let p := params set
  let e := entries set
  let src := keySources p sec prf seed
  let sk := readKey src (ArmKeygen.secret p.n)
  let pk := readKey src (ArmKeygen.publicKey p.n)
  let keys := slhKeygenInternal p sec prf seed
  change sec.length = p.n ∧ prf.length = p.n ∧ seed.length = p.n at sizes
  have key : (sk,pk) = keys := observedKeys e sec prf seed sizes
  have kl : sk.length = 4*p.n ∧ pk.length = 2*p.n := by
    have len := congrArg (fun (x : Bytes × Bytes) => (x.1.length,x.2.length)) key
    simp only [keys,slhKeygenInternal,List.length_append,xmssNode_length p e.valid,sizes.1,sizes.2.1,sizes.2.2,Prod.mk.injEq] at len
    omega
  let random := randomness m p sk supplied
  have rl : random.length = p.n := by
    by_cases hm : m = .deterministic
    · simp [random,randomness,hm,Spec.block,kl.1]; omega
    · simpa [random,randomness,hm] using rnd hm
  let sf := withContext msg ctx
  have h : sk.length = 4*p.n ∧ pk.length = 2*p.n ∧ random.length = p.n := ⟨kl.1,kl.2,rl⟩
  let calls := e.model.reference sf sk random h.1 h.2.2
  let sig := e.model.result calls e.model.expected
  have hs : sig = slhSignInternal p sf sk random := e.signEq prof (e.signChecked prof) calls
  have sl : sig.length = p.sigBytes := hs ▸ slhSignInternal_length p e.valid _ _ _
  have inner := NativeSession.run_eq e prof sec prf seed sf random ⟨sizes.1,sizes.2.1,sizes.2.2,rl⟩
  unfold runWithReferenceCalls at inner
  simp only [e.keyChecked,e.signChecked,e.verifyChecked] at inner
  change (if h' : sk.length = 4*p.n ∧ pk.length = 2*p.n ∧ random.length = p.n then _ else _) = _ at inner
  rw [dite_eq_left h] at inner
  change (if hs' : sig.length = p.sigBytes then _ else _) = _ at inner
  rw [dite_eq_left sl] at inner
  let verdict := ArmVerifyBody.returned (referenceVerifier e.valid sf sig pk sl h.2.1) e.verifyEvents
  change some ((sk,pk),sig,verdict) = some (keys,slhSignInternal p sf keys.1 random,true) at inner
  have inner' := Option.some.inj inner
  have sw := ArmPureWrapper.validContext ((wrappers set).signChecked m) short
  have vw := ArmPureWrapper.validContext ((wrappers set).verifyChecked useAlias) short
  change run set m useAlias a b prof sec prf seed msg ctx supplied =
    some (keys,slhSign p msg ctx keys.1 (randomness m p keys.1 supplied),true)
  unfold run
  simp only [show ArmKeygen.run (entries set).kg (entries set).path = _ from e.keyChecked,
    sw,vw,frame_eq,wiring,fits,← verifyTarget]
  change (if h' : sk.length = 4*p.n ∧ pk.length = 2*p.n ∧ random.length = p.n then _ else _) = _
  rw [dite_eq_left h]
  simp only [show ArmInternalSigner.run (entries set).signing prof = _ from e.signChecked prof,
    ArmPureWrapper.signReturn,ite_true]
  change (if hs' : sig.length = p.sigBytes then _ else _) = _
  rw [dite_eq_left sl]
  change (do let events ← e.verifyRun; return ((sk,pk),some sig,ArmPureWrapper.verifyReturn .forwarded
    (ArmVerifyBody.returned (referenceVerifier e.valid sf sig pk sl h.2.1) events))) = _
  rw [e.verifyChecked]
  change some ((sk,pk),some sig,verdict) = _
  have skEq := congrArg Prod.fst key
  change sk = keys.1 at skEq
  simpa only [slhSign,show ¬ ctx.length > 255 by omega,ite_false,sf,random,skEq] using
    congrArg (fun x : (Bytes × Bytes) × Bytes × Bool => some (x.1,some x.2.1,x.2.2)) inner'

#print axioms run_eq
run_cmd
  for ax in (← Lean.collectAxioms ``run_eq) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Public SHAKE session proof depends on unexpected axiom {ax}"
end LinkedArm.PureNativeSession
