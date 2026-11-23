import Spec.AppleSha2PureNativeSession
import Spec.AppleSha2PublicVerifyWitness
import Spec.AppleSegmentedFrameWitness

/-! Instantiate the public SHA-2 session interfaces with the measured segmented
signer and both public verification aliases. Reference calls supply cryptographic
outputs under the corresponding native leaf and hash contracts. The tuple
contains the returned secret/public key pair, owned signature option and Boolean.
Its proof includes both allocating and segmented public routes on every SHA-2
parameter set. It assumes bounded valid slices, nonoverlapping writable memory,
the modeled successful allocator/ABI, and the documented native digest and
subtree call contracts. Panic, unwinding and allocation failure are outside it. -/
namespace LinkedArm.Sha2PureNativeSession
open Spec NativeSession

def longImage : Set → ArmSegmentedSigner.Image
  | .s128 => LinkedSegmentedFrame.full_sha2_128s
  | .f128 => LinkedSegmentedFrame.full_sha2_128f
  | .s192 => LinkedSegmentedFrame.full_sha2_192s
  | .f192 => LinkedSegmentedFrame.full_sha2_192f
  | .s256 => LinkedSegmentedFrame.full_sha2_256s
  | .f256 => LinkedSegmentedFrame.full_sha2_256f

theorem longBinding (s : Set) : (longImage s).frame = segment s := by cases s <;> rfl

theorem longRow (s : Set) : (longImage s).frame.p = params s := by cases s <;> rfl

theorem longChecked (s : Set) (i : Fin 4) :
    ArmSegmentedSigner.run (longImage s) i = some ArmSegmentedSigner.expected := by
  cases s
  · exact LinkedSegmentedFrame.full_sha2_128s_checked i
  · exact LinkedSegmentedFrame.full_sha2_128f_checked i
  · exact LinkedSegmentedFrame.full_sha2_192s_checked i
  · exact LinkedSegmentedFrame.full_sha2_192f_checked i
  · exact LinkedSegmentedFrame.full_sha2_256s_checked i
  · exact LinkedSegmentedFrame.full_sha2_256f_checked i

def verifyImage : Set → Bool → ArmSha2PublicVerify.Image
  | .s128, false => LinkedAppleSha2PublicVerify.sha2_128s_verify
  | .s128, true => LinkedAppleSha2PublicVerify.sha2_128s_slh_verify
  | .f128, false => LinkedAppleSha2PublicVerify.sha2_128f_verify
  | .f128, true => LinkedAppleSha2PublicVerify.sha2_128f_slh_verify
  | .s192, false => LinkedAppleSha2PublicVerify.sha2_192s_verify
  | .s192, true => LinkedAppleSha2PublicVerify.sha2_192s_slh_verify
  | .f192, false => LinkedAppleSha2PublicVerify.sha2_192f_verify
  | .f192, true => LinkedAppleSha2PublicVerify.sha2_192f_slh_verify
  | .s256, false => LinkedAppleSha2PublicVerify.sha2_256s_verify
  | .s256, true => LinkedAppleSha2PublicVerify.sha2_256s_slh_verify
  | .f256, false => LinkedAppleSha2PublicVerify.sha2_256f_verify
  | .f256, true => LinkedAppleSha2PublicVerify.sha2_256f_slh_verify

theorem verifyRow (s : Set) (b : Bool) : (verifyImage s b).internal.core.p = params s := by
  cases s <;> cases b <;> rfl

theorem verifiedEq (s : Set) (b : Bool) (vp : Fin 8) (msg ctx sig pk : Bytes)
    (v : ArmSha2Verify.Callees (verifyImage s b).internal.core.p (ArmSha2PublicVerify.input msg ctx vp) sig pk) :
    ArmSha2PublicVerify.verified (a := verifyImage s b) (choices := vp) (msg := msg) (ctx := ctx) v =
      some (slhVerify (verifyImage s b).internal.core.p msg sig ctx pk) := by
  cases s <;> cases b
  · exact LinkedAppleSha2PublicVerify.sha2_128s_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_128s_slh_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_128f_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_128f_slh_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_192s_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_192s_slh_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_192f_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_192f_slh_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_256s_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_256s_slh_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_256f_verify_eq v
  · exact LinkedAppleSha2PublicVerify.sha2_256f_slh_verify_eq v

private theorem row (s : Set) : (longImage s).frame.p ∈ sha2Sets := by cases s <;> decide

def longReference (s : Set) (prof : Fin 4) (msg ctx key rnd : Bytes) : Option Bytes := do
  guard ((longImage s).frame.entry == (segment s).entry && (longImage s).frame.param == (segment s).param)
  if h : key.length = 4*(longImage s).frame.p.n ∧ rnd.length = (longImage s).frame.p.n then
    (ArmSegmentedSigner.run (longImage s) prof).map fun (f,o) =>
      ArmInternalSigner.Sha2.materialize (referenceSha2Signer (row s)
        (ArmSegmentedFrame.evaluate rnd ctx msg f.digest) key rnd h.1 h.2) o
  else none

def verifyReference (s : Set) (b : Bool) (vp : Fin 8) (msg ctx sig pk : Bytes) : Option Bool :=
  let p := (verifyImage s b).internal.core.p
  if h : sig.length = p.sigBytes ∧ pk.length = 2*p.n then
    let pv : p.Valid := by simpa only [p,verifyRow] using (entries s).valid
    let v := referenceVerifier pv (ArmSha2PublicVerify.input msg ctx vp) sig pk h.1 h.2
    ArmSha2PublicVerify.verified (a := verifyImage s b) (choices := vp) (msg := msg) (ctx := ctx) v
  else none

def referenceOuter (s : Set) : OuterCalls s where
  longSign := longReference s
  longEq := by
    intro prof msg ctx key rnd vc long keySize rndSize
    have k : key.length = 4*(longImage s).frame.p.n := by simpa [longRow] using keySize
    have r : rnd.length = (longImage s).frame.p.n := by simpa [longRow] using rndSize
    unfold longReference
    simp only [show (longImage s).frame.entry = (segment s).entry from congrArg ArmSegmentedFrame.Image.entry (longBinding s),
      show (longImage s).frame.param = (segment s).param from congrArg ArmSegmentedFrame.Image.param (longBinding s),
      beq_self_eq_true, Bool.and_self]
    change (if h : key.length = 4*(longImage s).frame.p.n ∧ rnd.length = (longImage s).frame.p.n then _ else _) = _
    rw [dite_eq_left (And.intro k r)]
    exact (ArmSegmentedSigner.referenceResult (longChecked s prof) (row s) msg ctx key rnd k r vc long).trans
      (congrArg (fun p => slhSign p msg ctx key rnd) (longRow s))
  verify := verifyReference s
  verifyEq := by
    intro b vp msg ctx sig pk _ hs hk
    have h : sig.length = (verifyImage s b).internal.core.p.sigBytes ∧ pk.length = 2*(verifyImage s b).internal.core.p.n := by
      simpa [verifyRow] using And.intro hs hk
    unfold verifyReference
    dsimp only
    rw [dite_eq_left h]
    exact (verifiedEq s b vp msg ctx sig pk _).trans
      (congrArg (fun p => some (slhVerify p msg sig ctx pk)) (verifyRow s b))

/-- One theorem for the measured keygen, all three public signing entries and
both verification aliases, for messages on either side of the 1024-byte cutoff. -/
theorem public_run_eq (s : Set) (m : PureNativeSession.Signing) (useAlias : Bool)
    (a : PureNativeSession.Allocation) (prof : Fin 4) (vp : Fin 8)
    (sec prf seed msg ctx supplied : Bytes)
    (sizes : sec.length = (params s).n ∧ prf.length = (params s).n ∧ seed.length = (params s).n)
    (rnd : m ≠ .deterministic → supplied.length = (params s).n)
    (valid : ctx.length ≤ 255) (fits : 2 + ctx.length + msg.length < 2^63) :
    let p := params s
    let keys := slhKeygenInternal p sec prf seed
    run s m useAlias a prof vp (referenceOuter s) sec prf seed msg ctx supplied =
      some (keys,slhSign p msg ctx keys.1 (PureNativeSession.randomness m p keys.1 supplied),true) :=
  run_eq s m useAlias a prof vp (referenceOuter s) sec prf seed msg ctx supplied sizes rnd valid fits

#print axioms public_run_eq
run_cmd
  for ax in (← Lean.collectAxioms ``public_run_eq) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Public SHA-2 session proof depends on unexpected axiom {ax}"
end LinkedArm.Sha2PureNativeSession
