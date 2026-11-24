import Spec.AppleSha2NativeSession

namespace LinkedArm.NativeSession
open Spec ArmVerifyLength

structure VerificationEntry (p : Params) where
  driver : Entries p
  lengthPath : Path
  next : Nat
  gate : inspect lengthPath = some ⟨p.sigBytes, next, false⟩

/-- Verify a caller-supplied signature. Its size selects the actual measured
    rejection edge or the checked body; its contents are entirely arbitrary. -/
def arbitraryVerdict {p} (entry : VerificationEntry p) (msg sig pk : Bytes) : Option Bool := do
  match ← execute entry.lengthPath sig.length with
  | .returned value => return value
  | .continued pc =>
    guard (pc == entry.next)
    if h : sig.length = p.sigBytes ∧ pk.length = 2*p.n then
      let events ← entry.driver.verifyRun
      let calls := referenceVerifier entry.driver.valid msg sig pk h.1 h.2
      return ArmVerifyBody.returned calls events
    else none

theorem arbitraryVerdict_eq {p} (entry : VerificationEntry p) (msg sig pk : Bytes)
    (fits : sig.length < 2^64) (keySize : pk.length = 2*p.n) :
    arbitraryVerdict entry msg sig pk = some (slhVerifyInternal p msg sig pk) := by
  by_cases valid : sig.length = p.sigBytes
  · have edge := acceptedEdge entry.gate (valid ▸ fits)
    have e : execute entry.lengthPath sig.length = some (.continued entry.next) := valid ▸ edge
    have ok := And.intro valid keySize
    let calls := referenceVerifier entry.driver.valid msg sig pk valid keySize
    have equal := (entry.driver.verifyTrace entry.driver.verifyChecked calls).eq_spec
    simpa [arbitraryVerdict, e, edge, ok, entry.driver.verifyChecked, calls] using
      congrArg some equal
  · have edge := rejects entry.gate sig fits valid
    have falseResult := (toVerifyTrace entry.gate msg sig pk false edge).eq_spec
    simpa [arbitraryVerdict, edge] using congrArg some falseResult

def shake_128s_verifier : VerificationEntry Spec.shake_128s :=
  ⟨shake_128s_entries, LinkedAppleVerifyLength.shake_128s_path, _, LinkedAppleVerifyLength.shake_128s_checked⟩

def shake_128f_verifier : VerificationEntry Spec.shake_128f :=
  ⟨shake_128f_entries, LinkedAppleVerifyLength.shake_128f_path, _, LinkedAppleVerifyLength.shake_128f_checked⟩

def shake_192s_verifier : VerificationEntry Spec.shake_192s :=
  ⟨shake_192s_entries, LinkedAppleVerifyLength.shake_192s_path, _, LinkedAppleVerifyLength.shake_192s_checked⟩

def shake_192f_verifier : VerificationEntry Spec.shake_192f :=
  ⟨shake_192f_entries, LinkedAppleVerifyLength.shake_192f_path, _, LinkedAppleVerifyLength.shake_192f_checked⟩

def shake_256s_verifier : VerificationEntry Spec.shake_256s :=
  ⟨shake_256s_entries, LinkedAppleVerifyLength.shake_256s_path, _, LinkedAppleVerifyLength.shake_256s_checked⟩

def shake_256f_verifier : VerificationEntry Spec.shake_256f :=
  ⟨shake_256f_entries, LinkedAppleVerifyLength.shake_256f_path, _, LinkedAppleVerifyLength.shake_256f_checked⟩

def sha2_128s_verifier : VerificationEntry Spec.sha2_128s :=
  ⟨sha2_128s_entries, LinkedAppleSha2VerifyLength.sha2_128s_path, _, LinkedAppleSha2VerifyLength.sha2_128s_guard⟩

def sha2_128f_verifier : VerificationEntry Spec.sha2_128f :=
  ⟨sha2_128f_entries, LinkedAppleSha2VerifyLength.sha2_128f_path, _, LinkedAppleSha2VerifyLength.sha2_128f_guard⟩

def sha2_192s_verifier : VerificationEntry Spec.sha2_192s :=
  ⟨sha2_192s_entries, LinkedAppleSha2VerifyLength.sha2_192s_path, _, LinkedAppleSha2VerifyLength.sha2_192s_guard⟩

def sha2_192f_verifier : VerificationEntry Spec.sha2_192f :=
  ⟨sha2_192f_entries, LinkedAppleSha2VerifyLength.sha2_192f_path, _, LinkedAppleSha2VerifyLength.sha2_192f_guard⟩

def sha2_256s_verifier : VerificationEntry Spec.sha2_256s :=
  ⟨sha2_256s_entries, LinkedAppleSha2VerifyLength.sha2_256s_path, _, LinkedAppleSha2VerifyLength.sha2_256s_guard⟩

def sha2_256f_verifier : VerificationEntry Spec.sha2_256f :=
  ⟨sha2_256f_entries, LinkedAppleSha2VerifyLength.sha2_256f_path, _, LinkedAppleSha2VerifyLength.sha2_256f_guard⟩

run_cmd
  for decl in [``arbitraryVerdict_eq,
      ``shake_128s_verifier, ``shake_128f_verifier,
      ``shake_192s_verifier, ``shake_192f_verifier,
      ``shake_256s_verifier, ``shake_256f_verifier,
      ``sha2_128s_verifier, ``sha2_128f_verifier,
      ``sha2_192s_verifier, ``sha2_192f_verifier,
      ``sha2_256s_verifier, ``sha2_256f_verifier] do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} depends on unexpected axiom {ax}"

#print axioms arbitraryVerdict_eq
end LinkedArm.NativeSession
