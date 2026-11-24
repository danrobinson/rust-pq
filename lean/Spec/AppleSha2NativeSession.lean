import Spec.AppleNativeSession
import Spec.AppleSha2InternalSignerWitness
import Spec.AppleSha2VerifyWitness

namespace LinkedArm.NativeSession
open Spec LinkedArm.Signer

def sha2_128s_entries : Entries Spec.sha2_128s where
  kg := LinkedAppleKeygen.sha2_128s_keygen_config
  path := LinkedAppleKeygen.sha2_128s_keygen_path
  signing := LinkedSha2InternalSigner.sha2_128s
  model := sha2Model (by decide)
  verifyRun := ArmSha2Verify.run LinkedAppleSha2VerifyBody.sha2_128s_image
  verifyEvents := ArmSha2Verify.expected Spec.sha2_128s
  keyChecked := LinkedAppleKeygen.sha2_128s_keygen_checked
  signChecked := LinkedSha2InternalSigner.sha2_128s_checked
  verifyChecked := LinkedAppleSha2VerifyBody.sha2_128s_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedSha2InternalSigner.sha2_128s_eq
  verifyTrace := LinkedAppleSha2VerifyBody.sha2_128s_trace

def sha2_128s_internal_keygen : Entries Spec.sha2_128s :=
  { sha2_128s_entries with
    kg := LinkedAppleKeygen.sha2_128s_slh_keygen_internal_config
    path := LinkedAppleKeygen.sha2_128s_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.sha2_128s_slh_keygen_internal_checked }

def sha2_128f_entries : Entries Spec.sha2_128f where
  kg := LinkedAppleKeygen.sha2_128f_keygen_config
  path := LinkedAppleKeygen.sha2_128f_keygen_path
  signing := LinkedSha2InternalSigner.sha2_128f
  model := sha2Model (by decide)
  verifyRun := ArmSha2Verify.run LinkedAppleSha2VerifyBody.sha2_128f_image
  verifyEvents := ArmSha2Verify.expected Spec.sha2_128f
  keyChecked := LinkedAppleKeygen.sha2_128f_keygen_checked
  signChecked := LinkedSha2InternalSigner.sha2_128f_checked
  verifyChecked := LinkedAppleSha2VerifyBody.sha2_128f_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedSha2InternalSigner.sha2_128f_eq
  verifyTrace := LinkedAppleSha2VerifyBody.sha2_128f_trace

def sha2_128f_internal_keygen : Entries Spec.sha2_128f :=
  { sha2_128f_entries with
    kg := LinkedAppleKeygen.sha2_128f_slh_keygen_internal_config
    path := LinkedAppleKeygen.sha2_128f_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.sha2_128f_slh_keygen_internal_checked }

def sha2_192s_entries : Entries Spec.sha2_192s where
  kg := LinkedAppleKeygen.sha2_192s_keygen_config
  path := LinkedAppleKeygen.sha2_192s_keygen_path
  signing := LinkedSha2InternalSigner.sha2_192s
  model := sha2Model (by decide)
  verifyRun := ArmSha2Verify.run LinkedAppleSha2VerifyBody.sha2_192s_image
  verifyEvents := ArmSha2Verify.expected Spec.sha2_192s
  keyChecked := LinkedAppleKeygen.sha2_192s_keygen_checked
  signChecked := LinkedSha2InternalSigner.sha2_192s_checked
  verifyChecked := LinkedAppleSha2VerifyBody.sha2_192s_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedSha2InternalSigner.sha2_192s_eq
  verifyTrace := LinkedAppleSha2VerifyBody.sha2_192s_trace

def sha2_192s_internal_keygen : Entries Spec.sha2_192s :=
  { sha2_192s_entries with
    kg := LinkedAppleKeygen.sha2_192s_slh_keygen_internal_config
    path := LinkedAppleKeygen.sha2_192s_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.sha2_192s_slh_keygen_internal_checked }

def sha2_192f_entries : Entries Spec.sha2_192f where
  kg := LinkedAppleKeygen.sha2_192f_keygen_config
  path := LinkedAppleKeygen.sha2_192f_keygen_path
  signing := LinkedSha2InternalSigner.sha2_192f
  model := sha2Model (by decide)
  verifyRun := ArmSha2Verify.run LinkedAppleSha2VerifyBody.sha2_192f_image
  verifyEvents := ArmSha2Verify.expected Spec.sha2_192f
  keyChecked := LinkedAppleKeygen.sha2_192f_keygen_checked
  signChecked := LinkedSha2InternalSigner.sha2_192f_checked
  verifyChecked := LinkedAppleSha2VerifyBody.sha2_192f_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedSha2InternalSigner.sha2_192f_eq
  verifyTrace := LinkedAppleSha2VerifyBody.sha2_192f_trace

def sha2_192f_internal_keygen : Entries Spec.sha2_192f :=
  { sha2_192f_entries with
    kg := LinkedAppleKeygen.sha2_192f_slh_keygen_internal_config
    path := LinkedAppleKeygen.sha2_192f_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.sha2_192f_slh_keygen_internal_checked }

def sha2_256s_entries : Entries Spec.sha2_256s where
  kg := LinkedAppleKeygen.sha2_256s_keygen_config
  path := LinkedAppleKeygen.sha2_256s_keygen_path
  signing := LinkedSha2InternalSigner.sha2_256s
  model := sha2Model (by decide)
  verifyRun := ArmSha2Verify.run LinkedAppleSha2VerifyBody.sha2_256s_image
  verifyEvents := ArmSha2Verify.expected Spec.sha2_256s
  keyChecked := LinkedAppleKeygen.sha2_256s_keygen_checked
  signChecked := LinkedSha2InternalSigner.sha2_256s_checked
  verifyChecked := LinkedAppleSha2VerifyBody.sha2_256s_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedSha2InternalSigner.sha2_256s_eq
  verifyTrace := LinkedAppleSha2VerifyBody.sha2_256s_trace

def sha2_256s_internal_keygen : Entries Spec.sha2_256s :=
  { sha2_256s_entries with
    kg := LinkedAppleKeygen.sha2_256s_slh_keygen_internal_config
    path := LinkedAppleKeygen.sha2_256s_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.sha2_256s_slh_keygen_internal_checked }

def sha2_256f_entries : Entries Spec.sha2_256f where
  kg := LinkedAppleKeygen.sha2_256f_keygen_config
  path := LinkedAppleKeygen.sha2_256f_keygen_path
  signing := LinkedSha2InternalSigner.sha2_256f
  model := sha2Model (by decide)
  verifyRun := ArmSha2Verify.run LinkedAppleSha2VerifyBody.sha2_256f_image
  verifyEvents := ArmSha2Verify.expected Spec.sha2_256f
  keyChecked := LinkedAppleKeygen.sha2_256f_keygen_checked
  signChecked := LinkedSha2InternalSigner.sha2_256f_checked
  verifyChecked := LinkedAppleSha2VerifyBody.sha2_256f_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedSha2InternalSigner.sha2_256f_eq
  verifyTrace := LinkedAppleSha2VerifyBody.sha2_256f_trace

def sha2_256f_internal_keygen : Entries Spec.sha2_256f :=
  { sha2_256f_entries with
    kg := LinkedAppleKeygen.sha2_256f_slh_keygen_internal_config
    path := LinkedAppleKeygen.sha2_256f_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.sha2_256f_slh_keygen_internal_checked }

run_cmd
  for decl in [``sha2_128s_entries, ``sha2_128f_entries, ``sha2_128s_internal_keygen, ``sha2_128f_internal_keygen,
      ``sha2_192s_entries, ``sha2_192f_entries, ``sha2_192s_internal_keygen, ``sha2_192f_internal_keygen,
      ``sha2_256s_entries, ``sha2_256f_entries, ``sha2_256s_internal_keygen, ``sha2_256f_internal_keygen] do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} depends on unexpected axiom {ax}"

end LinkedArm.NativeSession
