import Lean.Util.CollectAxioms
import Spec.AppleKeygenWitness
import Spec.AppleInternalSignerWitness
import Spec.AppleVerifyBodyWitness
import Spec.ArmReferenceCalls

/-! Composition over one linked Apple executable. The keys read from the
    keygen return regions feed the signer and verifier. The verifier's signature
    is the serialized signer result. Only the individual native callee contracts
    and the interpreters' successful-runtime models are assumed. -/
namespace LinkedArm.NativeSession
open Spec LinkedArm.Signer
/-- The two signing families have different hash and FORS ABIs. Their native
    trace constructors prove equality of the bytes selected for return. -/
structure SigningModel (p : Params) where
  Calls : Bytes → Bytes → Bytes → Type
  result : ∀ {msg key rand}, Calls msg key rand → ArmInternalSigner.Observation → Bytes
  reference : ∀ msg key rand, key.length = 4*p.n → rand.length = p.n → Calls msg key rand
  expected : ArmInternalSigner.Observation

def shakeModel {p} (row : p ∈ parameterSets) : SigningModel p where
  Calls := ArmInternalSigner.Callees p
  result := ArmInternalSigner.materialize
  reference := referenceSigner row
  expected := ArmInternalSigner.expected

def sha2Model {p} (row : p ∈ sha2Sets) : SigningModel p where
  Calls := ArmInternalSigner.Sha2.Callees p
  result := ArmInternalSigner.Sha2.materialize
  reference := referenceSha2Signer row
  expected := ArmInternalSigner.Sha2.expected

structure Entries (p : Params) where
  kg : ArmKeygen.Config
  path : List (Nat × Nat)
  model : SigningModel p
  signing : ArmInternalSigner.Image
  verifyRun : Option (List ArmVerifyBody.Action)
  verifyEvents : List ArmVerifyBody.Action
  keyChecked : ArmKeygen.run kg path = some (ArmKeygen.secret p.n, ArmKeygen.publicKey p.n)
  signChecked : ∀ profile : Fin 4, ArmInternalSigner.run signing profile = some model.expected
  verifyChecked : verifyRun = some verifyEvents
  keyWidth : p.n % 4 = 0 ∧ p.n ≤ 32
  valid : p.Valid
  signEq : ∀ {msg key rand out} (profile : Fin 4), ArmInternalSigner.run signing profile = some out →
    (s : model.Calls msg key rand) → model.result s out = slhSignInternal p msg key rand
  verifyTrace : ∀ {msg sig key events}, verifyRun = some events →
    (v : ArmVerifyBody.Callees p msg sig key) → VerifyTrace p msg sig key (ArmVerifyBody.returned v events)

def readKey (sources : Nat → Bytes) (cells : ArmKeygen.Cells) := ArmKeygen.bytes (ArmKeygen.interpret sources) cells

/-- Termination of the restricted top-level interpreters on each of the four
    successful allocation profiles. Each call site uses its stated contract. -/
theorem returns {p} (e : Entries p) (profile : Fin 4) :
    ∃ keys signed verified, ArmKeygen.run e.kg e.path = some keys ∧
      ArmInternalSigner.run e.signing profile = some signed ∧ e.verifyRun = some verified :=
  ⟨_, _, _, e.keyChecked, e.signChecked profile, e.verifyChecked⟩

theorem internal {p} (e : Entries p) (profile : Fin 4)
    {keys signed verified} (kg : ArmKeygen.run e.kg e.path = some keys)
    (sg : ArmInternalSigner.run e.signing profile = some signed) (vr : e.verifyRun = some verified)
    (sources : Nat → Bytes) (sizes : ∀ i < 4, (sources i).length = p.n)
    (subtree : Node p (sources 0) (sources 2) {Adrs.zero with layer := p.d-1} 0 p.hp (sources 3))
    {msg rand} (s : e.model.Calls msg (readKey sources keys.1) rand)
    (v : ArmVerifyBody.Callees p msg (e.model.result s signed) (readKey sources keys.2)) :
    (readKey sources keys.1, readKey sources keys.2) = slhKeygenInternal p (sources 0) (sources 1) (sources 2) ∧
    e.model.result s signed = slhSignInternal p msg (readKey sources keys.1) rand ∧
    ArmVerifyBody.returned v verified = slhVerifyInternal p msg (e.model.result s signed) (readKey sources keys.2) ∧
    ArmVerifyBody.returned v verified = true := by
  have key := ArmKeygen.concreteKeyGeneration kg e.keyChecked sources sizes e.keyWidth.1 e.keyWidth.2 subtree
  have sign := e.signEq profile sg s
  have verify := (e.verifyTrace vr v).eq_spec
  have wellFormed := keygen_keyOk p e.valid _ _ _ (sizes 0 (by decide)) (sizes 1 (by decide)) (sizes 2 (by decide))
  rw [← key.eq_spec] at wellFormed
  have accept := slh_complete_internal p e.valid msg (readKey sources keys.1) rand wellFormed.1
  have pk : readKey sources keys.2 = skPk p (readKey sources keys.1) := wellFormed.2
  rw [← sign, ← pk, ← verify] at accept
  exact ⟨key.eq_spec, sign, verify, accept⟩

def keySources (p : Params) (secret prf seed : Bytes) : Nat → Bytes
  | 0 => secret
  | 1 => prf
  | 2 => seed
  | _ => xmssNode p secret 0 p.hp seed {Adrs.zero with layer := p.d-1}

/-- Execute the three measured control-flow interpreters using the reference
    implementation at each cryptographic call. The only externally supplied
    values are seeds, message, randomness and successful allocation profile. -/
def runWithReferenceCalls {p : Params} (e : Entries p) (profile : Fin 4)
    (secret prf seed msg rand : Bytes) : Option ((Bytes × Bytes) × Bytes × Bool) := do
  let keys ← ArmKeygen.run e.kg e.path
  let sources := keySources p secret prf seed
  let sk := readKey sources keys.1
  let pk := readKey sources keys.2
  if h : sk.length = 4*p.n ∧ pk.length = 2*p.n ∧ rand.length = p.n then
    let obs ← ArmInternalSigner.run e.signing profile
    let s := e.model.reference msg sk rand h.1 h.2.2
    let sig := e.model.result s obs
    if hs : sig.length = p.sigBytes then
      let events ← e.verifyRun
      let v := referenceVerifier e.valid msg sig pk hs h.2.1
      return ((sk,pk),sig,ArmVerifyBody.returned v events)
    else none
  else none

/-- Every correctly sized input yields the FIPS key pair, the FIPS signature
    bytes, and acceptance in the measured driver model with reference callees. -/
theorem run_eq {p} (e : Entries p) (profile : Fin 4) (secret prf seed msg rand : Bytes)
    (sizes : secret.length = p.n ∧ prf.length = p.n ∧ seed.length = p.n ∧ rand.length = p.n) :
    let keys := slhKeygenInternal p secret prf seed
    runWithReferenceCalls e profile secret prf seed msg rand =
      some (keys, slhSignInternal p msg keys.1 rand, true) := by
  have valid := e.valid
  let sources := keySources p secret prf seed
  have sized (i : Nat) (hi : i < 4) : (sources i).length = p.n := by
    interval_cases i
    · exact sizes.1
    · exact sizes.2.1
    · exact sizes.2.2.1
    · exact xmssNode_length p valid _ _ _ _ _
  let sk := readKey sources (ArmKeygen.secret p.n)
  let pk := readKey sources (ArmKeygen.publicKey p.n)
  have tree : Node p (sources 0) (sources 2) {Adrs.zero with layer := p.d-1} 0 p.hp (sources 3) :=
    referenceNode _ _ _ _ _ _
  have key : (sk,pk) = slhKeygenInternal p secret prf seed :=
    (ArmKeygen.concreteKeyGeneration e.keyChecked e.keyChecked sources sized
      e.keyWidth.1 e.keyWidth.2 tree).eq_spec
  have len := congrArg (fun (x : Bytes × Bytes) => (x.1.length,x.2.length)) key
  simp only [slhKeygenInternal, List.length_append, xmssNode_length p valid, sizes.1,
    sizes.2.1, sizes.2.2.1, Prod.mk.injEq] at len
  have h : sk.length = 4*p.n ∧ pk.length = 2*p.n ∧ rand.length = p.n := by
    exact ⟨by omega,by omega,sizes.2.2.2⟩
  let calls := e.model.reference msg sk rand h.1 h.2.2
  let sig := e.model.result calls e.model.expected
  have hs : sig = slhSignInternal p msg sk rand :=
    e.signEq profile (e.signChecked profile) calls
  have sigLen : sig.length = p.sigBytes := hs ▸ slhSignInternal_length p valid _ _ _
  let ver := referenceVerifier e.valid msg sig pk sigLen h.2.1
  have result := internal e profile e.keyChecked (e.signChecked profile) e.verifyChecked sources sized tree calls ver
  unfold runWithReferenceCalls
  simp only [e.keyChecked, e.signChecked, e.verifyChecked]
  change (if h' : sk.length = 4*p.n ∧ pk.length = 2*p.n ∧ rand.length = p.n then _ else _) = _
  rw [dite_eq_left h]
  change (if hs' : sig.length = p.sigBytes then _ else _) = _
  rw [dite_eq_left sigLen]
  change some ((sk,pk),sig,ArmVerifyBody.returned ver e.verifyEvents) = _
  rw [result.2.2.2,hs,← key]

def shake_128s_entries : Entries Spec.shake_128s where
  kg := LinkedAppleKeygen.shake_128s_keygen_config
  path := LinkedAppleKeygen.shake_128s_keygen_path
  signing := LinkedInternalSigner.shake_128s
  model := shakeModel (by decide)
  verifyRun := ArmVerifyBody.run LinkedAppleVerifyBody.shake_128s_image
  verifyEvents := ArmVerifyBody.expected Spec.shake_128s
  keyChecked := LinkedAppleKeygen.shake_128s_keygen_checked
  signChecked := LinkedInternalSigner.shake_128s_checked
  verifyChecked := LinkedAppleVerifyBody.shake_128s_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedInternalSigner.shake_128s_eq
  verifyTrace := LinkedAppleVerifyBody.shake_128s_trace

def shake_128s_internal_keygen : Entries Spec.shake_128s :=
  { shake_128s_entries with
    kg := LinkedAppleKeygen.shake_128s_slh_keygen_internal_config
    path := LinkedAppleKeygen.shake_128s_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.shake_128s_slh_keygen_internal_checked }

def shake_128f_entries : Entries Spec.shake_128f where
  kg := LinkedAppleKeygen.shake_128f_keygen_config
  path := LinkedAppleKeygen.shake_128f_keygen_path
  signing := LinkedInternalSigner.shake_128f
  model := shakeModel (by decide)
  verifyRun := ArmVerifyBody.run LinkedAppleVerifyBody.shake_128f_image
  verifyEvents := ArmVerifyBody.expected Spec.shake_128f
  keyChecked := LinkedAppleKeygen.shake_128f_keygen_checked
  signChecked := LinkedInternalSigner.shake_128f_checked
  verifyChecked := LinkedAppleVerifyBody.shake_128f_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedInternalSigner.shake_128f_eq
  verifyTrace := LinkedAppleVerifyBody.shake_128f_trace

def shake_128f_internal_keygen : Entries Spec.shake_128f :=
  { shake_128f_entries with
    kg := LinkedAppleKeygen.shake_128f_slh_keygen_internal_config
    path := LinkedAppleKeygen.shake_128f_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.shake_128f_slh_keygen_internal_checked }

def shake_192s_entries : Entries Spec.shake_192s where
  kg := LinkedAppleKeygen.shake_192s_keygen_config
  path := LinkedAppleKeygen.shake_192s_keygen_path
  signing := LinkedInternalSigner.shake_192s
  model := shakeModel (by decide)
  verifyRun := ArmVerifyBody.run LinkedAppleVerifyBody.shake_192s_image
  verifyEvents := ArmVerifyBody.expected Spec.shake_192s
  keyChecked := LinkedAppleKeygen.shake_192s_keygen_checked
  signChecked := LinkedInternalSigner.shake_192s_checked
  verifyChecked := LinkedAppleVerifyBody.shake_192s_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedInternalSigner.shake_192s_eq
  verifyTrace := LinkedAppleVerifyBody.shake_192s_trace

def shake_192s_internal_keygen : Entries Spec.shake_192s :=
  { shake_192s_entries with
    kg := LinkedAppleKeygen.shake_192s_slh_keygen_internal_config
    path := LinkedAppleKeygen.shake_192s_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.shake_192s_slh_keygen_internal_checked }

def shake_192f_entries : Entries Spec.shake_192f where
  kg := LinkedAppleKeygen.shake_192f_keygen_config
  path := LinkedAppleKeygen.shake_192f_keygen_path
  signing := LinkedInternalSigner.shake_192f
  model := shakeModel (by decide)
  verifyRun := ArmVerifyBody.run LinkedAppleVerifyBody.shake_192f_image
  verifyEvents := ArmVerifyBody.expected Spec.shake_192f
  keyChecked := LinkedAppleKeygen.shake_192f_keygen_checked
  signChecked := LinkedInternalSigner.shake_192f_checked
  verifyChecked := LinkedAppleVerifyBody.shake_192f_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedInternalSigner.shake_192f_eq
  verifyTrace := LinkedAppleVerifyBody.shake_192f_trace

def shake_192f_internal_keygen : Entries Spec.shake_192f :=
  { shake_192f_entries with
    kg := LinkedAppleKeygen.shake_192f_slh_keygen_internal_config
    path := LinkedAppleKeygen.shake_192f_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.shake_192f_slh_keygen_internal_checked }

def shake_256s_entries : Entries Spec.shake_256s where
  kg := LinkedAppleKeygen.shake_256s_keygen_config
  path := LinkedAppleKeygen.shake_256s_keygen_path
  signing := LinkedInternalSigner.shake_256s
  model := shakeModel (by decide)
  verifyRun := ArmVerifyBody.run LinkedAppleVerifyBody.shake_256s_image
  verifyEvents := ArmVerifyBody.expected Spec.shake_256s
  keyChecked := LinkedAppleKeygen.shake_256s_keygen_checked
  signChecked := LinkedInternalSigner.shake_256s_checked
  verifyChecked := LinkedAppleVerifyBody.shake_256s_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedInternalSigner.shake_256s_eq
  verifyTrace := LinkedAppleVerifyBody.shake_256s_trace

def shake_256s_internal_keygen : Entries Spec.shake_256s :=
  { shake_256s_entries with
    kg := LinkedAppleKeygen.shake_256s_slh_keygen_internal_config
    path := LinkedAppleKeygen.shake_256s_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.shake_256s_slh_keygen_internal_checked }

def shake_256f_entries : Entries Spec.shake_256f where
  kg := LinkedAppleKeygen.shake_256f_keygen_config
  path := LinkedAppleKeygen.shake_256f_keygen_path
  signing := LinkedInternalSigner.shake_256f
  model := shakeModel (by decide)
  verifyRun := ArmVerifyBody.run LinkedAppleVerifyBody.shake_256f_image
  verifyEvents := ArmVerifyBody.expected Spec.shake_256f
  keyChecked := LinkedAppleKeygen.shake_256f_keygen_checked
  signChecked := LinkedInternalSigner.shake_256f_checked
  verifyChecked := LinkedAppleVerifyBody.shake_256f_checked
  keyWidth := by decide
  valid := by constructor <;> decide
  signEq := LinkedInternalSigner.shake_256f_eq
  verifyTrace := LinkedAppleVerifyBody.shake_256f_trace

def shake_256f_internal_keygen : Entries Spec.shake_256f :=
  { shake_256f_entries with
    kg := LinkedAppleKeygen.shake_256f_slh_keygen_internal_config
    path := LinkedAppleKeygen.shake_256f_slh_keygen_internal_path
    keyChecked := LinkedAppleKeygen.shake_256f_slh_keygen_internal_checked }

#print axioms run_eq
#print axioms internal
#print axioms shake_128s_entries
#print axioms shake_128f_entries
/- Check all instantiated certificates as well as the two composition results. -/
run_cmd
  for decl in [``run_eq, ``internal, ``returns, ``shake_128s_entries, ``shake_128f_entries,
      ``shake_192s_entries, ``shake_192f_entries, ``shake_256s_entries, ``shake_256f_entries,
      ``shake_128s_internal_keygen, ``shake_128f_internal_keygen,
      ``shake_192s_internal_keygen, ``shake_192f_internal_keygen,
      ``shake_256s_internal_keygen, ``shake_256f_internal_keygen] do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} depends on unexpected axiom {ax}"

end LinkedArm.NativeSession
