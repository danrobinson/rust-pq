import Facade.PublicSession
import Spec.AppleNativeVerdict

/-! Composition across the Rust extraction and the measured native driver model.
    The native side receives precisely the seeds, framed message and randomness
    used by the public Rust call; all output buffers below are actual results. -/
open Aeneas Aeneas.Std Result
open LinkedArm.Signer LinkedArm.NativeSession
namespace slhdsa.Suite

def PublicNativeSession {S K V N : Usize} (p : Spec.Params) (slack : Nat) (e : Entries p)
    (kg : Array U8 S → Array U8 K → Array U8 V → Result (Array U8 K × Array U8 V))
    (sign : Slice U8 → Slice U8 → Array U8 K → Array U8 N → Result (Option (alloc.vec.Vec U8)))
    (det : Slice U8 → Slice U8 → Array U8 K → Result (Option (alloc.vec.Vec U8)))
    (check : Slice U8 → Slice U8 → Slice U8 → Array U8 V → Result Bool) : Prop :=
  ∀ (profile : Fin 4)
    (seeds : Array U8 S) (skBuf : Array U8 K) (pkBuf : Array U8 V)
    (m ctx : Slice U8) (random : Array U8 N) (mode : Bool)
    (_ : Room m.length slack) (_ : ctx.length ≤ 255),
    let part := Spec.block p (bytes seeds.val)
    ∃ sk pk sig, kg seeds skBuf pkBuf = ok (sk,pk) ∧
      (if mode then det m ctx sk else sign m ctx sk random) = ok (some sig) ∧
      check m sig.deref ctx pk = ok true ∧
      runWithReferenceCalls e profile (part 0) (part 1) (part 2)
        (Spec.withContext (bytes m.val) (bytes ctx.val))
        (if mode then Spec.block p (bytes sk.val) 2 else bytes random.val) =
        some ((bytes sk.val, bytes pk.val), bytes sig.val, true)

theorem public_native_agreement {S K V N : Usize} {p : Spec.Params} {slack : Nat}
    {kg sign det check} (rust : @PublicSession S K V N p slack kg sign det check)
    (e : Entries p) (set : p ∈ parameterSets ∨ p ∈ sha2ParameterSets)
    (seedsLength : S.val = 3*p.n) (randomLength : N.val = p.n) :
    PublicNativeSession p slack e kg sign det check := by
  intro profile seeds skBuf pkBuf m ctx random mode room context
  let part := Spec.block p (bytes seeds.val)
  have plen (i : Nat) (hi : i < 3) : (part i).length = p.n := by
    simp [part, Spec.block, seedsLength]
    interval_cases i <;> omega
  have sizes := And.intro (plen 0 (by decide)) (And.intro (plen 1 (by decide)) (plen 2 (by decide)))
  obtain ⟨sk, pk, sig, kgRun, signRun, verified, session⟩ :=
    rust seeds skBuf pkBuf m ctx random mode room context
  have valid : (bytes ctx.val).length ≤ 255 := by simpa using context
  obtain ⟨keys, signed, _, _⟩ := (session_iff set sizes valid).mp session
  let rand := if mode then Spec.block p (bytes sk.val) 2 else bytes random.val
  have skLength : (bytes sk.val).length = 4*p.n := by
    have h := congrArg (fun (ks : Spec.Bytes × Spec.Bytes) => ks.1.length) keys
    simp only [Spec.slhKeygenInternal, List.length_append, Spec.xmssNode_length p e.valid] at h
    change (bytes sk.val).length = ((part 0).length + (part 1).length + (part 2).length + p.n) at h
    omega
  have rn : rand.length = p.n := by
    cases mode <;> simp [rand, Spec.block, skLength, randomLength]
    omega
  have exactSig : bytes sig.val = Spec.slhSignInternal p
      (Spec.withContext (bytes m.val) (bytes ctx.val)) (bytes sk.val) rand := by
    simpa only [Spec.slhSign, ite_eq_right (show ¬ (bytes ctx.val).length > 255 by omega),
      Option.some.injEq, rand] using signed
  refine ⟨sk,pk,sig,kgRun,signRun,verified,?_⟩
  rw [run_eq e profile _ _ _ _ _ ⟨sizes.1,sizes.2.1,sizes.2.2,rn⟩, ← keys, exactSig]

theorem shake_128s_native_agreement : PublicNativeSession Spec.shake_128s 409 shake_128s_entries
    sets.shake_128s.keygen sets.shake_128s.sign sets.shake_128s.sign_deterministic sets.shake_128s.verify :=
  public_native_agreement shake_128s_session shake_128s_entries
    (by left; decide) (by decide) (by decide)

theorem shake_128f_native_agreement : PublicNativeSession Spec.shake_128f 409 shake_128f_entries
    sets.shake_128f.keygen sets.shake_128f.sign sets.shake_128f.sign_deterministic sets.shake_128f.verify :=
  public_native_agreement shake_128f_session shake_128f_entries
    (by left; decide) (by decide) (by decide)

theorem shake_192s_native_agreement : PublicNativeSession Spec.shake_192s 561 shake_192s_entries
    sets.shake_192s.keygen sets.shake_192s.sign sets.shake_192s.sign_deterministic sets.shake_192s.verify :=
  public_native_agreement shake_192s_session shake_192s_entries
    (by left; decide) (by decide) (by decide)

theorem shake_192f_native_agreement : PublicNativeSession Spec.shake_192f 561 shake_192f_entries
    sets.shake_192f.keygen sets.shake_192f.sign sets.shake_192f.sign_deterministic sets.shake_192f.verify :=
  public_native_agreement shake_192f_session shake_192f_entries
    (by left; decide) (by decide) (by decide)

theorem shake_256s_native_agreement : PublicNativeSession Spec.shake_256s 561 shake_256s_entries
    sets.shake_256s.keygen sets.shake_256s.sign sets.shake_256s.sign_deterministic sets.shake_256s.verify :=
  public_native_agreement shake_256s_session shake_256s_entries
    (by left; decide) (by decide) (by decide)

theorem shake_256f_native_agreement : PublicNativeSession Spec.shake_256f 561 shake_256f_entries
    sets.shake_256f.keygen sets.shake_256f.sign sets.shake_256f.sign_deterministic sets.shake_256f.verify :=
  public_native_agreement shake_256f_session shake_256f_entries
    (by left; decide) (by decide) (by decide)

theorem sha2_128s_native_agreement : PublicNativeSession Spec.sha2_128s 409 sha2_128s_entries
    sets.sha2_128s.keygen sets.sha2_128s.sign sets.sha2_128s.sign_deterministic sets.sha2_128s.verify :=
  public_native_agreement sha2_128s_session sha2_128s_entries
    (by right; decide) (by decide) (by decide)

theorem sha2_128f_native_agreement : PublicNativeSession Spec.sha2_128f 409 sha2_128f_entries
    sets.sha2_128f.keygen sets.sha2_128f.sign sets.sha2_128f.sign_deterministic sets.sha2_128f.verify :=
  public_native_agreement sha2_128f_session sha2_128f_entries
    (by right; decide) (by decide) (by decide)

theorem sha2_192s_native_agreement : PublicNativeSession Spec.sha2_192s 561 sha2_192s_entries
    sets.sha2_192s.keygen sets.sha2_192s.sign sets.sha2_192s.sign_deterministic sets.sha2_192s.verify :=
  public_native_agreement sha2_192s_session sha2_192s_entries
    (by right; decide) (by decide) (by decide)

theorem sha2_192f_native_agreement : PublicNativeSession Spec.sha2_192f 561 sha2_192f_entries
    sets.sha2_192f.keygen sets.sha2_192f.sign sets.sha2_192f.sign_deterministic sets.sha2_192f.verify :=
  public_native_agreement sha2_192f_session sha2_192f_entries
    (by right; decide) (by decide) (by decide)

theorem sha2_256s_native_agreement : PublicNativeSession Spec.sha2_256s 561 sha2_256s_entries
    sets.sha2_256s.keygen sets.sha2_256s.sign sets.sha2_256s.sign_deterministic sets.sha2_256s.verify :=
  public_native_agreement sha2_256s_session sha2_256s_entries
    (by right; decide) (by decide) (by decide)

theorem sha2_256f_native_agreement : PublicNativeSession Spec.sha2_256f 561 sha2_256f_entries
    sets.sha2_256f.keygen sets.sha2_256f.sign sets.sha2_256f.sign_deterministic sets.sha2_256f.verify :=
  public_native_agreement sha2_256f_session sha2_256f_entries
    (by right; decide) (by decide) (by decide)

/-- The caller can supply any signature, including one with a wrong length.
    On a valid context the extracted verifier and measured internal verifier
    return the same Boolean for the framed message and supplied public key. -/
theorem submitted_signature_agreement (family : Spec.HashFamily) {N : Usize} (p : params.Params)
    (hp : PN p N) (entry : VerificationEntry (view family p)) (m sig ctx pk : Slice U8)
    (keySize : pk.length = 2*N.val) (room : Room m.length (msgSlack N.val + 257))
    (valid : ctx.length ≤ 255) (fits : (bytes sig.val).length < 2^64) :
    ∃ v, verify family N p m sig ctx pk = ok v ∧
      arbitraryVerdict entry (Spec.withContext (bytes m.val) (bytes ctx.val)) (bytes sig.val) (bytes pk.val) = some v := by
  obtain ⟨v, run, value⟩ := spec_imp_exists (api_verify_spec family p hp m sig ctx pk keySize room)
  have width : (view family p).n = N.val := hp.n
  have k : (bytes pk.val).length = 2*(view family p).n := by simpa [width] using keySize
  have vctx : (bytes ctx.val).length ≤ 255 := by simpa using valid
  refine ⟨v, run, ?_⟩
  rw [arbitraryVerdict_eq entry _ _ _ fits k, value]
  simp only [Spec.slhVerify, ite_eq_right (show ¬(bytes ctx.val).length > 255 by omega)]

run_cmd
  for decl in [``public_native_agreement, ``submitted_signature_agreement,
      ``shake_128s_native_agreement, ``shake_128f_native_agreement,
      ``shake_192s_native_agreement, ``shake_192f_native_agreement,
      ``shake_256s_native_agreement, ``shake_256f_native_agreement,
      ``sha2_128s_native_agreement, ``sha2_128f_native_agreement,
      ``sha2_192s_native_agreement, ``sha2_192f_native_agreement,
      ``sha2_256s_native_agreement, ``sha2_256f_native_agreement] do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} depends on unexpected axiom {ax}"
#print axioms public_native_agreement
end slhdsa.Suite
