import Facade.Suite
import Spec.AppleEndToEnd

/-! A source-level witness for the complete session. All three output buffers come
    from executing the extracted Rust adapters, including deterministic dispatch.
    The only input-size restriction on the message is the adapters' arithmetic bound. -/
open Aeneas Aeneas.Std Result
namespace slhdsa.Suite
open LinkedArm.Signer

theorem extracted_session (family : Spec.HashFamily) {N : Usize} (p : params.Params) (hp : PN p N)
    (set : view family p ∈ parameterSets ∨ view family p ∈ sha2ParameterSets)
    (secret prf seed skBuf pkBuf message context random sigBuf : Slice U8) (hasRandom : Bool)
    (hs : secret.length = N.val) (hf : prf.length = N.val) (hd : seed.length = N.val)
    (hsk : skBuf.length = 4 * N.val) (hpk : pkBuf.length = 2 * N.val)
    (hbuf : sigBuf.length = (paramsS p).sigBytes)
    (hr : hasRandom = true → random.length = N.val)
    (room : Room message.length (msgSlack N.val + 257)) (valid : context.length ≤ 255) :
    ∃ sk pk sig,
      keygen_seeds family N p secret prf seed skBuf pkBuf = ok (sk, pk) ∧
      sign_into family N p message context sk hasRandom random sigBuf = ok (true, sig) ∧
      verify family N p message sig context pk = ok true ∧
      Session (view family p) (bytes secret.val) (bytes prf.val) (bytes seed.val)
        (bytes message.val) (bytes context.val) (bytes random.val) (!hasRandom)
        (bytes sk.val) (bytes pk.val) (bytes sig.val) true := by
  let P := view family p
  have vn : P.n = N.val := hp.n
  have lens : (bytes secret.val).length = P.n ∧ (bytes prf.val).length = P.n ∧
      (bytes seed.val).length = P.n := by simpa [vn, Slice.length] using And.intro hs (And.intro hf hd)
  have ctx : (bytes context.val).length ≤ 255 := by simpa [Slice.length] using valid
  have cx : context.val.length ≤ 255 := valid
  obtain ⟨⟨sk, pk⟩, kg, keys⟩ := spec_imp_exists
    (adapter_keygen_seeds_spec family p hp secret prf seed skBuf pkBuf hs hf hd hsk hpk)
  have sizes := congrArg (fun (x : Spec.Bytes × Spec.Bytes) => (x.1.length, x.2.length)) keys
  change ((bytes sk.val).length, (bytes pk.val).length) =
    ((Spec.slhKeygenInternal P _ _ _).1.length, (Spec.slhKeygenInternal P _ _ _).2.length) at sizes
  simp only [Spec.slhKeygenInternal, List.length_append, Spec.xmssNode_length P (Suite.valid family hp),
    lens.1, lens.2.1, lens.2.2, bytes_length, Prod.mk.injEq, vn] at sizes
  have skLen : sk.length = 4 * N.val := by change sk.val.length = _; omega
  have pkLen : pk.length = 2 * N.val := by change pk.val.length = _; omega
  obtain ⟨⟨success, sig⟩, sg, sigSpec⟩ := spec_imp_exists
    (adapter_sign_into_spec family p hp message context sk hasRandom random sigBuf skLen hbuf hr room)
  have hsuc : success = true := sigSpec.1.mpr valid
  subst success
  have signed := sigSpec.2.1 rfl
  obtain ⟨verdict, vf, verified⟩ := spec_imp_exists
    (api_verify_spec family p hp message sig context pk pkLen room)
  have correct := Spec.keygen_keyOk P (Suite.valid family hp) _ _ _ lens.1 lens.2.1 lens.2.2
  rw [← keys] at correct
  have accepted := Spec.slh_complete_internal P (Suite.valid family hp) (Spec.withContext (bytes message.val)
    (bytes context.val)) (bytes sk.val) (randS (paramsS p) (bytes sk.val) hasRandom random) correct.1
  have sigEq : Spec.slhSignInternal P (Spec.withContext (bytes message.val) (bytes context.val))
    (bytes sk.val) (randS (paramsS p) (bytes sk.val) hasRandom random) = bytes sig.val := by
    simpa [Spec.slhSign, cx, show ¬context.val.length > 255 by omega] using signed
  rw [sigEq, ← correct.2] at accepted
  have fv : Spec.slhVerify P (bytes message.val) (bytes sig.val) (bytes context.val) (bytes pk.val) = true := by
    simpa [Spec.slhVerify, cx, show ¬context.val.length > 255 by omega] using accepted
  have res := verified.trans fv
  rw [res] at vf
  refine ⟨sk, pk, sig, kg, sg, vf, (session_iff set lens ctx).mpr ⟨keys, ?_, fv.symm, rfl⟩⟩
  cases hasRandom <;> simpa [randS, Spec.block, view] using signed.symm

/-- Verify any submitted bytes, including signatures with incorrect lengths.
    For a valid context the actual return is equivalent to the structured trace
    verdict. For an oversized context the call returns false. -/
theorem extracted_verdict_iff (family : Spec.HashFamily) {N : Usize} (p : params.Params)
    (hp : PN p N) (message sig ctx pk : Slice U8) (answer : Bool)
    (hpk : pk.length = 2 * N.val) (room : Room message.length (msgSlack N.val + 257)) :
    verify family N p message sig ctx pk = ok answer ↔
      (if ctx.length > 255 then answer = false else
        Nonempty (VerifyTrace (view family p) (Spec.withContext (bytes message.val) (bytes ctx.val))
          (bytes sig.val) (bytes pk.val) answer)) := by
  obtain ⟨v, run, hv⟩ := spec_imp_exists (api_verify_spec family p hp message sig ctx pk hpk room)
  rw [run, hv]
  have ctxLength : (bytes ctx.val).length = ctx.length := bytes_length _
  by_cases h : ctx.length > 255
  · simp [h, Spec.slhVerify, ctxLength, eq_comm]
  · simp only [h, ↓reduceIte, verification_trace_iff, Spec.slhVerify, ctxLength]
    simp [eq_comm]

/-- The signer returns the original destination when the context is oversized. -/
theorem extracted_rejects_context (family : Spec.HashFamily) {N : Usize} (p : params.Params)
    (hp : PN p N) (message ctx sk random dest : Slice U8) (hasRandom : Bool)
    (hsk : sk.length = 4 * N.val) (hbuf : dest.length = (paramsS p).sigBytes)
    (hr : hasRandom = true → random.length = N.val)
    (room : Room message.length (msgSlack N.val + 257)) (oversized : 255 < ctx.length) :
    sign_into family N p message ctx sk hasRandom random dest = ok (false, dest) := by
  obtain ⟨⟨b, out⟩, run, post⟩ := spec_imp_exists
    (adapter_sign_into_spec family p hp message ctx sk hasRandom random dest hsk hbuf hr room)
  cases b with
  | true => exact False.elim (Nat.not_le.mpr oversized (post.1.mp rfl))
  | false => exact (post.2.2 rfl) ▸ run

#print axioms extracted_verdict_iff
#print axioms extracted_rejects_context
#print axioms extracted_session
end slhdsa.Suite
