import Spec.AppleSignerComposition
import Spec.Correctness

/-! Composition of the observed key-generation and verification data flow.
The evidence for constructing these traces from native instructions is described
in the artifact report. The relations themselves do not assume the final verdict. -/

namespace LinkedArm.Signer

open Spec

structure KeyGeneration (p : Params) (secret prf seed sk pk : Bytes) where
  root : Bytes
  tree : Node p secret seed { Adrs.zero with layer := p.d - 1 } 0 p.hp root
  secretBytes : sk = secret ++ prf ++ seed ++ root
  publicBytes : pk = seed ++ root

theorem KeyGeneration.eq_spec {p secret prf seed sk pk}
    (v : KeyGeneration p secret prf seed sk pk) :
    (sk, pk) = slhKeygenInternal p secret prf seed := by
  simp only [v.secretBytes, v.publicBytes, v.tree.eq_spec, slhKeygenInternal]

abbrev VerifyState := Bytes × Nat × Nat

structure VerificationLayers (p : Params) (sig seed : Bytes) (initial : VerifyState) where
  states : Nat → VerifyState
  start : states 0 = initial
  recover : ∀ j, j < p.d →
    let st := states j
    LayerRoot p st.1 seed ((sig.drop (j * p.xmssSigBytes)).take p.xmssSigBytes)
      st.2.2 { Adrs.zero with layer := j, tree := st.2.1 } (states (j+1)).1
  coords : ∀ j, j < p.d →
    (states (j+1)).2 = ((states j).2.1 >>> p.hp, (states j).2.1 % 2^p.hp)

theorem VerificationLayers.eq_spec {p sig seed initial}
    (v : VerificationLayers p sig seed initial) (root : Bytes) :
    ((v.states p.d).1 == root) =
      htVerify p initial.1 sig seed initial.2.1 initial.2.2 root := by
  have prefix_eq (k : Nat) (hk : k ≤ p.d) :
      v.states k = (List.range k).foldl (htVerifyLayer p sig seed) initial := by
    induction k with
    | zero => exact v.start
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih (by omega)]
      apply Prod.ext
      · exact (v.recover k (by omega)).eq_spec
      · exact v.coords k (by omega)
  rw [htVerify_eq, prefix_eq p.d (by omega)]

/-- The valid-length case includes arbitrary signature bytes, whether accepted or rejected. -/
structure VerifyBody (p : Params) (msg sig pk : Bytes) (verdict : Bool) where
  digest : Bytes
  digits : List Nat
  forsRoot : Bytes
  digest_eq : digest = Hmsg p (sig.take p.n) (block p pk 0) (block p pk 1) msg
  indices : digits = base2b (digest.take p.mdBytes) p.a p.k
  forest : forsRoot = forsRoots p digits ((sig.drop p.n).take p.forsSigBytes)
    (block p pk 0) (forsAddress p digest)
  layers : VerificationLayers p (sig.drop (p.n + p.forsSigBytes)) (block p pk 0)
    (forsRoot, digestTree p digest, digestLeaf p digest)
  result : verdict = ((layers.states p.d).1 == block p pk 1)

inductive VerifyTrace (p : Params) (msg sig pk : Bytes) : Bool → Type where
  | wrongLength (h : sig.length ≠ p.sigBytes) : VerifyTrace p msg sig pk false
  | checked {verdict} (h : sig.length = p.sigBytes) (body : VerifyBody p msg sig pk verdict) :
    VerifyTrace p msg sig pk verdict

theorem VerifyTrace.eq_spec {p msg sig pk verdict} (v : VerifyTrace p msg sig pk verdict) :
    verdict = slhVerifyInternal p msg sig pk := by
  cases v with
  | wrongLength h => simp [slhVerifyInternal, h]
  | checked h b =>
    have forest : b.forsRoot = forsPkFromSig p ((sig.drop p.n).take p.forsSigBytes)
        (b.digest.take p.mdBytes) (block p pk 0) (forsAddress p b.digest) := by
      rw [b.forest, b.indices]; rfl
    rw [b.result, b.layers.eq_spec]
    simp only [slhVerifyInternal, h, ne_eq, not_true_eq_false, ↓reduceIte, forest, b.digest_eq]
    rfl

/-- The domain separator and context-length byte are part of the verified message. -/
theorem pure_verdict {p msg sig ctx pk verdict}
    (v : if ctx.length > 255 then verdict = false
      else Nonempty (VerifyTrace p (withContext msg ctx) sig pk verdict)) :
    verdict = slhVerify p msg sig ctx pk := by
  by_cases h : ctx.length > 255
  · simpa [slhVerify, h] using v
  · simp only [h, ↓reduceIte] at v
    obtain ⟨trace⟩ := v
    simpa [slhVerify, h] using trace.eq_spec

/-- A keygen, signing and verification trace compose for every standard SHAKE set,
    every message and every valid context. Randomness is arbitrary. -/
theorem successful_roundtrip {p secret prf seed sk pk msg ctx rand sig verdict}
    (row : p ∈ parameterSets)
    (sizes : secret.length = p.n ∧ prf.length = p.n ∧ seed.length = p.n)
    (valid : ctx.length ≤ 255)
    (key : KeyGeneration p secret prf seed sk pk)
    (sign : Signature p (withContext msg ctx) sk rand sig)
    (verify : VerifyTrace p (withContext msg ctx) sig pk verdict) :
    (sk, pk) = slhKeygenInternal p secret prf seed ∧
    some sig = slhSign p msg ctx sk rand ∧
    verdict = slhVerify p msg sig ctx pk ∧ verdict = true := by
  have pv : p.Valid := by
    simp only [parameterSets, List.mem_cons, List.not_mem_nil, or_false] at row
    rcases row with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> decide
  have kg := keygen_keyOk p pv secret prf seed sizes.1 sizes.2.1 sizes.2.2
  rw [← key.eq_spec] at kg
  have signature := supported_internal_eq row sign
  have accepted := slh_complete_internal p pv (withContext msg ctx) sk rand kg.1
  rw [← signature, ← kg.2, ← verify.eq_spec] at accepted
  refine ⟨key.eq_spec, supported_pure_eq row valid sign, ?_, accepted⟩
  simpa [slhVerify, show ¬ctx.length > 255 by omega] using verify.eq_spec

/-- The key-generation trace relation admits precisely the reference key pair. -/
theorem keygen_trace_iff {p secret prf seed sk pk} :
    Nonempty (KeyGeneration p secret prf seed sk pk) ↔
      (sk, pk) = slhKeygenInternal p secret prf seed := by
  constructor
  · rintro ⟨v⟩; exact v.eq_spec
  · intro keys
    exact ⟨{ root := _, tree := referenceNode _ _ _ _ _ _,
             secretBytes := congrArg Prod.fst keys, publicBytes := congrArg Prod.snd keys }⟩

private def verificationLayers (p sig seed initial) : VerificationLayers p sig seed initial where
  states j := (List.range j).foldl (htVerifyLayer p sig seed) initial
  start := rfl
  recover j _ := by
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact referenceLayerRoot _ _ _ _ _ _
  coords j _ := by simp [List.range_succ, htVerifyLayer]

/-- Even for arbitrary malformed signature bytes, the verifier relation is total
    and admits exactly the verdict returned by the reference algorithm. -/
theorem verification_trace_iff {p msg sig pk verdict} :
    Nonempty (VerifyTrace p msg sig pk verdict) ↔ verdict = slhVerifyInternal p msg sig pk := by
  constructor
  · rintro ⟨v⟩; exact v.eq_spec
  · rintro rfl
    by_cases len : sig.length = p.sigBytes
    · let seed := block p pk 0
      let dg := Hmsg p (sig.take p.n) seed (block p pk 1) msg
      let f := forsPkFromSig p ((sig.drop p.n).take p.forsSigBytes) (dg.take p.mdBytes)
        seed (forsAddress p dg)
      let ls := verificationLayers p (sig.drop (p.n + p.forsSigBytes)) seed
        (f, digestTree p dg, digestLeaf p dg)
      refine ⟨.checked len { digest := dg, digits := _, forsRoot := f,
                             digest_eq := rfl, indices := rfl, forest := rfl,
                             layers := ls, result := ?_ }⟩
      simp only [slhVerifyInternal, len, ne_eq, not_true_eq_false, ↓reduceIte]
      rfl
    · simpa [slhVerifyInternal, len] using
        (show Nonempty (VerifyTrace p msg sig pk false) from ⟨.wrongLength len⟩)

#print axioms keygen_trace_iff
#print axioms verification_trace_iff
#print axioms KeyGeneration.eq_spec
#print axioms VerifyTrace.eq_spec
#print axioms pure_verdict
#print axioms successful_roundtrip

end LinkedArm.Signer
