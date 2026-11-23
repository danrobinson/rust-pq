import Spec.AppleSha2Composition

namespace LinkedArm.Signer
open Spec

def sha2ParameterSets := [sha2_128s,sha2_128f,sha2_192s,sha2_192f,sha2_256s,sha2_256f]

/-- Observations at key generation, signing, and verification share the same key,
    message framing, randomness and serialized signature across all three calls. -/
def Session (p : Params) (secret prf seed msg ctx supplied : Bytes) (deterministic : Bool)
    (sk pk sig : Bytes) (verdict : Bool) : Prop :=
  let frame := withContext msg ctx
  let random := if deterministic then block p sk 2 else supplied
  Nonempty (KeyGeneration p secret prf seed sk pk) ∧
  ((p ∈ parameterSets ∧ Nonempty (Signature p frame sk random sig)) ∨
   (p ∈ sha2ParameterSets ∧ Nonempty (Sha2.Signature p frame sk random sig))) ∧
  Nonempty (VerifyTrace p frame sig pk verdict)

/-- For every well-sized input of every standardized set a complete mathematical
    execution exists. Its externally observable tuple is uniquely the FIPS one. -/
theorem session_iff {p secret prf seed msg ctx supplied deterministic sk pk sig verdict}
    (set : p ∈ parameterSets ∨ p ∈ sha2ParameterSets)
    (sizes : secret.length = p.n ∧ prf.length = p.n ∧ seed.length = p.n)
    (valid : ctx.length ≤ 255) :
    Session p secret prf seed msg ctx supplied deterministic sk pk sig verdict ↔
      (sk, pk) = slhKeygenInternal p secret prf seed ∧
      some sig = slhSign p msg ctx sk (if deterministic then block p sk 2 else supplied) ∧
      verdict = slhVerify p msg sig ctx pk ∧ verdict = true := by
  constructor
  · rintro ⟨⟨key⟩, family, ⟨verify⟩⟩
    rcases family with ⟨shake, ⟨sign⟩⟩ | ⟨sha2, ⟨sign⟩⟩
    · exact successful_roundtrip shake sizes valid key sign verify
    · exact Sha2.successful_roundtrip sha2 sizes valid deterministic key sign verify
  · rintro ⟨keys, sign, verify, _⟩
    have hs : sig = slhSignInternal p (withContext msg ctx) sk
        (if deterministic then block p sk 2 else supplied) := by
      simpa [slhSign, show ¬ctx.length > 255 by omega] using sign
    refine ⟨keygen_trace_iff.mpr keys, ?_, verification_trace_iff.mpr ?_⟩
    · rcases set with shake | sha2
      · exact Or.inl ⟨shake, (trace_iff shake).mpr hs⟩
      · exact Or.inr ⟨sha2, (Sha2.trace_iff sha2).mpr hs⟩
    · simpa [slhVerify, show ¬ctx.length > 255 by omega] using verify

theorem session_exists {p secret prf seed msg ctx supplied deterministic}
    (set : p ∈ parameterSets ∨ p ∈ sha2ParameterSets)
    (sizes : secret.length = p.n ∧ prf.length = p.n ∧ seed.length = p.n)
    (valid : ctx.length ≤ 255) :
    ∃ sk pk sig, Session p secret prf seed msg ctx supplied deterministic sk pk sig true := by
  let keys := slhKeygenInternal p secret prf seed
  let random := if deterministic then block p keys.1 2 else supplied
  let sig := slhSignInternal p (withContext msg ctx) keys.1 random
  have pv : p.Valid := by
    rcases set with s | s
    all_goals
      simp only [parameterSets, sha2ParameterSets, List.mem_cons, List.not_mem_nil, or_false] at s
      rcases s with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> decide
  have kg := keygen_keyOk p pv secret prf seed sizes.1 sizes.2.1 sizes.2.2
  have accepted := slh_complete_internal p pv (withContext msg ctx) keys.1 random kg.1
  refine ⟨keys.1, keys.2, sig, (session_iff set sizes valid).mpr ⟨rfl, ?_, ?_, rfl⟩⟩
  · simp [slhSign, show ¬ctx.length > 255 by omega, sig, random]
  · rw [← kg.2] at accepted
    simpa [slhVerify, show ¬ctx.length > 255 by omega, sig] using accepted.symm

#print axioms session_iff
#print axioms session_exists
end LinkedArm.Signer
