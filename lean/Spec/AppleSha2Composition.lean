import Spec.AppleSignatureRoundTrip

/-! SHA-2 specialization of the signing trace. The ordinary and segmented
drivers agree on the logical bytes passed to HMAC and MGF1. This file proves
the consequence of their call equations for both message layouts. -/
namespace LinkedArm.Signer.Sha2
open Spec

private def sha (p : Params) : Bytes → Bytes := if p.n = 16 then sha256 else sha512
private def blockSize (p : Params) : Nat := if p.n = 16 then 64 else 128

private def keyPad (p : Params) (key : Bytes) : Bytes :=
  key ++ List.replicate (blockSize p - key.length) 0#8

/-- The output of each actual MGF1 counter invocation, in byte order. -/
structure HashCalls (p : Params) (msg sk random r digest : Bytes) where
  inner : Bytes
  first : Bytes
  counters : Nat → Bytes
  keySize : (block p sk 1).length ≤ blockSize p
  ipad : inner = sha p ((keyPad p (block p sk 1)).map (· ^^^ 0x36#8) ++ (random ++ msg))
  opad : r = (sha p ((keyPad p (block p sk 1)).map (· ^^^ 0x5c#8) ++ inner)).take p.n
  firstHash : first = sha p (r ++ block p sk 2 ++ block p sk 3 ++ msg)
  counter : ∀ i < (p.m + blockSize p / 2 - 1) / (blockSize p / 2),
    counters i = sha p ((r ++ block p sk 2 ++ first) ++ toByte i 4)
  output : digest = ((List.range ((p.m + blockSize p / 2 - 1) / (blockSize p / 2))).flatMap counters).take p.m

theorem HashCalls.eq_spec {p msg sk random r digest}
    (hc : HashCalls p msg sk random r digest) (family : p.family = .sha2) :
    r = PRFmsg p (block p sk 1) random msg ∧
    digest = Hmsg p r (block p sk 2) (block p sk 3) msg := by
  constructor
  · rw [hc.opad, hc.ipad]
    by_cases h : p.n = 16
    · have k : ¬ (block p sk 1).length > 64 := by simpa [blockSize, h] using hc.keySize
      simp [PRFmsg, family, sha, keyPad, blockSize, h, hmacSha256, k]
    · have k : ¬ (block p sk 1).length > 128 := by simpa [blockSize, h] using hc.keySize
      simp [PRFmsg, family, sha, keyPad, blockSize, h, hmacSha512, k]
  · let count := (p.m + blockSize p / 2 - 1) / (blockSize p / 2)
    have allCounters : (List.range count).flatMap hc.counters =
        (List.range count).flatMap (fun i => sha p ((r ++ block p sk 2 ++ hc.first) ++ toByte i 4)) := by
      apply List.flatMap_congr
      exact fun i hi => hc.counter i (List.mem_range.mp hi)
    rw [hc.output, allCounters, hc.firstHash]
    by_cases h : p.n = 16 <;> simp [Hmsg, family, sha, blockSize, h, mgf1, count]

/-- Actual reference computations for both HMAC hashes, the message hash and
    every MGF1 counter. This constructs the HashCalls data, including intermediate
    bytes, for arbitrary arguments. -/
def referenceHashes (p : Params) (msg sk random : Bytes) (family : p.family = .sha2)
    (keyFits : p.n ≤ (if p.n = 16 then 64 else 128)) :
    HashCalls p msg sk random (PRFmsg p (block p sk 1) random msg)
      (Hmsg p (PRFmsg p (block p sk 1) random msg) (block p sk 2) (block p sk 3) msg) := by
  let key := keyPad p (block p sk 1)
  let inner := sha p (key.map (· ^^^ 0x36#8) ++ (random ++ msg))
  let r := (sha p (key.map (· ^^^ 0x5c#8) ++ inner)).take p.n
  let first := sha p (r ++ block p sk 2 ++ block p sk 3 ++ msg)
  let counter := fun i => sha p ((r ++ block p sk 2 ++ first) ++ toByte i 4)
  let digest := ((List.range ((p.m + blockSize p / 2 - 1) / (blockSize p / 2))).flatMap counter).take p.m
  have hc : HashCalls p msg sk random r digest :=
    { inner, first, counters := counter, keySize := by
        exact (List.length_take_le ..).trans keyFits
      ipad := rfl, opad := rfl, firstHash := rfl, counter := fun _ _ => rfl, output := rfl }
  obtain ⟨rEq,dgEq⟩ := hc.eq_spec family
  rw [rEq] at dgEq
  rw [rEq,dgEq] at hc
  exact hc

structure Signature (p : Params) (msg sk random out : Bytes) where
  r : Bytes
  digest : Bytes
  hashes : HashCalls p msg sk random r digest
  digits : List Nat
  decode : digits = base2b (digest.take p.mdBytes) p.a p.k
  forsSig : Bytes
  forsPk : Bytes
  forest : forsSig = forsRows p digits (block p sk 0) (block p sk 2) (forsAddress p digest)
  recovery : forsPk = forsRoots p digits forsSig (block p sk 2) (forsAddress p digest)
  layers : Layers
  calls : LayerCalls p (block p sk 0) (block p sk 2)
    ([],forsPk,digestTree p digest,digestLeaf p digest) layers
  output : out = r ++ forsSig ++
    (afterLayers p layers ([],forsPk,digestTree p digest,digestLeaf p digest) p.d).1

theorem Signature.eq_spec {p msg sk random out} (s : Signature p msg sk random out)
    (family : p.family = .sha2) : out = slhSignInternal p msg sk random := by
  obtain ⟨r, dg⟩ := s.hashes.eq_spec family
  have fs : s.forsSig = forsSign p (s.digest.take p.mdBytes) (block p sk 0) (block p sk 2)
      (forsAddress p s.digest) := by rw [s.forest, s.decode]; rfl
  have fr : s.forsPk = forsPkFromSig p s.forsSig (s.digest.take p.mdBytes) (block p sk 2)
      (forsAddress p s.digest) := by rw [s.recovery, s.decode]; rfl
  rw [s.output, layers_eq s.calls, fr, fs, dg, r]
  rfl

/-- Construct the SHA-2 call trace from the HMAC inner/outer digests, each MGF1
    counter, the FORS operations, and the visited hypertree layers. -/
theorem trace_iff {p msg sk random out}
    (row : p ∈ [sha2_128s,sha2_128f,sha2_192s,sha2_192f,sha2_256s,sha2_256f]) :
    Nonempty (Signature p msg sk random out) ↔ out = slhSignInternal p msg sk random := by
  have props : p.family = .sha2 ∧ p.n ≤ blockSize p := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at row
    rcases row with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  constructor
  · rintro ⟨s⟩; exact s.eq_spec props.1
  · rintro rfl
    let r := PRFmsg p (block p sk 1) random msg
    let digest := Hmsg p r (block p sk 2) (block p sk 3) msg
    let hc := referenceHashes p msg sk random props.1 props.2
    let md := digest.take p.mdBytes
    let a := forsAddress p digest
    let sig := forsSign p md (block p sk 0) (block p sk 2) a
    let root := forsPkFromSig p sig md (block p sk 2) a
    let init : LayerState := ([],root,digestTree p digest,digestLeaf p digest)
    let calls := referenceCalls p (block p sk 0) (block p sk 2) init
    refine ⟨{ r, digest, hashes := hc, digits := base2b md p.a p.k, decode := rfl,
              forsSig := sig, forsPk := root, forest := rfl, recovery := rfl,
              layers := referenceLayers p (block p sk 0) (block p sk 2) init,
              calls, output := ?_ }⟩
    rw [layers_eq calls]
    dsimp only [init, root, sig, a, md]
    rfl

theorem successful_roundtrip {p secret prf seed sk pk msg ctx supplied sig verdict}
    (row : p ∈ [sha2_128s,sha2_128f,sha2_192s,sha2_192f,sha2_256s,sha2_256f])
    (sizes : secret.length = p.n ∧ prf.length = p.n ∧ seed.length = p.n)
    (valid : ctx.length ≤ 255) (deterministic : Bool)
    (key : KeyGeneration p secret prf seed sk pk)
    (sign : Signature p (withContext msg ctx) sk (if deterministic then block p sk 2 else supplied) sig)
    (verify : VerifyTrace p (withContext msg ctx) sig pk verdict) :
    (sk, pk) = slhKeygenInternal p secret prf seed ∧
    some sig = slhSign p msg ctx sk (if deterministic then block p sk 2 else supplied) ∧
    verdict = slhVerify p msg sig ctx pk ∧ verdict = true := by
  have props : p.Valid ∧ p.family = .sha2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at row
    rcases row with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by constructor <;> decide, rfl⟩
  have kg := keygen_keyOk p props.1 secret prf seed sizes.1 sizes.2.1 sizes.2.2
  rw [← key.eq_spec] at kg
  have signature := sign.eq_spec props.2
  have accepted := slh_complete_internal p props.1 (withContext msg ctx) sk
    (if deterministic then block p sk 2 else supplied) kg.1
  rw [← signature, ← kg.2, ← verify.eq_spec] at accepted
  refine ⟨key.eq_spec, ?_, ?_, accepted⟩
  · simp [slhSign, show ¬ctx.length > 255 by omega, signature]
  · simpa [slhVerify, show ¬ctx.length > 255 by omega] using verify.eq_spec

#print axioms HashCalls.eq_spec
#print axioms trace_iff
#print axioms Signature.eq_spec
#print axioms successful_roundtrip

end LinkedArm.Signer.Sha2
