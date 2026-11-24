import Gather512.Top
import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result

namespace slhdsa.X86.S512.Gather
private theorem be_word (w : BitVec 64) : w.toBEBytes = Spec.toByte w.toNat 8 := by
  apply List.ext_getElem
  · simp [Spec.toByte]
  · intro i hi hj
    have bound : i < 8 := by simpa using hi
    simp only [BitVec.toBEBytes,List.getElem_reverse,Spec.toByte,List.getElem_map,List.getElem_range]
    have len : w.toLEBytes.length = 8 := by simp
    ext k hk
    have h := BitVec.toLEBytes_getElem_testBit w (8-1-i) k (by omega) ⟨hk,by omega⟩
    simp only [len]
    have modbit (x : Nat) : (x % 256).testBit k = x.testBit k := by
      change (x % 2^8).testBit k = _
      rw [Nat.testBit_mod_two_pow x 8 k]; simp [hk]
    simp only [BitVec.getElem_eq_testBit_toNat,BitVec.toNat_ofNat,modbit,Nat.testBit_shiftRight]
    exact h

theorem encode_take (ws : List (BitVec 64)) (n : Nat) :
    bytes (Parents.encoded (ws.take n)) = (_root_.slhdsa.S512.ser ws).take (8*n) := by
  induction n generalizing ws with
  | zero => simp [Parents.encoded,bytes]
  | succ n ih =>
    cases ws with
    | nil => simp [Parents.encoded,bytes,_root_.slhdsa.S512.ser]
    | cons w ws =>
      have length : (Spec.toByte w.toNat 8).length = 8 := by simp [Spec.toByte]
      simp only [List.take_succ_cons,Parents.encoded,List.flatMap_cons,bytes_append]
      change bytes (Parents.be ⟨w⟩) ++ bytes (Parents.encoded (ws.take n)) = _
      rw [ih]
      have eqn : bytes (Parents.be ⟨w⟩) = Spec.toByte w.toNat 8 := by simpa [bytes,Parents.be, List.map_map] using be_word w
      rw [eqn]
      change _ = ((Spec.toByte w.toNat 8) ++ _root_.slhdsa.S512.ser ws).take (8*(n+1))
      rw [show 8*(n+1) = (Spec.toByte w.toNat 8).length+8*n by omega,List.take_length_add_append]

/-- Feed a chaining state for one seed block and the correctly padded continuation for
each lane. The production result is exactly the FIPS 180-4 hash truncated to N bytes. -/
theorem seeded_digest_spec (N L : Usize) (seed : Array U64 8#usize)
    (rows : Slice (Array U8 L)) (out : Slice (Array U8 N)) (B : Spec.Bytes) (msgs : Fin 8 → Spec.Bytes)
    (cpu : GatherRust.avx512Available = true) (shape : (N.val = 24 ∧ L.val = 1280) ∨ (N.val = 32 ∧ L.val = 2304))
    (hn : 0 < rows.length) (h8 : rows.length ≤ 8) (heq : out.length = rows.length) (hB : B.length = 128)
    (hs : seed.val.map (·.bv) = Spec.SHA512.compress Spec.SHA512.H0 B)
    (hp : ∀ j : Fin 8, j.val < rows.length → bytes rows.val[j.val]!.val = _root_.slhdsa.S512.padFrom 128 (msgs j)) :
    GatherRust.sha512.x86.key_digests seed rows out ⦃ r => r.length = out.length ∧ ∀ j : Fin 8,
      j.val < rows.length → bytes r.val[j.val]!.val = (Spec.sha512 (B ++ msgs j)).take N.val ⦄ := by
  apply WP.spec_mono (key_digests_spec N L seed rows out cpu shape hn h8 heq)
  rintro r ⟨hl,hr⟩
  refine ⟨hl, fun j hj => ?_⟩
  have len : (_root_.slhdsa.S512.padFrom 128 (msgs j)).length = L.val := by rw [← hp j hj]; simp
  rw [hr j hj,encode_take,hs,hp j hj,_root_.slhdsa.S512.sha512_prefix128 _ _ hB, show 8*(N.val/8) = N.val by omega]
  simp only [hashed,_root_.slhdsa.S512.hashFrom,len]

/-- FIPS 205 T for all active SHA2-192/256 WOTS public-key messages, given the
caller-provided seed state and padded address/endpoint strings in their specified layouts. -/
theorem tweakable_digest_spec (p : Spec.Params) (N L : Usize) (seed : Array U64 8#usize)
    (rows : Slice (Array U8 L)) (out : Slice (Array U8 N)) (pk : Spec.Bytes)
    (adrs : Fin 8 → Spec.Adrs) (endpoints : Fin 8 → Spec.Bytes)
    (cpu : GatherRust.avx512Available = true) (shape : (N.val = 24 ∧ L.val = 1280) ∨ (N.val = 32 ∧ L.val = 2304))
    (fam : p.family = .sha2) (width : p.n = N.val) (hpk : pk.length = p.n)
    (hn : 0 < rows.length) (h8 : rows.length ≤ 8) (heq : out.length = rows.length)
    (hs : seed.val.map (·.bv) = Spec.SHA512.compress Spec.SHA512.H0 (pk ++ Spec.toByte 0 (128-p.n)))
    (hp : ∀ j : Fin 8, j.val < rows.length → bytes rows.val[j.val]!.val =
      _root_.slhdsa.S512.padFrom 128 ((adrs j).compress ++ endpoints j)) :
    GatherRust.sha512.x86.key_digests seed rows out ⦃ r => r.length = out.length ∧ ∀ j : Fin 8,
      j.val < rows.length → bytes r.val[j.val]!.val = Spec.T p pk (adrs j) (endpoints j) ⦄ := by
  have hB : (pk ++ Spec.toByte 0 (128-p.n)).length = 128 := by simp [Spec.toByte,hpk]; omega
  apply WP.spec_mono (seeded_digest_spec N L seed rows out _ _ cpu shape hn h8 heq hB hs hp)
  rintro r ⟨hl,hr⟩
  refine ⟨hl,fun j hj => ?_⟩
  simpa only [Spec.T, fam, show ¬N.val = 16 by omega, ↓reduceIte, List.append_assoc,width] using hr j hj

#print axioms seeded_digest_spec
#print axioms tweakable_digest_spec
end slhdsa.X86.S512.Gather
