import Kgridbulk.Top

open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kgridbulk
set_option maxHeartbeats 1500000

/-- The parallel build uses one all-zero rate block to permute a single sponge. -/
theorem zero_block_permute (s : Array U64 25#usize) (input : Slice U8)
    (zero : input.val = List.replicate 136 (0#u8))
    (available : GatherRust.avx512Available = true) :
    KgridbulkRust.shake256.stream_x86.blocks s input ⦃ out =>
      Keccak.words out = permute (Keccak.words s) ⦄ := by
  have size : input.length = 136 := by simp [Slice.length, zero]
  apply WP.spec_mono (blocks_fips s input (by rw [size]) available)
  intro out eq
  rw [feed_block _ _ (by simp [Keccak.words]) size] at eq
  have blank : ∀ i : Fin 17, wordAt (List.replicate 136 (0#u8)) (8*i.val) = 0 := by decide
  have unchanged : ratePrefix (Keccak.words s) input.val 17 = Keccak.words s := by
    apply ext25 _ _ (by simp [ratePrefix]) (by simp [Keccak.words])
    intro i hi
    rw [ratePrefix, ofFnAt _ _ hi]
    by_cases h : i < 17
    · rw [ite_eq_left h, zero, blank ⟨i,h⟩]
      exact BitVec.xor_zero
    · rw [ite_eq_right h]
  rw [unchanged] at eq
  exact (Prod.mk.inj eq).1

#print axioms zero_block_permute
end slhdsa.Kgridbulk
