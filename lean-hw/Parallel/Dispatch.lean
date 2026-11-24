import Keccakscalar.Proof
import Kgridbulk.ZeroBlock

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelDispatch

abbrev sha256.x86.avx512_available := GatherRust.sha256.x86.avx512_available
abbrev shake256.stream_x86.blocks := KgridbulkRust.shake256.stream_x86.blocks
abbrev shake256.permute_loop := KeccakScalarRust.shake256.permute_loop

/-- Fresh Aeneas entry for the x86 parallel build. The source gate also checks
the scalar loop, round constant table and all external signatures. -/
def shake256.permute
  (state : Array Std.U64 25#usize) : Result (Array Std.U64 25#usize) := do
  let b ← sha256.x86.avx512_available
  if b
  then
    let a := Array.repeat 136#usize 0#u8
    let s ← lift (Array.to_slice a)
    shake256.stream_x86.blocks state s
  else shake256.permute_loop state 0#usize

theorem permute_fips (s : Array U64 25#usize) :
    shake256.permute s ⦃ out => Keccak.words out = Spec.Keccak.permute (Keccak.words s) ⦄ := by
  cases h : GatherRust.avx512Available with
  | false =>
    simpa [shake256.permute, sha256.x86.avx512_available, GatherRust.sha256.x86.avx512_available,
      h, step_simps, KeccakScalarRust.shake256.permute, shake256.permute_loop] using
      PlatformShake.scalar_permute s
  | true =>
    simp only [shake256.permute, sha256.x86.avx512_available, GatherRust.sha256.x86.avx512_available,
      h, bind_ok, ite_true, lift]
    apply Kgridbulk.zero_block_permute _ _ _ h
    simp [Array.val_to_slice,Array.repeat_val]

#print axioms permute_fips
end slhdsa.ParallelDispatch
