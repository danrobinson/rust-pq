module
public import X86stream.Types
public import X86remainder.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace X86StreamRust
abbrev core.slice.Slice.as_chunks {T : Type u} := @ArmStreamRust.core.slice.Slice.as_chunks T
abbrev sha256.stream.remainder := X86RemainderRust.sha256.stream.remainder
abbrev sha512.stream.remainder := X86RemainderRust.sha512.stream.remainder
abbrev sha256.stream.dedicated.get := X86RemainderRust.sha256.stream.dedicated.get

/-- Runtime check for AVX-512F, AVX-512BW and BMI2. -/
opaque vectorAvailable : Bool
def sha256.stream.available.get : Result Bool := ok vectorAvailable
abbrev sha512.stream.available.get := sha256.stream.available.get

/-- The group kernels remain abstract in this extraction. The driver theorem
requires a sequential-compression specification whenever it selects one. -/
opaque sha256.stream.prescheduled : Array U32 8#usize → Slice (Array (Array U8 64#usize) 16#usize) → Result (Array U32 8#usize)
opaque sha512.stream.prescheduled : Array U64 8#usize → Slice (Array (Array U8 128#usize) 8#usize) → Result (Array U64 8#usize)
end X86StreamRust
