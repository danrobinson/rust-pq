module
public import X86stream.Types
public import X86remainder.Funs
public import Streamvector.Funs
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

abbrev sha256.stream.prescheduled := StreamVectorRust.sha256.stream.prescheduled
abbrev sha512.stream.prescheduled := StreamVectorRust.sha512.stream.prescheduled
end X86StreamRust
