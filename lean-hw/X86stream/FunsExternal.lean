module
public import X86stream.Types
public import X86remainder.Funs
public import S8driver.Funs
public import S512driver.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace X86StreamRust
abbrev core.slice.Slice.as_chunks {T : Type u} := @ArmStreamRust.core.slice.Slice.as_chunks T
abbrev sha256.stream.remainder := X86RemainderRust.sha256.stream.remainder
abbrev sha512.stream.remainder := X86RemainderRust.sha512.stream.remainder
abbrev sha256.stream.dedicated.get := X86RemainderRust.sha256.stream.dedicated.get

/-- The five CPU and OS feature reports consumed by the two streaming cpufeatures guards. -/
opaque avx512f : Bool
opaque avx512bw : Bool
opaque avx512vl : Bool
opaque avx2 : Bool
opaque bmi2 : Bool
def vectorAvailable512 := avx512f && avx512bw && bmi2
def vectorAvailable256 := avx512f && avx512bw && avx512vl && avx2 && bmi2
def sha256.stream.available.get : Result Bool := ok vectorAvailable256
def sha512.stream.available.get : Result Bool := ok vectorAvailable512

abbrev sha256.stream.prescheduled := S8driverRust.sha256.stream.prescheduled
abbrev sha512.stream.prescheduled := S512driverRust.sha512.stream.prescheduled
end X86StreamRust
