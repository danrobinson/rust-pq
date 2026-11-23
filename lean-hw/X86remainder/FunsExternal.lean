module
public import X86remainder.Types
public import Rcdispatch.Funs
public import Streamscalar.Funs
public import Armstream.FunsExternal
public import Chainwide.FunsExternal
@[expose] public section
open Aeneas.Std Result
namespace X86RemainderRust
abbrev core.slice.raw.from_ref {T : Type u} := @ArmStreamRust.core.slice.raw.from_ref T
abbrev sha2.sha256.compress256 := RcDispatchRust.sha256.compress256
abbrev sha2.sha512.compress512 := RcDispatchRust.sha512.compress512
abbrev sha256.stream.scalar := StreamScalarRust.sha256.stream.scalar
abbrev sha512.stream.scalar := StreamScalarRust.sha512.stream.scalar

opaque bmi2Available : Bool
def sha256.stream.has_bmi2.get : Result Bool := ok bmi2Available
abbrev sha512.stream.has_bmi2.get := sha256.stream.has_bmi2.get
def sha256.stream.hardware_backend.get : Result Bool := ok (RcDispatchRust.sha && RcDispatchRust.ssse3 && RcDispatchRust.sse41)
abbrev sha512.stream.hardware_backend.get := RcDispatchRust.sha512.avx2_cpuid.get
def sha256.stream.dedicated.get : Result Bool := ok RcDispatchRust.sha
def sha512.stream.dedicated.get : Result Bool := ok RcDispatchRust.sha
end X86RemainderRust
