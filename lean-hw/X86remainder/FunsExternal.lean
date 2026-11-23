module
public import X86remainder.Types
public import Streamscalar.Funs
public import Armstream.FunsExternal
public import Chainwide.FunsExternal
@[expose] public section
open Aeneas.Std Result
namespace X86RemainderRust
abbrev core.slice.raw.from_ref {T : Type u} := @ArmStreamRust.core.slice.raw.from_ref T
abbrev sha2.sha256.compress256 := ArmStreamRust.sha2.sha256.compress256
abbrev sha2.sha512.compress512 := ArmStreamRust.sha2.sha512.compress512
abbrev sha256.stream.scalar := StreamScalarRust.sha256.stream.scalar
abbrev sha512.stream.scalar := StreamScalarRust.sha512.stream.scalar

opaque bmi2Available : Bool
def sha256.stream.has_bmi2.get : Result Bool := ok bmi2Available
abbrev sha512.stream.has_bmi2.get := sha256.stream.has_bmi2.get
def sha256.stream.dedicated.get : Result Bool := ok ChainWideRust.shaNiAvailable
abbrev sha512.stream.dedicated.get := sha256.stream.dedicated.get
end X86RemainderRust
