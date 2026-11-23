module
public import Streamscalar.Types
public import Streamstep.Funs
@[expose] public section
namespace StreamScalarRust
abbrev sha256.stream.read_word := StreamStepRust.sha256.stream.read_word
abbrev sha512.stream.read_word := StreamStepRust.sha512.stream.read_word
abbrev sha256.stream.scalar_step := StreamStepRust.sha256.stream.scalar_step
abbrev sha512.stream.scalar_step := StreamStepRust.sha512.stream.scalar_step
end StreamScalarRust
