module
public import Streamstep.Types
public import Streamround.Funs
@[expose] public section
namespace StreamStepRust
abbrev sha256.stream.round := StreamRoundRust.sha256.stream.round
abbrev sha512.stream.round := StreamRoundRust.sha512.stream.round
end StreamStepRust
