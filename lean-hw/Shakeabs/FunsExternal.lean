module
public import Shakeabs.Types
public import Keccakscalar.Funs
@[expose] public section
namespace ShakeAbsRust
/-- The scalar Keccak implementation. Other backends can be substituted after
proving equality on all states. -/
abbrev shake256.permute := KeccakScalarRust.shake256.permute
end ShakeAbsRust
