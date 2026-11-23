module
public import Treehash.Types
public import X86remainder.Funs
@[expose] public section
namespace TreeHashRust
abbrev sha256.compress := X86RemainderRust.sha256.compress
abbrev sha512.compress := X86RemainderRust.sha512.compress
end TreeHashRust
