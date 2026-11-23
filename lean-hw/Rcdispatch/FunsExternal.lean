module
public import Rcdispatch.Types
public import Rcni.Funs
public import Rcavx.Funs
public import Armstream.FunsExternal
@[expose] public section
open Aeneas.Std Result
namespace RcDispatchRust
opaque sha : Bool
opaque ssse3 : Bool
opaque sse41 : Bool
opaque avx2 : Bool
def sha256.shani_cpuid.get : Result Bool := ok (sha && sse41)
def sha512.avx2_cpuid.get : Result Bool := ok avx2
abbrev sha256.x86_sha.compress := RcNiRust.sha256.x86_sha.compress
abbrev sha512.x86_avx2.compress := RcAvxRust.sha512.x86_avx2.compress
-- The caller's feature guards make these branches unreachable. Returning failure
-- keeps accidental execution from satisfying a total-correctness postcondition.
def sha256.soft.unroll.compress (_ : Array U32 8#usize) (_ : Slice (Array U8 64#usize)) : Result (Array U32 8#usize) := fail .panic
def sha512.soft.unroll.compress (_ : Array U64 8#usize) (_ : Slice (Array U8 128#usize)) : Result (Array U64 8#usize) := fail .panic
end RcDispatchRust
