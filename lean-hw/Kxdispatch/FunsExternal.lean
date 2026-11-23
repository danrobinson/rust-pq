module
public import Kxdispatch.Types
public import Kavxperm.Funs
public import Gather512.FunsExternal
@[expose] public section
namespace KxdispatchRust
abbrev shake256.parallel.avx512.permute := KavxpermRust.shake256.parallel.avx512.permute
abbrev sha256.x86.avx512_available := GatherRust.sha256.x86.avx512_available
end KxdispatchRust
