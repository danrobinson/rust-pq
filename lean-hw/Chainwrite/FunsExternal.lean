module
public import Chainwrite.Types
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ChainWriteRust
abbrev sha256.x86.avx512.transpose_rows := StoreRust.sha256.x86.avx512.transpose_rows
abbrev core.core_arch.x86.avx512bw._mm512_shuffle_epi8 := StoreRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8
abbrev core.core_arch.x86.avx512f._mm512_broadcast_i32x4 := StoreRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4
def core.num.U16.trailing_zeros (x : U16) : Result U32 := ok ⟨x.bv.ctz.setWidth 32⟩
end ChainWriteRust
