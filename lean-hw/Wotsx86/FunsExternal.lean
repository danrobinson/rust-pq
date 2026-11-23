module
public import Wotsx86.Types
public import Wots.Funs
public import Gather512.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace WotsX86Rust

def asKernel (a : address.Adrs) : WotsRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

def sha256.x86.avx512.wots_endpoints {N L} (state : Array U32 8#usize) (sk : Array U8 N) (a : address.Adrs)
    (first : U32) (out : Slice (Array U8 L)) :=
  WotsRust.sha256.x86.avx512.wots_endpoints state sk (asKernel a) first out

def sha256.x86.avx512.recover (N : Usize) (state : Array U32 8#usize) (a : address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (out : Slice (Array U8 64#usize)) :=
  WotsRust.sha256.x86.avx512.recover N state (asKernel a) sig digits out

abbrev sha256.x86.has_avx512.get := GatherRust.sha256.x86.avx512_available
end WotsX86Rust
