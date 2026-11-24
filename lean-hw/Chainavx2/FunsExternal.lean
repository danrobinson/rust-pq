module
public import Chainavx2.Types
public import Chainavx2.Chunks
public import Parent512.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ChainAvx2Rust
abbrev hash.chain_blocks_portable := slhdsa.hash.chain_blocks_portable
abbrev sha256.x86.avx2.compress8 := Avx2Rust.sha256.x86.avx2.compress8

def nativeLanes (x : _root_.core.core_arch.x86.__m256i) : Array U32 8#usize :=
  Array.from (List.ofFn fun i : Fin 8 => (⟨x i⟩ : U32)) (by simp)

instance : LaneRepr (Array _root_.core.core_arch.x86.__m256i 8#usize)
    (Array (Array U32 8#usize) 8#usize) where
  castBits x := Array.from (List.ofFn fun i : Fin 8 => nativeLanes (x.val[i.val]'(by scalar_tac))) (by simp)
end ChainAvx2Rust
