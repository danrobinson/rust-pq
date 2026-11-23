module
public import Store256.Types
@[expose] public section
open Aeneas Aeneas.Std Result slhdsa.X86
namespace StoreRust.core.core_arch.x86
abbrev avx512bw._mm512_shuffle_epi8 := GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8
abbrev avx512f._mm512_broadcast_i32x4 := GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4

/-- Intel VPUNPCK interleaves equal-sized elements from corresponding 128-bit lanes. -/
def unpack (width half : Nat) (a b : _root_.core.core_arch.x86.__m512i) : Result _root_.core.core_arch.x86.__m512i := ok fun j =>
  let word := j.val % 4
  let src := 4*(j.val/4) + 2*half + (word/(2*width))*width + word%width
  (if word/width % 2 = 0 then a else b) ⟨src%16,Nat.mod_lt _ (by decide)⟩

abbrev avx512f._mm512_unpacklo_epi32 := unpack 1 0
abbrev avx512f._mm512_unpackhi_epi32 := unpack 1 1
abbrev avx512f._mm512_unpacklo_epi64 := unpack 2 0
abbrev avx512f._mm512_unpackhi_epi64 := unpack 2 1
end StoreRust.core.core_arch.x86

namespace StoreRust
abbrev Rows := Array (Array (Array U8 16#usize) 4#usize) 4#usize
def arr4 {α : Type} (f : Fin 4 → α) : Array α 4#usize :=
  Array.from (List.ofFn f) (by simp)
def arr16 {α : Type} (f : Fin 16 → α) : Array α 16#usize :=
  Array.from (List.ofFn f) (by simp)

/-- Reinterpret four 64-byte registers in little-endian memory order. -/
instance : LaneRepr (Array _root_.core.core_arch.x86.__m512i 4#usize) Rows where
  castBits x := arr4 fun g => arr4 fun q => arr16 fun k =>
    ⟨GatherRust.core.core_arch.x86.byteAt x.val[g.val]! (16*q.val+k.val)⟩
end StoreRust
