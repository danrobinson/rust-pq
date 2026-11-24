module
public import Kgridbulk.Types
public import Kdiag.Funs
public import Chainwide.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace KgridbulkRust
instance : ChainWideRust.MemoryElement U64 := ⟨8,fun x => x.bv.toLEBytes.map (fun b => ⟨b⟩)⟩
abbrev core.slice.Slice.as_ptr := @ChainWideRust.core.slice.Slice.as_ptr
abbrev core.ptr.const_ptr.RawPtrConstT.add := @ChainWideRust.core.ptr.const_ptr.RawPtrConstT.add
abbrev core.ptr.const_ptr.RawPtrConstT.cast := @GatherRust.core.ptr.const_ptr.RawPtrConstT.cast
abbrev sha256.x86.avx512_available := GatherRust.sha256.x86.avx512_available
abbrev shake256.stream_x86.even := KdiagRust.shake256.stream_x86.even
abbrev shake256.stream_x86.odd := KdiagRust.shake256.stream_x86.odd
abbrev core.core_arch.x86.avx512f._mm512_xor_si512 := KavxRust.core.core_arch.x86.avx512f._mm512_xor_si512

/-- A masked unaligned 64-bit load checks the entire extent of each active lane. -/
def core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64 (mask : U8) (p : ConstRawPtr I64) :
    Result core.core_arch.x86.__m512i :=
  if ∀ j : Fin 8, mask.bv.getLsbD j.val = true → p.offset + 8*j.val + 8 ≤ p.allocation.length then
    ok fun j => if mask.bv.getLsbD j.val then
      GatherRust.core.core_arch.x86.littleWord p.allocation (p.offset + 8*j.val) else 0
  else fail .undef

/-- Store the five enabled words of a row into a 25-word state. -/
def shake256.stream_x86.write_row (s : Array U64 25#usize) (y : Usize) (row : core.core_arch.x86.__m512i) :
    Result (Array U64 25#usize) :=
  if y.val < 5 then
    ok (Array.make 25#usize (List.ofFn (n := 25) fun i =>
      if i.val / 5 = y.val then ⟨row ⟨i.val%5,by omega⟩⟩ else s.val[i.val]!))
  else fail .undef
end KgridbulkRust
