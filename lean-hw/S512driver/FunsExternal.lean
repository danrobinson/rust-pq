module
public import S512driver.Types
public import Streamvector.Funs
public import Digest256.FunsExternal
public import Streamround.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace S512driverRust
abbrev sha512.stream.schedule_table := StreamVectorRust.sha512.stream.schedule_table
abbrev sha512.stream.round := StreamRoundRust.sha512.stream.round
namespace core
abbrev slice.Slice.as_ptr {L : Usize} := @GatherRust.core.slice.Slice.as_ptr L
abbrev ptr.const_ptr.RawPtrConstT.cast {T : Type} := @GatherRust.core.ptr.const_ptr.RawPtrConstT.cast T
abbrev ptr.const_ptr.RawPtrConstT.add := GatherRust.core.ptr.const_ptr.RawPtrConstT.add
namespace core_arch.x86
open _root_.core.core_arch.x86
abbrev avx512bw._mm512_shuffle_epi8 := GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8
abbrev avx512f._mm512_broadcast_i32x4 := GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4
abbrev avx512f._mm512_set_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32
def avx512f._mm512_i32gather_epi32 (scale : I32) (offsets : __m512i) (p : GatherRust.ReadPtr I32) :=
  DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32 scale (fun _ => 0) 65535#u16 offsets p
def avx512f._mm512_i32gather_epi64 (scale : I32) (offsets : __m256i) (p : GatherRust.ReadPtr I64) :=
  GatherRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi64 scale (fun _ => 0) 255#u8 offsets p
end core_arch.x86
end core
end S512driverRust

