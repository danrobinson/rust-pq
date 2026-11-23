module
public import Rcni.Memory
public import Chainni.FunsExternal
public import Shani.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RcNiRust
open slhdsa.Intel
abbrev core.core_arch.x86.sse41._mm_blend_epi16 := ChainNiRust.core.core_arch.x86.sse41._mm_blend_epi16
def sha256.x86_sha.load_block (b : Array U8 64#usize) : Result (Array Reg 4#usize) :=
  let lane := Memory.shuffled b 0x0C0D0E0F08090A0B 0x0405060700010203
  ok (Array.make 4#usize [lane 0,lane 1,lane 2,lane 3])
def sha256.x86_sha.load_state (s : Array U32 8#usize) : Result (Array Reg 2#usize) :=
  ok (Array.make 2#usize [Memory.readState s 0,Memory.readState s 1])
def sha256.x86_sha.store_state (s : Array U32 8#usize) (v : Array Reg 2#usize) : Result (Array U32 8#usize) :=
  let s := Memory.store s 0 v.val[0]!
  let s := Memory.store s 1 v.val[1]!
  ok s
end RcNiRust
