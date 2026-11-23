module
public import Wotswide.Types
public import Wotsx86.Funs
public import X86remainder.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace WotsWideRust
def checkedAddress (a : address.Adrs) : WotsX86Rust.address.Adrs :=
  ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
abbrev sha256.compress := X86RemainderRust.sha256.compress
abbrev sha512.compress := X86RemainderRust.sha512.compress
def sha256.x86.recover (N : Usize) (state : Array U32 8#usize) (a : address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (out : Slice (Array U8 64#usize)) :=
  WotsX86Rust.sha256.x86.recover N state (checkedAddress a) sig digits out
end WotsWideRust
