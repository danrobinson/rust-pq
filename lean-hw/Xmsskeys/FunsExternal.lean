module
public import Xmsskeys.Types
public import Wotsx86.Funs
public import Digest256.Funs
public import Gather512.Funs
public import Keypadding.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace XmssKeysRust
def asChecked (a : address.Adrs) : WotsX86Rust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def asPad (a : address.Adrs) : PadRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def xmss.wide.prepare_message {L} (row : Array U8 L) (a : address.Adrs) :=
  PadRust.xmss.wide.prepare_message row (asPad a)
def sha256.x86.wots_endpoints {N L} (st : Array U32 8#usize) (sk : Array U8 N) (a : address.Adrs)
    (first : U32) (out : Slice (Array U8 L)) := WotsX86Rust.sha256.x86.wots_endpoints st sk (asChecked a) first out
abbrev sha256.x86.key_digests {N L} := @DigestRust.sha256.x86.key_digests N L
abbrev sha512.x86.key_digests {N L} := @GatherRust.sha512.x86.key_digests N L

def core.slice.Slice.chunks_mut {T : Type u} (s : Slice T) (width : Usize) :
    Result (core.slice.iter.ChunksMut T × (core.slice.iter.ChunksMut T → Slice T)) :=
  if width.val=0 then fail .panic else ok (⟨s,width,0⟩,fun it => it.slice)

def core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next {T : Type u} (it : core.slice.iter.ChunksMut T) :
    Result (Option (Slice T) × core.slice.iter.ChunksMut T ×
      (core.slice.iter.ChunksMut T → Option (Slice T) → core.slice.iter.ChunksMut T)) :=
  if it.offset < it.slice.length then
    let part := (it.slice.val.drop it.offset).take it.width.val
    let chunk := Slice.from part (by have := it.slice.property; simp [part]; omega)
    ok (some chunk,{it with offset := it.offset+part.length},fun other returned =>
      match returned with
      | none => other
      | some changed => {other with slice := other.slice.setSlice! it.offset changed.val})
  else ok (none,it,fun other _ => other)

/-- The mutable-item specialization threads Aeneas's returned borrow through
enumeration. The index belongs to the iterator and has no write-back effect. -/
structure core.iter.traits.iterator.Iterator (I A : Type u) where
  next : I → Result (Option A × I × (I → Option A → I))
  enumerate : I → Result (Aeneas.Std.core.iter.adapters.enumerate.Enumerate I ×
    (Aeneas.Std.core.iter.adapters.enumerate.Enumerate I → I))

@[trait_default] def core.iter.traits.iterator.Iterator.enumerate.trait_default {I A : Type u}
    (_ : core.iter.traits.iterator.Iterator I A) (i : I) :
    Result (Aeneas.Std.core.iter.adapters.enumerate.Enumerate I × (Aeneas.Std.core.iter.adapters.enumerate.Enumerate I → I)) :=
  ok (⟨i,0#usize⟩,fun e => e.iter)

def core.iter.adapters.enumerate.IteratorEnumerate.next {I A : Type}
    (methods : core.iter.traits.iterator.Iterator I A) (it : Aeneas.Std.core.iter.adapters.enumerate.Enumerate I) := do
  let (item,next,back) ← methods.next it.iter
  let restore := fun (other : Aeneas.Std.core.iter.adapters.enumerate.Enumerate I) (out : Option (Usize × A)) =>
    {other with iter := back other.iter (out.map Prod.snd)}
  match item with
  | none => ok (none,{it with iter := next},restore)
  | some x =>
    let count ← it.count + 1#usize
    ok (some (it.count,x),⟨next,count⟩,restore)
end XmssKeysRust
