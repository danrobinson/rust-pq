module
public import Parent512.Types
@[expose] public section
open Aeneas Aeneas.Std Result
open slhdsa.X86

def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    {T : Type u} {N : Usize} (a : Array T N) : Result (core.array.iter.IntoIter T N) := ok a.val

def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    {T : Type u} {N : Usize} (it : core.array.iter.IntoIter T N) : Result (Option T × core.array.iter.IntoIter T N) :=
  match it with
  | [] => ok (none, [])
  | x :: xs => ok (some x, xs)

def core.array.Array.map {T F U : Type u} {N : Usize} (inst : core.ops.function.FnMut F T U)
    (a : Array T N) (f : F) : Result (Array U N) :=
  core.array.from_fn N { FnOnceInst := {call_once := fun g i => do
    let x ← a.index_usize i
    inst.FnOnceInst.call_once g x }, call_mut := fun g i => do
      let x ← a.index_usize i
      inst.call_mut g x } f

/-- Only the two native-endian bit reinterpretations in this extraction have instances. -/
class LaneRepr (Src Dst : Type) where
  castBits : Src → Dst

instance : LaneRepr (Array U64 8#usize) core.core_arch.x86.__m512i where
  castBits x := ofWords64 fun i => x.val[i.val]!.bv

instance : LaneRepr core.core_arch.x86.__m512i (Array U64 8#usize) where
  castBits x := Array.from (List.ofFn fun i : Fin 8 => (⟨word64 x i⟩ : U64)) (by simp)

def core.intrinsics.transmute {Src : Type} (Dst : Type) [LaneRepr Src Dst] (x : Src) : Result Dst :=
  ok (LaneRepr.castBits x)
