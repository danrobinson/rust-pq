import Aeneas

namespace ParallelWorkerIterators
open Aeneas Aeneas.Std Result

/-- Rust's IntoIterator for a shared Vec takes its slice iterator. -/
def borrowed {T : Type u} (v : alloc.vec.Vec T) : Result (core.slice.iter.Iter T) :=
  core.slice.Slice.iter v.deref

def mapped {I : Type i} {F : Type f} (it : I) (callback : F) : Result (core.iter.adapters.map.Map I F) :=
  ok ⟨it,callback⟩

/-- Preserve both the advanced iterator and the state returned by FnMut. -/
def next {I : Type i} {F : Type f} {T : Type t} {U : Type u} (iterator : core.iter.traits.iterator.Iterator I T)
    (callback : core.ops.function.FnMut F T U) (m : core.iter.adapters.map.Map I F) :
    Result (Option U × core.iter.adapters.map.Map I F) :=
  Aeneas.Std.bind (iterator.next m.iter) fun (item,it) =>
    match item with
    | none => ok (none,⟨it,m.f⟩)
    | some x => Aeneas.Std.bind (callback.call_mut m.f x) fun (value,f) =>
        ok (some value,⟨it,f⟩)

private def mapItems {T : Type t} {F : Type f} {U : Type u}
    (callback : core.ops.function.FnMut F T U) (xs : List T) (state : F) :
    Result { ys : List U // ys.length=xs.length } :=
  match xs with
  | [] => ok ⟨[],rfl⟩
  | x::rest => Aeneas.Std.bind (callback.call_mut state x) fun (y,state') =>
      Aeneas.Std.bind (mapItems callback rest state') fun ys =>
        ok ⟨y::ys.val,by simp [ys.property]⟩

def arrayMap {T : Type t} {F : Type f} {U : Type u} {N : Usize} (callback : core.ops.function.FnMut F T U)
    (a : Array T N) (f : F) : Result (Array U N) :=
  Aeneas.Std.bind (mapItems callback a.val f) fun ys => ok (Array.from ys.val (by simp [ys.property]))

theorem exhausted {I : Type i} {F : Type f} {T : Type t} {U : Type u} (it : core.iter.traits.iterator.Iterator I T)
    (f : core.ops.function.FnMut F T U) (m : core.iter.adapters.map.Map I F) (stop : I)
    (last : it.next m.iter = ok (none,stop)) : next it f m = ok (none,⟨stop,m.f⟩) := by
  simp [next,last,bind_ok]

theorem emits {I : Type i} {F : Type f} {T : Type t} {U : Type u} (it : core.iter.traits.iterator.Iterator I T)
    (f : core.ops.function.FnMut F T U) (m : core.iter.adapters.map.Map I F) (x : T) (value : U)
    (tail : I) (f' : F) (found : it.next m.iter = ok (some x,tail))
    (computed : f.call_mut m.f x = ok (value,f')) :
    next it f m = ok (some value,⟨tail,f'⟩) := by
  simp [next,found,computed,bind_ok]

end ParallelWorkerIterators
