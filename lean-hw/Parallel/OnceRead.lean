import Parallel.SignJoinProgram

namespace ParallelOnceRead
open Aeneas Aeneas.Std Result

/-- Offsets are relative to the same live allocation. An absent reference is
represented separately from a pointer to byte zero of that allocation. -/
structure Layout where
  flag : Nat
  flagBytes : Nat
  payload : Nat
  bytes : Nat
  deriving DecidableEq, Repr

def Layout.separate (l : Layout) : Prop :=
  l.flag+l.flagBytes≤l.payload ∨ l.payload+l.bytes≤l.flag

instance (l : Layout) : Decidable l.separate := by unfold Layout.separate; infer_instance

/-- The selected address after the acquire load, zero comparison, and select. -/
def getRef (l : Layout) (loadFlag : Nat → Nat) : Option Nat :=
  if loadFlag l.flag=0 then some l.payload else none

theorem get_empty (l : Layout) (flag : Nat → Nat) (empty : flag l.flag=3) :
    getRef l flag=none := by simp [getRef,empty]

/-- A successful acquire returning the complete state exposes the payload at
the same offset used by the initializing copy. The caller supplies the
synchronized memory observation. -/
theorem get_complete {α : Type} (l : Layout) (flag : Nat → Nat) (memory : Nat → α)
    (value : α) (complete : flag l.flag=0) (copied : memory l.payload=value) :
    ok ((getRef l flag).map memory) = slhdsa.ParallelSignJoin.readCell (some value) := by
  simp [getRef,complete,copied,slhdsa.ParallelSignJoin.readCell]

theorem other_state (l : Layout) (flag : Nat → Nat) (incomplete : flag l.flag≠0) :
    getRef l flag=none := by simp [getRef,incomplete]

end ParallelOnceRead
