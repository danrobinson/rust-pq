import Metal.Completion

namespace MetalCompletion.BridgeWait

inductive Event | endEncoding | commit | waitUntilCompleted | status | releaseHandle
  deriving DecidableEq, Repr

/-- One possible normally returning path through the optimized Objective-C bridge.
The status field records the comparison with the SDK's completed enumerator. -/
structure Path where
  nonnull : Bool
  completed : Option Bool
  events : List Event
  code : Int
  deriving DecidableEq, Repr

def valid (p : Path) : Prop :=
  if p.nonnull then
    ∃ b : Bool, p.completed = some b ∧
      p.events = [.endEncoding,.commit,.waitUntilCompleted,.status,.releaseHandle] ∧
      p.code = bridgeCode b
  else p.completed = none ∧ p.events = [] ∧ p.code = -1

instance (p : Path) : Decidable (valid p) := by unfold valid; infer_instance

theorem readback {α : Type} (p : Path) (h : valid p) (read : Unit → α) :
    (if p.code = 0 then Except.ok (read ()) else Except.error Error.device) =
    (if p.nonnull then afterWait (.submitted (p.completed.getD false)) read
     else .error .device) := by
  cases p with
  | mk present status events code =>
    cases present <;> simp [valid] at h ⊢
    · simp [h.2.2]
    · rcases h with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;> rfl

inductive BarrierEvent | retainHandle | bufferBarrier (scope : Nat) | releaseHandle
  deriving DecidableEq, Repr

structure BarrierPath where
  nonnull : Bool
  concurrent : Option Bool
  events : List BarrierEvent
  deriving DecidableEq, Repr

/-- The ARC retain spans the command property access and the optional encoder
message. Scope one is checked against the target SDK's buffer enumerator. -/
def validBarrier (p : BarrierPath) : Prop :=
  if p.nonnull then
    ∃ b : Bool, p.concurrent = some b ∧
      p.events = [.retainHandle] ++ (if b then [.bufferBarrier 1] else []) ++ [.releaseHandle]
  else p.concurrent = none ∧ p.events = []

instance (p : BarrierPath) : Decidable (validBarrier p) := by unfold validBarrier; infer_instance

end MetalCompletion.BridgeWait
