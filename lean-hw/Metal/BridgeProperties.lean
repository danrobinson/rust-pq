import Std

namespace MetalBridgeProperties

inductive Value | incoming | previous (offset width : Nat)
  deriving DecidableEq
inductive Event | retain (v : Value) | write (offset width : Nat) (v : Value)
  | release (v : Value) | result (v : Value) | clear (offset : Nat)
  deriving DecidableEq
structure Field where
  offset : Nat
  width : Nat
  strong : Bool
  deriving DecidableEq

def validAccess (f : Field) (getter setter : List Event) : Prop :=
  let old := Value.previous f.offset f.width
  let store := Event.write f.offset f.width .incoming
  getter = [.result old] ∧ setter =
    if f.strong then [.retain .incoming, store, .release old] else [store]

instance (f : Field) (r w : List Event) : Decidable (validAccess f r w) := by
  unfold validAccess; infer_instance

/-- All physical field bytes are distinct, and the destructor clears every
strong slot exactly once. Clearing an Objective-C strong slot releases its object. -/
def validClass (fields : List Field) (destructor : List Event) : Prop :=
  (fields.flatMap fun f => (List.range f.width).map (f.offset + ·)).Nodup ∧
    destructor.Perm ((fields.filter Field.strong).map fun f => Event.clear f.offset)

instance (fs : List Field) (d : List Event) : Decidable (validClass fs d) := by
  unfold validClass; infer_instance

/-- A non-nil strong slot contributes one reference to its object. Other
references can include other fields of the same wrapper. -/
def held [DecidableEq α] (slot : Option α) (obj : α) : Nat :=
  if slot = some obj then 1 else 0

/-- Under ARC's retain/release semantics, the compiled order is safe for
self-assignment, replacing an object and setting or clearing a nil slot. -/
theorem replace_count [DecidableEq α] (outside : α → Nat) (old new : Option α) (obj : α) :
    let beforeRelease := outside obj + held old obj + held new obj
    held old obj ≤ beforeRelease ∧ beforeRelease - held old obj = outside obj + held new obj := by
  dsimp
  omega

theorem destroy_count [DecidableEq α] (outside : α → Nat) (old : Option α) (obj : α) :
    outside obj + held old obj - held old obj = outside obj := by omega

end MetalBridgeProperties
