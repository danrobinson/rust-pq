import Parallel.PoolBorrow

namespace ParallelPool.Lease

/-- Distinct allocation lifetimes may reuse the same numeric address. The
projection keeps allocation identity, generation and offset when erasing F. -/
structure Object where
  allocation : Nat
  generation : Nat
  offset : Nat
  address : Nat
  typeId : Nat
  deriving DecidableEq

inductive Value where
  | shared (o : Object)
  | raw (t : Nat) (o : Object)
  | erased (o : Object)
  | code (t : Nat)
  | pair (first second : Value)
  | refTo (v : Value)
  | called (o : Object)
  deriving DecidableEq

/-- The MIR projection follows value-producing instructions only. The enclosing
atomic history supplies the job read from the published cell. -/
inductive Term where
  | arg (i : Nat)
  | addressOf (x : Term)
  | erase (x : Term)
  | trampoline
  | pair (x y : Term)
  | field (x : Term) (i : Nat)
  | localRef (x : Term)
  | load (x : Term)
  | castF (x : Term)
  | shared (x : Term)
  | call (x : Term)
  deriving Repr

def eval (ty : Nat) (args : List Value) : Term → Option Value
  | .arg i => args[i]?
  | .addressOf x => do
    let .shared o ← eval ty args x | none
    return .raw o.typeId o
  | .erase x => do
    let .raw _ o ← eval ty args x | none
    return .erased o
  | .trampoline => some (.code ty)
  | .pair x y => do return .pair (← eval ty args x) (← eval ty args y)
  | .field x i => do
    let .pair left right ← eval ty args x | none
    match i with | 0 => some left | 1 => some right | _ => none
  | .localRef x => do return .refTo (← eval ty args x)
  | .load x => do
    let .refTo v ← eval ty args x | none
    return v
  | .castF x => do
    let .erased o ← eval ty args x | none
    return .raw ty o
  | .shared x => do
    let .raw t o ← eval ty args x | none
    if t=o.typeId then some (.shared o) else none
  | .call x => do
    let .shared o ← eval ty args x | none
    return .called o

structure Program where
  claim : Term
  capture : Term
  wrapper : Term
  indirect : Term
  trampoline : Term

/-- Each boundary takes the actual MIR operands from the preceding stage.
The indirect function pointer determines the monomorphization used to
reconstitute a shared reference from the erased argument. -/
def invoke (p : Program) (original : Object) : Option Value := do
  let job ← eval original.typeId [.shared original] p.claim
  let captures ← eval original.typeId [job] p.capture
  let .pair call data ← eval original.typeId [captures] p.wrapper | none
  let .pair (.code target) erased ← eval original.typeId [call,data] p.indirect | none
  eval target [erased] p.trampoline

def production : Program where
  claim := .pair (.erase (.addressOf (.arg 0))) .trampoline
  capture := .pair (.localRef (.field (.arg 0) 0)) (.localRef (.field (.arg 0) 1))
  wrapper := .pair (.load (.field (.arg 0) 1)) (.load (.field (.arg 0) 0))
  indirect := .pair (.arg 0) (.arg 1)
  trampoline := .call (.shared (.castF (.arg 0)))

theorem exact_object (o : Object) : invoke production o = some (.called o) := by
  simp [invoke,production,eval]

/-- Across reuse, even objects with identical numeric addresses remain
distinguishable through the actual job data and callback. -/
theorem no_address_confusion (x y : Object) (different : x≠y) :
    invoke production x ≠ invoke production y := by
  simp [exact_object,different]

/-- The cast/data-flow equality and asynchronous borrow window compose for
every worker, including an epoch whose final residual counter contains its
panic bit. The later dispatch may reuse the identical numeric address. -/
theorem scoped_invocation (epochs : (e : Nat) → Borrow.Epoch e) (co : Borrow.Coherent epochs)
    (object : Nat → Object) (e w : Nat) (assigned : w < (epochs e).workers) (k : Nat) :
    invoke production (object e) = some (.called (object e)) ∧
    Borrow.HB epochs (.initialize e) (.copyJob e w) ∧
    Borrow.HB epochs (.useClosure e w) (.endBorrow e) ∧
    Borrow.HB epochs (.useClosure e w) (.initialize (e+k+1)) := by
  have window := Borrow.borrow_lifetime epochs co e w assigned
  exact ⟨exact_object _,window.1,window.2.2,Borrow.reuse epochs co e w assigned k⟩

end ParallelPool.Lease
