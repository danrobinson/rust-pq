namespace slhdsa.Armwide.Transitions

/-- Origins of the seven native register fields and the two arithmetic update counts. -/
structure Register where
  x : Nat
  xb : Nat
  head : Nat
  chain : Nat
  cur : Nat
  advanced : Nat
  left : Nat
  consumed : Nat
  phase : Nat
  deriving DecidableEq, Inhabited

/-- Symbolic destination chain and both halves of the digest written there. -/
structure Event where
  chain : Nat
  x : Nat
  xb : Nat
  deriving DecidableEq, Inhabited

structure Snapshot where
  kept : List Register
  writes : List Event
  deriving DecidableEq, Inhabited

structure HashCall where
  head : Nat
  chain : Nat
  counter : Nat
  increment : Nat
  deriving DecidableEq, Inhabited

structure HashTrace where
  origin : Nat
  calls : List HashCall
  deriving DecidableEq, Inhabited

end slhdsa.Armwide.Transitions
