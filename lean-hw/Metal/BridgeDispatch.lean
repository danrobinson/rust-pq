import Std

namespace MetalBridgeDispatch

/-- Symbolic operands distinguish the Rust handles, inline data pointers,
binding indices, byte lengths and the two dimensions supplied by the caller. -/
inductive Operand
  | command | pipeline | scratch | gridX | groupX
  | handle (i : Nat) | pointer (i : Nat) | length (i : Nat) | index (i : Nat) | literal (n : Nat)
  | encoder (obj : Operand) | state (obj : Operand) | buffer (obj : Operand)
  | size (x y z : Operand)
  deriving DecidableEq, Repr

inductive Selector | pipeline | buffer | inlineBytes | scratch | threads | groups
  deriving DecidableEq, Repr

abbrev Message := Selector × List Operand

def expected (buffers inlineCount : Nat) (groups scratch : Bool) : List Message := Id.run do
  let enc := Operand.encoder .command
  let binds : List Message := (List.range buffers).map fun i =>
    (.buffer,[enc,.buffer (.handle i),.literal 0,.literal i])
  let bytes : List Message := (List.range inlineCount).map fun i =>
    (.inlineBytes,[enc,.pointer i,.length i,.index i])
  let mem : List Message := if scratch then [(.scratch,[enc,.scratch,.literal 0])] else []
  let shape := fun x => Operand.size x (.literal 1) (.literal 1)
  let dispatch := if groups then Selector.groups else Selector.threads
  return [(.pipeline,[enc,.state .pipeline])] ++ binds ++ bytes ++ mem ++
    [(dispatch,[enc,shape .gridX,shape .groupX])]

/-- A certificate on symbolic operands transfers to arbitrary buffer identities,
pointer values, byte lengths, and indices, including repeated binding indices. -/
theorem instantiate {actual : List Message} {n k : Nat} {g s : Bool}
    (certificate : actual = expected n k g s) (interpret : Operand → α) :
    actual.map (fun m => (m.1,m.2.map interpret)) =
      (expected n k g s).map (fun m => (m.1,m.2.map interpret)) :=
  congrArg _ certificate

end MetalBridgeDispatch
