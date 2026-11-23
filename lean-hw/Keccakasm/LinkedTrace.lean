import Keccakasm.Linked

namespace slhdsa.KeccakAsm.Binary
open Spec.Keccak

/-- Architectural data accesses and control transfers. A row is a 64-byte
access at RDI+64*i. The spill is a 64-byte access at RSP-72. Broadcast reads
8 bytes at table+i. RET reads the return address at the incoming RSP. -/
inductive Event where
  | loadRow (i : Nat)
  | storeRow (i : Nat)
  | writeSpill
  | readSpill
  | readConstant (i : Nat)
  | branch (taken : Bool)
  | ret
  deriving DecidableEq, Repr

def Op.accesses (offset : Nat) : Op → List Event
  | .spill _ => [.writeSpill]
  | .xor _ _ .spill => [.readSpill]
  | .xor _ _ .rc => [.readConstant offset]
  | _ => []

/-- Paired register and access semantics, using the operands of each executed instruction. -/
def observedOps (offset : Nat) (rc : Lane) : List Op → Registers → Registers × List Event
  | [], s => (s, [])
  | op::rest, s =>
    let (final, trace) := observedOps offset rc rest (execute rc s op)
    (final, op.accesses offset ++ trace)

private theorem observedOps_eq (off rc program s) :
    observedOps off rc program s = (program.foldl (execute rc) s, program.flatMap (Op.accesses off)) := by
  induction program generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [observedOps, ih, List.foldl_cons, List.flatMap_cons]

def observedRounds (data : Bytes) : List Nat → Registers → Registers × List Event
  | [], s => (s, [])
  | off::rest, s =>
    let (next, accesses) := observedOps off (loadConstant data off) ops s
    let (final, trace) := observedRounds data rest next
    (final, accesses ++ (.branch (decide (off+8 ≠ 192)) :: trace))

def roundTrace (off : Nat) := ops.flatMap (Op.accesses off) ++ [.branch (decide (off+8 ≠ 192))]

private theorem observedRounds_eq (data indices s) :
    observedRounds data indices s =
      ((indices.map (loadConstant data)).foldl loopRound s, indices.flatMap roundTrace) := by
  induction indices generalizing s with
  | nil => rfl
  | cons off rest ih =>
    simp only [observedRounds, observedOps_eq, ih, List.map_cons, List.foldl_cons,
      List.flatMap_cons, roundTrace, loopRound, List.append_assoc, List.cons_append, List.nil_append]

/-- Observe the same accepted complete leaf instruction stream from first load to return. -/
def observedImage (entry table : Nat) (code data : Bytes) (s : Registers) (a : State) :
    Option (State × List Event) := do
  if ¬ (reachableTable entry table ∧ code = imageCode rows ops entry table) then none else
  let indices ← iterations 24 0
  let (final, trace) := observedRounds data indices (load s a)
  return (project final, rows.zipIdx.map (fun q => Event.loadRow q.2) ++ trace ++
    rows.zipIdx.map (fun q => Event.storeRow q.2) ++ [.ret])

def accessTrace := (List.range 25).map Event.loadRow ++ offsets.flatMap roundTrace ++
  (List.range 25).map Event.storeRow ++ [.ret]

/-- All possible matrix contents and scratch register values give exactly this common
sequence, including all 24 branch outcomes, while yielding the FIPS result. -/
theorem image_trace_fips {entry table : Nat} {text data : Bytes}
    (rel : reachableTable entry table) (code : text = imageCode rows ops entry table)
    (rodata : data = roundTable) (s : Registers) (a : State) (shape : a.size = 25) :
    observedImage entry table text data s a = some (permute a, accessTrace) := by
  subst data
  simp only [observedImage, rel, code, and_self, not_true_eq_false, ↓reduceIte, counter_exits]
  change some (project (observedRounds roundTable offsets (load s a)).1, _) = _
  rw [observedRounds_eq, round_constants, rounds_refine, load_project s a shape, Array.foldl_toList]
  rfl

end slhdsa.KeccakAsm.Binary
