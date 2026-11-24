import Keccakasm.Binary

namespace slhdsa.KeccakAsm.Binary
open Spec.Keccak
set_option maxRecDepth 65536

/-- The prologue and epilogue map each of the 25 state rows to the same register. -/
def rows : List Reg := [24, 8, 13, 2, 30, 14, 12, 20, 15, 0, 19, 10, 17, 4, 9, 21, 18, 23, 5, 1, 22, 11, 16, 6, 3]

/-- The instructions between the loop head and the counter update. `imageCode`
re-encodes all operands and every instruction byte of the accepted release kernel. -/
def ops : List Op := [
  .spill 30,
  .mov 26 19,
  .tern 26 21 22 150,
  .tern 26 14 24 150,
  .mov 25 10,
  .tern 25 18 11 150,
  .tern 25 12 8 150,
  .mov 27 17,
  .tern 27 23 16 150,
  .tern 27 20 13 150,
  .mov 28 4,
  .tern 28 5 6 150,
  .tern 28 15 2 150,
  .mov 29 9,
  .tern 29 1 3 150,
  .tern 29 0 30 150,
  .rol 30 28 1,
  .xor 30 30 (.reg 25),
  .rol 25 25 1,
  .xor 31 29 (.reg 25),
  .rol 25 29 1,
  .xor 29 25 (.reg 27),
  .rol 25 27 1,
  .xor 25 25 (.reg 26),
  .rol 26 26 1,
  .xor 26 28 (.reg 26),
  .xor 17 30 (.reg 17),
  .xor 7 30 (.reg 16),
  .xor 27 30 (.reg 20),
  .xor 28 30 (.reg 23),
  .xor 13 30 (.reg 13),
  .xor 5 29 (.reg 5),
  .xor 2 29 (.reg 2),
  .xor 4 29 (.reg 4),
  .xor 6 29 (.reg 6),
  .xor 15 29 (.reg 15),
  .xor 19 31 (.reg 19),
  .xor 29 31 (.reg 24),
  .xor 22 31 (.reg 22),
  .xor 24 31 (.reg 14),
  .xor 30 31 (.reg 21),
  .xor 12 25 (.reg 12),
  .xor 8 25 (.reg 8),
  .rol 12 12 44,
  .rol 31 17 43,
  .mov 16 9,
  .rol 9 5 21,
  .xor 3 26 (.reg 3),
  .rol 20 3 14,
  .rol 14 2 28,
  .xor 0 26 (.reg 0),
  .rol 23 0 20,
  .rol 19 19 3,
  .xor 0 25 (.reg 18),
  .rol 18 0 45,
  .rol 0 7 61,
  .rol 7 8 1,
  .xor 2 25 (.reg 10),
  .rol 10 27 6,
  .rol 17 4 25,
  .xor 1 26 (.reg 1),
  .rol 4 1 8,
  .rol 8 22 18,
  .xor 1 26 .spill,
  .rol 21 1 27,
  .rol 22 24 36,
  .rol 24 2 10,
  .rol 5 28 15,
  .rol 1 6 56,
  .rol 27 13 62,
  .rol 28 15 55,
  .xor 2 26 (.reg 16),
  .rol 16 2 39,
  .rol 6 30 41,
  .xor 2 25 (.reg 11),
  .rol 3 2 2,
  .mov 2 9,
  .tern 2 20 29 210,
  .mov 30 20,
  .tern 30 29 12 210,
  .tern 29 12 31 210,
  .mov 11 12,
  .tern 11 31 9 210,
  .mov 13 31,
  .tern 13 9 20 210,
  .mov 20 19,
  .tern 20 18 0 210,
  .mov 15 18,
  .tern 15 0 14 210,
  .tern 0 14 23 210,
  .tern 14 23 19 210,
  .mov 12 23,
  .tern 12 19 18 210,
  .mov 19 7,
  .tern 19 10 17 210,
  .mov 9 8,
  .tern 9 7 10 210,
  .tern 10 17 4 210,
  .tern 17 4 8 210,
  .tern 4 8 7 210,
  .mov 8 11,
  .mov 18 22,
  .tern 18 24 5 210,
  .mov 23 24,
  .tern 23 5 1 210,
  .tern 5 1 21 210,
  .tern 1 21 22 210,
  .tern 21 22 24 210,
  .mov 22 27,
  .tern 22 28 16 210,
  .mov 11 28,
  .tern 11 16 6 210,
  .tern 16 6 3 210,
  .tern 6 3 27 210,
  .xor 24 29 .rc,
  .tern 3 27 28 210]

def project (s : Registers) : State := (rows.map fun r => s r).toArray

def load (s : Registers) (a : State) : Registers :=
  rows.zipIdx.foldl (fun t (r,i) => write t r a[i]!) s

def loopRound (s : Registers) (rc : Lane) : Registers := ops.foldl (execute rc) s

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem loopRound_refines (s : Registers) (rc : Lane) :
    project (loopRound s rc) = roundCode (project s) rc := by rfl

set_option maxRecDepth 65536 in
theorem load_project (s : Registers) (a : State) (h : a.size = 25) : project (load s a) = a := by
  apply Array.ext (by simpa [project,rows] using h.symm)
  intro i hi ha
  have bound : i < 25 := by simpa [project,rows] using hi
  rw [← getElem!_pos a i ha]
  interval_cases i <;> rfl

theorem rounds_refine (s : Registers) (cs : List Lane) :
    project (cs.foldl loopRound s) = cs.foldl round (project s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl_cons, ih, loopRound_refines, round_fips]

def roundTable : Bytes := constants.toList.flatMap fun c => littleEndian c.toNat 8

/-- Little-endian 64-bit memory read at the byte index in RCX. -/
def loadConstant (table : Bytes) (offset : Nat) : Lane :=
  BitVec.ofNat 64 ((List.range 8).foldl (fun acc i =>
    acc + (table[offset+i]!.toNat <<< (8*i))) 0)

/-- Counter starts at zero, then ADD 8; CMP 192; JNE. A missing exit yields none. -/
def iterations : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel+1, offset =>
    if offset+8 = 192 then some [offset]
    else (iterations fuel (offset+8)).map (offset :: ·)

def offsets := (List.range 24).map (8 * ·)

theorem counter_exits : iterations 24 0 = some offsets := by decide
theorem reads_in_bounds : offsets.all (fun i => i+8 ≤ roundTable.length) = true := by decide
theorem round_constants : offsets.map (loadConstant roundTable) = constants.toList := by decide

/-- Execute the linked loop on one lane using its byte table and the observed
counter schedule. All other vector-register lanes execute these same instructions. -/
def runLane (table : Bytes) (s : Registers) (a : State) : Option State := do
  let indices ← iterations 24 0
  return project ((indices.map (loadConstant table)).foldl loopRound (load s a))

theorem runLane_fips (s : Registers) (a : State) (h : a.size = 25) :
    runLane roundTable s a = some (permute a) := by
  rw [runLane, counter_exits]
  change some (project ((offsets.map (loadConstant roundTable)).foldl loopRound (load s a))) = _
  rw [round_constants, rounds_refine, load_project s a h, Array.foldl_toList]
  rfl

theorem linked_permutation_fips (regs : Fin 8 → Registers) (input : Fin 8 → State)
    (shape : ∀ i, (input i).size = 25) :
    (fun i => runLane roundTable (regs i) (input i)) = fun i => some (permute (input i)) :=
  funext fun i => runLane_fips _ _ (shape i)

/-- A restricted executable-image semantics. Matching includes the signed pointer
range, all prefix and operand bits, loop target, RET and the entire function extent. -/
def reachableTable (entry table : Nat) : Prop :=
  let leaEnd := entry + (rows.zipIdx.flatMap fun (r,i) => rowMove false r i).length + 9
  let disp : Int := (table : Int) - leaEnd
  disp ≥ -(2^31 : Int) ∧ disp < 2^31

instance (entry table : Nat) : Decidable (reachableTable entry table) := by
  unfold reachableTable
  infer_instance

def runImage (entry table : Nat) (text data : Bytes) (s : Registers) (a : State) : Option State :=
  if reachableTable entry table ∧ text = imageCode rows ops entry table then runLane data s a
  else none

theorem image_fips {entry table : Nat} {text data : Bytes}
    (rel : reachableTable entry table) (code : text = imageCode rows ops entry table)
    (rodata : data = roundTable) (regs : Fin 8 → Registers) (input : Fin 8 → State)
    (shape : ∀ i, (input i).size = 25) :
    (fun i => runImage entry table text data (regs i) (input i)) =
      fun i => some (permute (input i)) := by
  simpa [runImage, rel, code, rodata] using linked_permutation_fips regs input shape

end slhdsa.KeccakAsm.Binary
