import Slhdsa.Proofs.Hw.Wrappers

/-! Runs the Lean meaning of the intrinsic wrappers on the cases recorded
from a processor in `vectors/arm-wrappers.txt`, which
`cargo test --features hw-sha2` checks against the processor it runs on.

The wrappers are defined in `Slhdsa/FunsExternal.lean` over the instruction
model `Arm.lean`, as functions into Aeneas's `Result`, which cannot be run.
`Slhdsa/Proofs/Hw/Wrappers.lean` proves each of them equal to a bounds check
around a plain function, and those plain functions are what runs here.

    lake env lean --run ArmTest.lean ../vectors/arm-wrappers.txt
-/

open slhdsa

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def hexNat (s : String) : Nat := s.toList.foldl (fun n c => 16 * n + hexVal c) 0

def words (s : String) : List (BitVec 32) := (s.splitOn ",").map fun w => BitVec.ofNat 32 (hexNat w)

def bytesOf (s : String) : List (BitVec 8) :=
  let rec go : List Char → List (BitVec 8)
    | hi :: lo :: rest => BitVec.ofNat 8 (16 * hexVal hi + hexVal lo) :: go rest
    | _ => []
  go s.toList

def vec (s : String) : Arm.V :=
  match words s with
  | [a, b, c, d] => ⟨a, b, c, d⟩
  | _ => ⟨0, 0, 0, 0⟩

/-- One line of the record, `name args = result`, against the plain function
that `Slhdsa/Proofs/Hw/Wrappers.lean` proves the wrapper's definition to be.
The recorded cases are all within the bounds the wrappers check. -/
def check (line : String) : Bool :=
  match line.splitOn " " with
  | ["zero", "=", r] => (⟨0, 0, 0, 0⟩ : Arm.V) == vec r
  | ["pair", a, b, "=", r] => (⟨BitVec.ofNat 32 (hexNat a), BitVec.ofNat 32 (hexNat b), 0, 0⟩ : Arm.V) == vec r
  | ["load_words", ws, i, "=", r] =>
    let w := words ws
    4 ≤ w.length && i.toNat! ≤ w.length - 4 && wLoadWords w i.toNat! == vec r
  | ["store_words", a, e, "=", r] => wStoreWords (vec a) (vec e) == words r
  | ["load_be", bs, i, "=", r] =>
    let b := bytesOf bs
    16 ≤ b.length && i.toNat! ≤ b.length - 16 && wLoadBe b i.toNat! == vec r
  | ["store_be", bs, i, v, "=", r] =>
    let b := bytesOf bs
    16 ≤ b.length && i.toNat! ≤ b.length - 16 && wStoreBe b i.toNat! (vec v) == bytesOf r
  | ["shr16", a, "=", r] => Arm.USHR (vec a) 16 == vec r
  | ["shl16", a, "=", r] => Arm.SHL (vec a) 16 == vec r
  | ["add", a, b, "=", r] => Arm.ADD (vec a) (vec b) == vec r
  | ["or", a, b, "=", r] => Arm.ORR (vec a) (vec b) == vec r
  | ["and", a, b, "=", r] => Arm.AND (vec a) (vec b) == vec r
  | ["ext2", a, b, "=", r] => Arm.EXT2 (vec a) (vec b) == vec r
  | ["ext3", a, b, "=", r] => Arm.EXT3 (vec a) (vec b) == vec r
  | ["sha256su0", a, b, "=", r] => Arm.SHA256SU0 (vec a) (vec b) == vec r
  | ["sha256h", a, b, c, "=", r] => Arm.SHA256H (vec a) (vec b) (vec c) == vec r
  | ["sha256h2", a, b, c, "=", r] => Arm.SHA256H2 (vec a) (vec b) (vec c) == vec r
  | ["sha256su1", a, b, c, "=", r] => Arm.SHA256SU1 (vec a) (vec b) (vec c) == vec r
  | _ => false

def main (args : List String) : IO UInt32 := do
  let path := args.headD "../vectors/arm-wrappers.txt"
  let lines := (← IO.FS.lines path).toList.filter (· ≠ "")
  let mut bad := 0
  let mut n := 1
  for l in lines do
    if !check l then
      bad := bad + 1
      if bad ≤ 5 then IO.println s!"MISMATCH at line {n}: {l}"
    n := n + 1
  IO.println s!"{lines.length} cases, {bad} mismatches"
  return (if bad == 0 && lines.length > 0 then 0 else 1)
