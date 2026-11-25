-- Generated from the Apple dispatch and row load/store loops by scripts/check-apple-hybrid.py.
import Cachepath.AppleHybridRounds
namespace slhdsa.AppleHybrid
open Spec.Keccak
abbrev Route := Fin 8 × List (Kind × Lane)

private def program0 : List (Kind × Lane) := []
private def program1 : List (Kind × Lane) := [(.neon, 0x1), (.neon, 0x8082), (.neon, 0x800000000000808a), (.neon, 0x8000000080008000), (.neon, 0x808b), (.neon, 0x80000001), (.neon, 0x8000000080008081), (.neon, 0x8000000000008009), (.neon, 0x8a), (.neon, 0x88), (.neon, 0x80008009), (.neon, 0x8000000a), (.neon, 0x8000808b), (.neon, 0x800000000000008b), (.neon, 0x8000000000008089), (.neon, 0x8000000000008003), (.neon, 0x8000000000008002), (.neon, 0x8000000000000080), (.neon, 0x800a), (.neon, 0x800000008000000a), (.neon, 0x8000000080008081), (.neon, 0x8000000000008080), (.neon, 0x80000001), (.neon, 0x8000000080008008)]
private def program2 : List (Kind × Lane) := [(.sha3, 0x1), (.sha3, 0x8082), (.sha3, 0x800000000000808a), (.sha3, 0x8000000080008000), (.sha3, 0x808b), (.sha3, 0x80000001), (.sha3, 0x8000000080008081), (.sha3, 0x8000000000008009), (.sha3, 0x8a), (.sha3, 0x88), (.sha3, 0x80008009), (.sha3, 0x8000000a), (.sha3, 0x8000808b), (.sha3, 0x800000000000008b), (.sha3, 0x8000000000008089), (.sha3, 0x8000000000008003), (.sha3, 0x8000000000008002), (.sha3, 0x8000000000000080), (.sha3, 0x800a), (.sha3, 0x800000008000000a), (.sha3, 0x8000000080008081), (.sha3, 0x8000000000008080), (.sha3, 0x80000001), (.sha3, 0x8000000080008008)]
private def program3 : List (Kind × Lane) := [(.inplace, 0x1), (.inplace, 0x8082), (.inplace, 0x800000000000808a), (.inplace, 0x8000000080008000), (.inplace, 0x808b), (.inplace, 0x80000001), (.inplace, 0x8000000080008081), (.inplace, 0x8000000000008009), (.inplace, 0x8a), (.inplace, 0x88), (.inplace, 0x80008009), (.inplace, 0x8000000a), (.inplace, 0x8000808b), (.inplace, 0x800000000000008b), (.inplace, 0x8000000000008089), (.inplace, 0x8000000000008003), (.inplace, 0x8000000000008002), (.inplace, 0x8000000000000080), (.inplace, 0x800a), (.inplace, 0x800000008000000a), (.inplace, 0x8000000080008081), (.inplace, 0x8000000000008080), (.inplace, 0x80000001), (.inplace, 0x8000000080008008)]
private def program4 : List (Kind × Lane) := [(.scalar, 0x1), (.scalar, 0x8082), (.scalar, 0x800000000000808a), (.scalar, 0x8000000080008000), (.scalar, 0x808b), (.scalar, 0x80000001), (.scalar, 0x8000000080008081), (.scalar, 0x8000000000008009), (.scalar, 0x8a), (.scalar, 0x88), (.scalar, 0x80008009), (.scalar, 0x8000000a), (.scalar, 0x8000808b), (.scalar, 0x800000000000008b), (.scalar, 0x8000000000008089), (.scalar, 0x8000000000008003), (.scalar, 0x8000000000008002), (.scalar, 0x8000000000000080), (.scalar, 0x800a), (.scalar, 0x800000008000000a), (.scalar, 0x8000000080008081), (.scalar, 0x8000000000008080), (.scalar, 0x80000001), (.scalar, 0x8000000080008008)]

/-- Dispatch indices 0–8 call permute_active; index 9 calls permute. -/
def schedule (n : Fin 10) (sha3 : Bool) : _root_.Array Route :=
  match n.val, sha3 with
  | 0, false => #[(0, program0), (1, program0), (2, program0), (3, program0), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 0, true => #[(0, program0), (1, program0), (2, program0), (3, program0), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 1, false => #[(0, program1), (1, program1), (2, program0), (3, program0), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 1, true => #[(0, program2), (1, program2), (2, program0), (3, program0), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 2, false => #[(0, program1), (1, program1), (2, program0), (3, program0), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 2, true => #[(0, program2), (1, program2), (2, program0), (3, program0), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 3, false => #[(0, program1), (1, program1), (2, program1), (3, program1), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 3, true => #[(0, program3), (1, program3), (2, program4), (3, program0), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 4, false => #[(0, program1), (1, program1), (2, program1), (3, program1), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 4, true => #[(0, program2), (1, program2), (2, program2), (3, program2), (4, program0), (5, program0), (6, program0), (7, program0)]
  | 5, false => #[(0, program1), (1, program1), (2, program1), (3, program1), (4, program1), (5, program1), (6, program0), (7, program0)]
  | 5, true => #[(0, program3), (1, program3), (2, program3), (3, program3), (4, program4), (5, program0), (6, program0), (7, program0)]
  | 6, false => #[(0, program1), (1, program1), (2, program1), (3, program1), (4, program1), (5, program1), (6, program0), (7, program0)]
  | 6, true => #[(0, program3), (1, program3), (2, program4), (3, program3), (4, program3), (5, program4), (6, program0), (7, program0)]
  | 7, false => #[(0, program1), (1, program1), (2, program1), (3, program1), (4, program1), (5, program1), (6, program1), (7, program1)]
  | 7, true => #[(0, program3), (1, program3), (2, program3), (3, program3), (4, program4), (5, program2), (6, program2), (7, program0)]
  | 8, false => #[(0, program1), (1, program1), (2, program1), (3, program1), (4, program1), (5, program1), (6, program1), (7, program1)]
  | 8, true => #[(0, program3), (1, program3), (2, program3), (3, program3), (4, program3), (5, program3), (6, program4), (7, program4)]
  | 9, false => #[(0, program1), (1, program1), (2, program1), (3, program1), (4, program1), (5, program1), (6, program1), (7, program1)]
  | 9, true => #[(0, program3), (1, program3), (2, program3), (3, program3), (4, program3), (5, program3), (6, program4), (7, program4)]
  | _, _ => #[]

end slhdsa.AppleHybrid
