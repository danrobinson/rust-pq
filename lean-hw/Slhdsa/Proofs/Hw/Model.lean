import Slhdsa.Proofs.Sha256Core
open Aeneas Aeneas.Std Result

/-! A pure description of what the hardware kernel computes on one block, in
terms of the instruction model (`Arm.lean`). Both kernels of
`rust/src/sha256.rs`, module `hw`, are proved equal to it: `compress_block`
directly, and a step of a chain (`lane_step`) up to the rounds it has cached
and the half-step it skips. -/

namespace slhdsa
open Spec.SHA256

/-- The four elements of a vector, lowest first. -/
def vwords (v : Arm.V) : List Word := [v.e0, v.e1, v.e2, v.e3]

/-- The vector of the four words `l[i]`, …, `l[i + 3]`. -/
def vOf (l : List Word) (i : Nat) : Arm.V := ⟨l[i]!, l[i + 1]!, l[i + 2]!, l[i + 3]!⟩

/-- The vector of the four big-endian words at bytes `B[i]`, …, `B[i + 15]`. -/
def beV (B : Spec.Bytes) (i : Nat) : Arm.V :=
  ⟨word B i, word B (i + 4), word B (i + 8), word B (i + 12)⟩

/-- The state of the kernel between steps: the working variables, and the
four most recent schedule vectors, the one that step `i` consumes at index
`i % 4`. -/
structure KState where
  abcd : Arm.V
  efgh : Arm.V
  m : List Arm.V

/-- Step `i` of the kernel: rounds `4i`, …, `4i + 3`, and, for `i < 12`, the
schedule words `W[4i + 16]`, …, `W[4i + 19]`. -/
def kstep (s : KState) (i : Nat) : KState :=
  let w := Arm.ADD s.m[i % 4]! (vOf K (4 * i))
  { abcd := Arm.SHA256H s.abcd s.efgh w
    efgh := Arm.SHA256H2 s.efgh s.abcd w
    m := if i < 12 then
        s.m.set (i % 4)
          (Arm.SHA256SU1 (Arm.SHA256SU0 s.m[i % 4]! s.m[(i + 1) % 4]!) s.m[(i + 2) % 4]!
            s.m[(i + 3) % 4]!)
      else s.m }

/-- The sixteen steps of the kernel from working variables `abcd0`, `efgh0`
on the block whose words are `m0`, …, `m3`. -/
def kcompress (abcd0 efgh0 m0 m1 m2 m3 : Arm.V) : KState :=
  (List.range 16).foldl kstep ⟨abcd0, efgh0, [m0, m1, m2, m3]⟩

end slhdsa
