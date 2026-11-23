import Parent256.Batch
import Slhdsa.Proofs.InPlace
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Parent
abbrev Rows := Slice (Array U8 16#usize)

abbrev Processed := @InPlace.Processed 16#usize
abbrev advance := @InPlace.advance 16#usize

theorem children_intact (expected : Nat → Spec.Bytes) (before buf : Rows) (done i : Nat)
    (h : Processed expected before buf done) (hi : done ≤ i)
    (bound : 2*i+1 < before.length) : children buf i = children before i := by
  have left := h.2 (2*i) (by omega)
  have right := h.2 (2*i+1) bound
  simp only [if_neg (show ¬2*i < done by omega)] at left
  simp only [if_neg (show ¬2*i+1 < done by omega)] at right
  simp only [children,left,right]

end slhdsa.X86.Parent
