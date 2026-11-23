import Spec.Correctness

namespace slhdsa.PeerCall
open Spec

private def readBE (width : Nat) (buf : Bytes) :=
  toInt (List.replicate (width-buf.length) 0#8 ++ buf) % 2^(8*width)

/-- When checked_shl(64) returns None, wrapping subtraction from zero
produces the full 64-bit mask. -/
private def treeMask (bits : Nat) :=
  if bits < 64 then 2^bits-1 else 2^64-1

def splitResult (p : Params) (d : Bytes) : Bytes × Nat × Nat :=
  let bits := p.h - p.hp
  let treeSize := (bits+7)/8
  let leafSize := (p.hp+7)/8
  let tree := (d.drop p.mdBytes).take treeSize
  let leaf := (d.drop (p.mdBytes+treeSize)).take leafSize
  (d.take p.mdBytes, readBE 8 tree &&& treeMask bits, readBE 4 leaf &&& (2^p.hp-1))

private theorem zeros (n : Nat) (b : Bytes) : toInt (List.replicate n 0#8 ++ b) = toInt b := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,toInt] using ih

theorem split_correct (p : Params) (valid : p.Valid) (d : Bytes) :
    splitResult p d = (d.take p.mdBytes,digestTree p d,digestLeaf p d) := by
  have hp := h_div_d p valid
  have mask : treeMask (p.h-p.hp) = 2^(p.h-p.hp)-1 := by
    unfold treeMask
    split
    · rfl
    next h => rw [show p.h-p.hp=64 by have t := valid.tree_le; omega]
  have t : 2^(p.h-p.hp) ∣ 2^64 := pow_dvd_pow _ valid.tree_le
  have l : 2^p.hp ∣ 2^32 := pow_dvd_pow _ (by have h := valid.hp_le; omega)
  simp only [splitResult,readBE,zeros,mask,digestTree,digestLeaf,Params.treeBytes,Params.leafBytes,hp,
    Nat.and_two_pow_sub_one_eq_mod,show 8*8=64 by decide,show 8*4=32 by decide,
    Nat.mod_mod_of_dvd _ t,Nat.mod_mod_of_dvd _ l]

end slhdsa.PeerCall
