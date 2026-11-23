import Spec.Sha256

namespace slhdsa.RcSlhSha2
open Spec

/-- Logical contents of an eager buffer. `sent` records what compression
received, in order, and `pending` records bytes preceding the cursor. -/
structure Buffer where
  sent : Bytes
  pending : Bytes

def Buffer.bytes (b : Buffer) := b.sent ++ b.pending

def splitAligned (width : Nat) (sent data : Bytes) : Buffer :=
  let whole := width * (data.length / width)
  ⟨sent ++ data.take whole, data.drop whole⟩

def feed (width : Nat) (b : Buffer) (data : Bytes) : Buffer :=
  let rem := width - b.pending.length
  if data.length < rem then ⟨b.sent, b.pending ++ data⟩
  else if b.pending.length != 0 then
    splitAligned width (b.sent ++ b.pending ++ data.take rem) (data.drop rem)
  else splitAligned width b.sent data

theorem split_bytes (width : Nat) (sent data : Bytes) :
    (splitAligned width sent data).bytes = sent ++ data := by
  simp [splitAligned,Buffer.bytes,List.append_assoc]

theorem feed_bytes (width : Nat) (b : Buffer) (data : Bytes) :
    (feed width b data).bytes = b.bytes ++ data := by
  dsimp only [feed]
  split
  · simp [Buffer.bytes,List.append_assoc]
  split
  · rw [split_bytes]; simp [Buffer.bytes,List.append_assoc]
  next h =>
    have zero : b.pending = [] := List.length_eq_zero_iff.mp (by simpa using h)
    rw [split_bytes]; simp [Buffer.bytes,zero]

theorem split_remainder (width : Nat) (sent data : Bytes) :
    (splitAligned width sent data).pending.length = data.length % width := by
  simp only [splitAligned,List.length_drop]
  have h := Nat.mod_add_div data.length width
  omega

theorem feed_shape (width : Nat) (positive : 0 < width) (b : Buffer)
    (shape : b.pending.length < width) (data : Bytes) : (feed width b data).pending.length < width := by
  dsimp only [feed]
  split
  · simp only [List.length_append]; omega
  split <;> simp only [split_remainder] <;> apply Nat.mod_lt _ positive

theorem feed_many (width : Nat) (b : Buffer) (parts : List Bytes) :
    (parts.foldl (feed width) b).bytes = b.bytes ++ parts.flatten := by
  induction parts generalizing b with
  | nil => simp
  | cons x xs ih => simp [ih,feed_bytes,List.append_assoc]

theorem split_complete (width : Nat) (sent data : Bytes) (aligned : width ∣ sent.length) :
    width ∣ (splitAligned width sent data).sent.length := by
  have le : width * (data.length / width) ≤ data.length := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  simp only [splitAligned, List.length_append,List.length_take,Nat.min_eq_left le]
  exact Nat.dvd_add aligned (Nat.dvd_mul_right _ _)

theorem feed_complete (width : Nat) (b : Buffer) (shape : b.pending.length < width)
    (aligned : width ∣ b.sent.length) (data : Bytes) : width ∣ (feed width b data).sent.length := by
  dsimp only [feed]
  split
  · exact aligned
  next full =>
    split
    · apply split_complete
      rw [List.length_append,List.length_append,List.length_take,Nat.min_eq_left (Nat.le_of_not_gt full)]
      have align : b.sent.length + b.pending.length + (width-b.pending.length) = b.sent.length + width := by omega
      rw [align]; exact Nat.dvd_add aligned (Nat.dvd_refl _)
    · exact split_complete _ _ _ aligned

end slhdsa.RcSlhSha2
