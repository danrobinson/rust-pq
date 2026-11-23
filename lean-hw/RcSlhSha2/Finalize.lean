import RcSlhSha2.Buffer
import RcSlhSha2.Digest

namespace slhdsa.RcSlhSha2
open Spec

/-- The eager implementation uses the last physical byte for its cursor.
An underfull update writes strictly before that byte; filling the block
overwrites the cursor before the block is passed to compression. -/
theorem eager_offsets (width pos n : Nat) (w : width=64 ∨ width=128) (valid : pos<width) :
    pos < 256 ∧ (n < width-pos → pos+n ≤ width-1) ∧ pos+(width-pos)=width := by
  rcases w with rfl | rfl <;> omega

def Buffer.valid (b : Buffer) (width : Nat) := width ∣ b.sent.length ∧ b.pending.length < width

theorem feed_valid (w : Nat) (hw : 0 < w) (b : Buffer) (valid : b.valid w) (data : Bytes) :
    (feed w b data).valid w := ⟨feed_complete _ _ valid.2 valid.1 _,feed_shape _ hw _ valid.2 _⟩

def filled (w : Nat) (parts : List Bytes) : Buffer := parts.foldl (feed w) ⟨[],[]⟩

theorem filled_valid (w : Nat) (hw : 0 < w) (parts : List Bytes) : (filled w parts).valid w := by
  have inv (b : Buffer) (hb : b.valid w) : (parts.foldl (feed w) b).valid w := by
    induction parts generalizing b with
    | nil => exact hb
    | cons x xs ih => exact ih _ (feed_valid _ hw _ hb _)
  exact inv _ ⟨dvd_zero _,hw⟩

theorem filled_bytes (w : Nat) (parts : List Bytes) : (filled w parts).bytes = parts.flatten := by
  rw [filled, feed_many]
  rfl

/-- `pos` and the SHA core's full-block counter are read from the final
buffer state, just as in the two pinned SHA core finalizers. -/
def Buffer.finalize (b : Buffer) (w suffix : Nat) : Bytes :=
  let free := w - b.pending.length - 1
  let zeros := if free < suffix then free + (w-suffix) else free-suffix
  b.bytes ++ [0x80#8] ++ List.replicate zeros 0#8 ++
    toByte (8 * (b.pending.length + w * (b.sent.length / w))) suffix

theorem finalize_eq (w suffix : Nat) (hw : 0 < w) (b : Buffer) (hb : b.valid w) :
    b.finalize w suffix = padded w suffix b.bytes := by
  obtain ⟨⟨count,hcount⟩,small⟩ := hb
  have len : b.bytes.length = b.pending.length + w * count := by
    simp [Buffer.bytes,hcount,Nat.add_comm]
  simp [Buffer.finalize,padded,len,hcount,Nat.add_mul_div_left _ _ hw,
    Nat.mod_eq_of_lt small,Nat.div_eq_of_lt small,Nat.mul_div_cancel_left _ hw]

theorem finalized_parts (w suffix : Nat) (hw : 0 < w) (parts : List Bytes) :
    (filled w parts).finalize w suffix = padded w suffix parts.flatten := by
  rw [finalize_eq w suffix hw _ (filled_valid _ hw _),filled_bytes]

end slhdsa.RcSlhSha2
