import Mathlib.Tactic.IntervalCases
import Std.Tactic.BVDecide

namespace PeerShake.WordBytes

def byte (w : BitVec 64) (i : Nat) := w.extractLsb' (8*i) 8

/-- Native scalar and two-lane vector XOR act independently on the eight bytes of each lane. -/
theorem xor_byte (w b : BitVec 64) (i : Fin 8) :
    byte (w ^^^ b) i = byte w i ^^^ byte b i := BitVec.extractLsb'_xor

/-- PowerPC's big-endian I/O reverses bytes within each 64-bit word. -/
def swap (w : BitVec 64) : BitVec 64 :=
  byte w 0 ++ byte w 1 ++ byte w 2 ++ byte w 3 ++ byte w 4 ++ byte w 5 ++ byte w 6 ++ byte w 7

theorem swap_byte (w : BitVec 64) (i : Fin 8) : byte (swap w) i = byte w (7-i.val) := by
  obtain ⟨i,hi⟩ := i
  interval_cases i <;> simp [swap,byte] <;> bv_decide

end PeerShake.WordBytes
