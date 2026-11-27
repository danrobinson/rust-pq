import Spec.ArmRateBlocks
import Shakebatch.Oneblock

namespace Spec.Keccak.FusedStream
open ArmRateBlocks

/-- The lane update in the fused WOTS public-key compression loop. The cursor counts words. -/
def absorb (s : State × Nat) (w : Lane) : State × Nat :=
  let next := s.1.setIfInBounds s.2 (s.1[s.2]! ^^^ w)
  if s.2 = 16 then (permute next,0) else (next,s.2+1)

private def blocks (tip : Bytes) (n : Nat) : List Bytes :=
  (List.range n).map fun w => (tip.drop (8*w)).take 8

private theorem flattenBlocks (tip : Bytes) (n : Nat) :
    (blocks tip n).flatten = tip.take (8*n) := by
  induction n with
  | zero => simp [blocks]
  | succ n ih =>
    simp only [blocks,List.range_succ,List.map_append,List.map_cons,List.map_nil,
      List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
    rw [← blocks,ih, Nat.mul_succ,List.take_add]

/-- A complete WOTS chain tip crosses any intervening SHAKE rate boundary at the same
word as the byte-oriented FIPS 202 sponge, including a tip ending at a boundary. -/
theorem absorb_tip (tip : Bytes) (n : Nat) (aligned : tip.length = 8*n)
    (a : State) (size : a.size = 25) (pos : Nat) (rate : pos < 17) :
    let out := (List.range n).foldl (fun s w => absorb s (messageWord tip w)) (a,pos)
    (out.1,8*out.2) = tip.foldl feed (a,8*pos) := by
  have width : ∀ w ∈ blocks tip n, w.length = 8 := by
    intro w mem
    obtain ⟨j,within,rfl⟩ := List.mem_map.mp mem
    have lt := List.mem_range.mp within
    simp; omega
  have eq := foldWords permute (fun _ => rfl) (blocks tip n) width a size pos rate
  rw [flattenBlocks,← aligned,List.take_length] at eq
  simpa only [blocks,List.foldl_map,ArmRateBlocks.word,absorb,messageWord] using eq

/-- Apply the SHAKE delimiter and high padding bit as two sequential word stores.
This also covers both stores targeting word 16. -/
def finish (a : State) (pos : Nat) : State :=
  let tagged := a.setIfInBounds pos (a[pos]! ^^^ 0x1f)
  permute (tagged.setIfInBounds 16 (tagged[16]! ^^^ (1 <<< 63)))

theorem finish_eq (a : State) (pos : Nat) : finish a pos = finalize (a,8*pos) := by
  simp [finish,finalize,xorByte,Nat.mul_comm]

end Spec.Keccak.FusedStream
