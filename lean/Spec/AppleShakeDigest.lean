import Spec.AppleKeccakWitness
import Spec.SlhDsa

namespace LinkedArm.Digest
open Spec Spec.Keccak

/-- The output loop in the linked finish function, specialized to the first rate block. -/
def output (lanes : State) (i : Nat) : Nat → Bytes
  | 0 => []
  | k+1 => ((lanes[i/8]! >>> (8*(i%8))).truncate 8) :: output lanes (i+1) k

private theorem output_eq (lanes : State) (i n : Nat) (h : i+n ≤ 136) :
    output lanes i n = squeeze lanes i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have hne : i ≠ 136 := by omega
    simp only [output, squeeze, if_neg hne, extractByte]
    rw [ih (i+1) (by omega)]

def finish (scratch : Lane → ArmSha3Binary.Registers) (s : State × Nat) (n : Nat) : Bytes :=
  let a := s.1.setIfInBounds (s.2 / 8) (s.1[s.2 / 8]! ^^^ ((31 : Lane) <<< (8*(s.2%8))))
  let b := a.setIfInBounds 16 (a[16]! ^^^ 0x8000000000000000)
  output (linkedConstants.foldl (machineRound scratch) b) 0 n

theorem finish_eq (scratch : Lane → ArmSha3Binary.Registers) (s : State × Nat) (n : Nat)
    (hn : n ≤ 136) : finish scratch s n = squeeze (finalize s) 0 n := by
  unfold finish
  rw [output_eq _ _ _ (by omega), permutation_eq]
  rfl

private theorem feed_cursor (s : State × Nat) (b : Byte) (h : s.2 < 136) :
    (feed s b).2 < 136 := by
  unfold feed
  split <;> simp_all <;> omega

theorem reachable_cursor (bs : Bytes) : (bs.foldl feed initial).2 < 136 := by
  induction bs using List.reverseRecOn with
  | nil => decide
  | append_singleton pre b ih =>
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using feed_cursor _ b ih

/-- The four actual calls in H_msg, under the functional contract for the streaming
    sponge absorb operation. The Mach-O driver checker binds these buffers and their order. -/
theorem hmsg_eq (scratch : Lane → ArmSha3Binary.Registers)
    (absorb : State × Nat → Bytes → State × Nat)
    (habs : ∀ pre b : Bytes, absorb (pre.foldl feed initial) b = (pre ++ b).foldl feed initial)
    (p : Params) (hf : p.family = .shake)
    (hn : p.m ≤ 136) (r seed root msg : Bytes) :
    finish scratch (absorb (absorb (absorb (absorb initial r) seed) root) msg) p.m =
      Hmsg p r seed root msg := by
  rw [show absorb initial r = r.foldl feed initial by simpa using habs [] r,
      habs, habs, habs, finish_eq _ _ _ hn]
  simp [Hmsg, hf, shake256]

end LinkedArm.Digest
