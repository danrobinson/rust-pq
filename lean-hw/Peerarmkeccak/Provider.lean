import Peerarmkeccak.Xof
import Peerarmkeccak.Top
import Peerarmkeccak.IndexedProof
import Peerarmkeccak.SoftProof

open Spec Spec.Keccak
namespace PeerShake.Backend

attribute [local irreducible] Spec.Keccak.permute Spec.Keccak.extractByte
set_option maxHeartbeats 800000

private def absorb (k : State → State) (a : State) (bs : Bytes) : State :=
  k (bs.foldl Buffer.xorNext (a,0)).1

private def after (k : State → State) (a : State) : Nat → State
  | 0 => a
  | n+1 => after k (k a) n

/-- Every permutation call made while absorbing, padding and squeezing uses the selected kernel. -/
def xof (k : State → State) : Xof Buffer.Buffered where
  empty := Buffer.initialState
  update s part :=
    let f := Buffer.split (s.pending++part)
    ⟨f.blocks.foldl (absorb k) s.state,f.rest⟩
  finish s n :=
    let pendingState := (s.pending.foldl Buffer.xorNext (s.state,0)).1
    let initial := k (xorByte (xorByte pendingState s.pending.length 0x1f) 135 0x80)
    List.ofFn fun i : Fin n => extractByte (after k initial (i.val/136)) (i.val%136)

private theorem after_fips (a : State) (n : Nat) :
    after permute a n = Buffer.afterBlocks a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact ih _

private theorem xof_fips : xof permute = Buffer.provider := by
  have h : after permute = Buffer.afterBlocks := funext fun a => funext fun n => after_fips a n
  unfold xof Buffer.provider Buffer.readBytes
  rw [h]
  rfl

open Aeneas Aeneas.Std Result in
private def packed (a : State) (valid : a.size=25) : Aeneas.Std.Array U64 25#usize :=
  Aeneas.Std.Array.from (a.toList.map (fun w => ⟨w⟩)) (by simpa using valid)

private theorem packed_words (a : State) (valid : a.size=25) :
    slhdsa.Keccak.words (packed a valid) = a := by simp [packed,slhdsa.Keccak.words,List.map_map]

open Aeneas Aeneas.Std in
private noncomputable def observe (m : Result (Aeneas.Std.Array U64 25#usize)) : State := by
  classical
  exact if h : ∃ s : State, WP.spec m (fun out => slhdsa.Keccak.words out=s) then h.choose else #[]

open Aeneas Aeneas.Std in
private theorem observe_eq {m : Result (Aeneas.Std.Array U64 25#usize)} {s : State}
    (h : WP.spec m (fun out => slhdsa.Keccak.words out=s)) : observe m=s := by
  classical
  let has : ∃ w : State, WP.spec m (fun out => slhdsa.Keccak.words out=w) := ⟨s,h⟩
  rw [observe,dite_eq_left has]
  obtain ⟨o,h₁,h₂⟩ := WP.spec_exists (WP.spec_and has.choose_spec h)
  exact h₁.symm.trans h₂

open Aeneas Aeneas.Std in
/-- Rust's Keccak state always has 25 words. The extension to other logical array
lengths uses the verified scalar kernel and is never selected by a Rust state. -/
noncomputable def arm (a : State) : State :=
  if h : a.size=25 then
    observe (PeerArmRust.backends.aarch64_sha3.p1600_armv8_sha3 (packed a h) 24#usize)
  else PeerKeccak.SoftLinux.permute a

theorem arm_fips (a : State) : arm a = permute a := by
  unfold arm
  split
  next h =>
    apply observe_eq
    simpa only [packed_words] using PeerKeccak.Arm.single (packed a h)
  next => exact PeerKeccak.SoftLinux.permute_fips a

inductive Implementation where
  | armSha3 | appleScalar | scalar | indexed

noncomputable def kernel : Implementation → State → State
  | .armSha3 => arm
  | .appleScalar => PeerKeccak.Soft.permute
  | .scalar => PeerKeccak.SoftLinux.permute
  | .indexed => PeerKeccak.Indexed.permute

theorem kernel_fips (impl : Implementation) (a : State) : kernel impl a = permute a := by
  cases impl
  · exact arm_fips a
  · exact PeerKeccak.Soft.permute_fips a
  · exact PeerKeccak.SoftLinux.permute_fips a
  · exact PeerKeccak.Indexed.permute_fips a

/-- Byte-level correctness of the published provider with its concrete permutation backend. -/
def correct (impl : Implementation) : Correct (xof (kernel impl)) := by
  rw [show kernel impl = permute from funext (kernel_fips impl), xof_fips]
  exact Buffer.providerCorrect

#print axioms correct
end PeerShake.Backend
