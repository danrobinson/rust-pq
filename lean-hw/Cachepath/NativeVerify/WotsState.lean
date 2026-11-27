import Cachepath.NativeVerify.WotsHash
import Cachepath.NativeVerify.WotsOutput
import Cachepath.NativeVerify.WotsCompact
import Cachepath.NativeVerify.WotsInit
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch Shakeopt.WotsRefill
set_option linter.concreteInstances false
variable [machine : Machine]

def Packed (N : Usize) (v : LaneValues machine.width) (l : Nat) (msg : Spec.Bytes) : Prop :=
  ∃ b : Array U8 N, bytes b.val=msg ∧ ∀ k < N.val/8, laneWord v l k=inputWord b.val k

def digest (N : Usize) (s : Matrix machine.width) (l : Nat) :=
  Spec.Keccak.squeeze (ShakeBatch.lane s l) 0 N.val

theorem extract_digest (N : Usize) (s : Matrix machine.width) (lane : Usize)
    (small : N.val≤32) (align : N.val%8=0) (valid : lane.val<machine.width.val) :
    extract_lane N s 0#usize lane ⦃ out => bytes out.val=digest N s lane.val ⦄ := by
  apply WP.spec_mono (extract_lane_spec N s 0#usize lane align (by scalar_tac) valid)
  intro out cells
  unfold digest
  rw [Spec.Keccak.squeeze_short _ _ _ (by omega)]
  apply List.ext_getElem
  · simp [bytes]
  · intro b hl hr
    have bn : b < N.val := by simpa using hl
    simp only [bytes,List.getElem_map,List.getElem_range,Nat.zero_add]
    rw [← getElem!_pos,cells b bn,stateByte,le_byte _ _ (by omega)]
    simp only [Spec.Keccak.extractByte,ShakeBatch.lane,Spec.Keccak.ofFnAt _ _ (by omega : b/8 < 25),cell,
      UScalar.ofNatCore_val_eq,Nat.zero_add]

theorem digest_congr {N : Usize} (small : N.val≤32) (align : N.val%8=0)
    {a b : Matrix machine.width} {l j : Nat} (h : ∀ k < N.val/8, cell a k l=cell b k j) :
    digest N a l=digest N b j := by
  unfold digest
  rw [Spec.Keccak.squeeze_short _ _ _ (by omega),Spec.Keccak.squeeze_short _ _ _ (by omega)]
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  simp only [Nat.zero_add,Spec.Keccak.extractByte,ShakeBatch.lane,Spec.Keccak.ofFnAt _ _ (by omega : i/8 < 25),
    h (i/8) (by omega)]

theorem packed_of_digest {N : Usize} (s : Matrix machine.width) (v : LaneValues machine.width) (l : Nat)
    (small : N.val≤32) (align : N.val%8=0) (valid : l<machine.width.val)
    (word : ∀ j<N.val/8, laneWord v l j=cell s j l) : Packed N v l (digest N s l) := by
  obtain ⟨buf,output,words⟩ := digest_words (N:=N) s (by omega) align
  exact ⟨buf.val[l]!,output l valid,fun k hk => (word k hk).trans (words l valid k hk).symm⟩

theorem packed_congr {N : Usize} {v w : LaneValues machine.width} {l j : Nat} {msg : Spec.Bytes}
    (old : Packed N v l msg) (words : ∀ k<N.val/8, laneWord w j k=laneWord v l k) : Packed N w j msg := by
  obtain ⟨b,byte,h⟩ := old
  exact ⟨b,byte,fun k hk => (words k hk).trans (h k hk)⟩

abbrev Tips (N : Usize) := Array (Array U8 N) 67#usize
abbrev Ids := Array Usize machine.width
abbrev Steps := Array U32 machine.width
abbrev State := Matrix machine.width

/-- Already visited lanes hold their result in the saved four-word slot. The remaining
    lanes hold their current result in the transposed Keccak output. -/
structure Matches {N : Usize} (len : Nat) (abstract : RefillState)
    (cursor : Nat) (tips : Tips N) (next active : Usize) (ids : Ids) (steps : Steps)
    (v : LaneValues machine.width) (s : State) : Prop where
  act : active.val=abstract.active
  idx : next.val=abstract.next
  room : active.val≤machine.width.val
  ident : ∀ l<active.val, ids.val[l]!.val=abstract.laneId l
  step : ∀ l<active.val, steps.val[l]!.val=abstract.laneStep l
  inside : ∀ l<active.val, abstract.laneId l<len
  valid : ∀ l<active.val, abstract.laneStep l<15
  ends : ∀ l<active.val, abstract.laneEnd l=15
  prepared : ∀ l<active.val, l<cursor → Packed N v l (abstract.laneVal l)
  pending : ∀ l<active.val, cursor≤l → digest N s l=abstract.laneVal l
  output : ∀ i<len, bytes tips.val[i]!.val=abstract.out i

end slhdsa.NativeVerify.Wots
