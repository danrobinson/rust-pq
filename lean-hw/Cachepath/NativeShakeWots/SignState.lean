import Cachepath.NativeShakeWots.Chains
import Shakebatch.WotsSign
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots.Signer
open ShakeBatch Shakeopt.WotsRefill NativeVerify NativeVerify.Wots
set_option linter.concreteInstances false
variable [machine : Machine]

abbrev Secrets := Array (Array U64 4#usize) 67#usize
abbrev Signature := alloc.vec.Vec U8

def Block (sig : Signature) (n i : Nat) (b : Nat) := sig.val[i*n+b]!.bv

def Words {N : Usize} (secret : Array U64 4#usize) (value : Spec.Bytes) : Prop :=
  ∃ b : Array U8 N, bytes b.val=value ∧ ∀ k<N.val/8, secret.val[k]!.bv=inputWord b.val k

structure Schedule (N : Usize) where
  digits : Slice U32
  n : Usize
  order : Array Usize 67#usize
  total : Usize
  secrets : Secrets
  source : Nat → Spec.Bytes
  small : N.val≤32
  align : N.val%8=0
  count : n.val=N.val/8
  bound : digits.length≤67
  size : total.val≤67
  queued : ∀ i<total.val, let id := order.val[i]!.val
                          id<digits.length ∧ 0<digits.val[id]!.val ∧ digits.val[id]!.val≤15 ∧
                          Words (N:=N) secrets.val[id]! (source id)

def Schedule.ids {N : Usize} (c : Schedule N) := (c.order.val.take c.total.val).map UScalar.val
def Schedule.ending {N : Usize} (c : Schedule N) (id : Nat) := c.digits.val[id]!.val

theorem Schedule.length {N : Usize} (c : Schedule N) : c.ids.length=c.total.val := by simp [Schedule.ids,c.size]

theorem Schedule.get {N : Usize} (c : Schedule N) (i : Nat) (h : i<c.total.val) : c.ids[i]! = c.order.val[i]!.val := by
  have valid : i<c.ids.length := by rw [c.length];exact h
  rw [getElem!_pos c.ids i valid]
  simp only [Schedule.ids,List.getElem_map,List.getElem_take]
  rw [getElem!_pos c.order.val i (by simp;have := c.size;omega)]

structure Matches {N : Usize} (len : Nat) (g : RefillState) (cursor : Nat) (sig : Signature)
    (next active : Usize) (ids : Ids) (steps ends : Steps) (v : LaneValues machine.width) (s : State) : Prop where
  act : active.val=g.active
  idx : next.val=g.next
  room : active.val≤machine.width.val
  ident : ∀ l<active.val, ids.val[l]!.val=g.laneId l
  step : ∀ l<active.val, steps.val[l]!.val=g.laneStep l
  inside : ∀ l<active.val, g.laneId l<len
  valid : ∀ l<active.val, g.laneStep l<g.laneEnd l
  endsAt : ∀ l<active.val, ends.val[l]!.val=g.laneEnd l
  bound : ∀ l<active.val, g.laneEnd l≤15
  prepared : ∀ l<active.val, l<cursor → Packed N v l (g.laneVal l)
  pending : ∀ l<active.val, cursor≤l → digest N s l=g.laneVal l
  lenEq : sig.length=len*N.val
  output : ∀ i<len, ∀ b<N.val, Block sig N.val i b=(g.out i)[b]!

theorem block_store {N : Usize} (blob : Array U8 N) (sig out : Signature) (len id : Nat)
    (size : sig.length=len*N.val) (valid : id<len) (written : out.val=sig.val.setSlice! (id*N.val) blob.val) :
    out.length=len*N.val ∧ ∀ i<len, ∀ b<N.val,
      Block out N.val i b = if i=id then (bytes blob.val)[b]! else Block sig N.val i b := by
  constructor
  · change out.val.length=_;rw [written,List.length_setSlice!];exact size
  intro i hi b hb
  unfold Block
  rw [written]
  have cap : id*N.val+N.val≤sig.val.length := by
    change _ ≤ sig.length
    rw [size,← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ valid
  by_cases h : i=id
  · subst i
    rw [ite_eq_left rfl,List.getElem!_setSlice!_middle _ _ _ _ (by simp;omega),
      Nat.add_sub_cancel_left,bytes_getElem! _ _ (by simpa using hb),getElem!_pos blob.val b (by simpa using hb)]
  · rw [ite_eq_right h]
    by_cases left : i < id
    · have lt : (i+1)*N.val ≤ id*N.val := Nat.mul_le_mul_right _ left
      rw [Nat.succ_mul] at lt
      rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
    · have lt : (id+1)*N.val ≤ i*N.val := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at lt
      rw [List.getElem!_setSlice!_suffix _ _ _ _ (by simp;omega)]

end slhdsa.NativeShakeWots.Signer
