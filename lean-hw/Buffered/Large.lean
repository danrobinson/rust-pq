import Buffered.Run
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [kernel : Kernel]

private theorem split_pair {α β γ : Type} (x : α × β) (f : α → β → γ) :
    (match x with | (a,b) => f a b) = f x.1 x.2 := by cases x; rfl

private def large {N : Usize} (sk seed : Array U8 N) (idx height : U32) (a tree : address.Adrs) (z : Usize) := do
  let iter ← core.ops.range.RangeInclusive.new 0#usize z
  let indices ← subtree_loop1 iter idx z (Array.repeat 17#usize 0#u32)
  let shift ← height - 3#u32
  let blocks ← 1#u32 <<< shift
  let first ← idx <<< height
  let zeros := Array.repeat N 0#u8
  let rows := Array.repeat 8#usize zeros
  let result ← runBlocks sk seed a tree z blocks first (Array.repeat 17#usize (Array.repeat 16#usize zeros))
    (Array.repeat 17#usize 0#usize) indices (Array.repeat 8#usize tree) rows rows
  let row ← Array.index_usize result z
  Array.index_usize row 0#usize

theorem large_spec {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (idx height : U32) (lo : 3≤height.val) (hi : height.val≤9) (room : (idx.val+1)*2^height.val≤512)
    (process : ProcessAt p sk seed a idx height) :
    subtree sk seed idx height a ⦃ out => bytes out.val =
      Spec.xmssNode (Shake.params p) (bytes sk.val) idx.val height.val (bytes seed.val) (adrsS a) ⦄ := by
  let z := UScalar.cast .Usize height
  have width : z.val=height.val := by dsimp [z]; scalar_tac
  have one : height≠1#u32 := by intro eq; subst height; contradiction
  have two : height≠2#u32 := by intro eq; subst height; contradiction
  have fits : z≤16#usize := by scalar_tac
  unfold subtree
  simp only [bind_ok,show (8#usize != 8#usize)=false from rfl,Bool.false_eq_true,ite_false]
  step as ⟨tree,addr,_⟩
  have okHeight : (UScalar.cast .Usize height ≤ 16#usize) := fits
  simp only [lift,bind_ok,one,two,decide_false,Bool.false_or,okHeight,decide_true,massert,ite_true,ite_false]
  suffices ready : large sk seed idx height a tree z ⦃ out => bytes out.val =
      Spec.xmssNode (Shake.params p) (bytes sk.val) idx.val height.val (bytes seed.val) (adrsS a) ⦄ by
    simp only [large,runBlocks,z,bind_tc_eq,Std.bind_assoc,bind_ok,split_pair] at ready ⊢
    exact ready
  unfold large
  simp only [core.ops.range.RangeInclusive.new,bind_ok]
  step with init_indices idx z _ (by omega) (by simpa only [width] using room) as ⟨indices,initial⟩
  step as ⟨shift,shiftVal⟩
  step as ⟨blocks,blocksVal,_⟩
  step as ⟨first,firstVal,_⟩
  have smallPow : 2^height.val≤512 := (Nat.le_mul_of_pos_left _ (Nat.succ_pos idx.val)).trans room
  have blocksEq : blocks.val=2^(height.val-3) := by
    rw [blocksVal,Nat.shiftLeft_eq,Nat.one_mul]
    rw [Nat.mod_eq_of_lt,shiftVal]
    have h := (Nat.pow_le_pow_right (by decide : 0<2) (show shift.val≤height.val by omega)).trans smallPow
    exact h.trans_lt (by scalar_tac : 512 < U32.size)
  have firstEq : first.val=idx.val*2^height.val := by
    rw [firstVal,Nat.shiftLeft_eq,Nat.mod_eq_of_lt]
    exact (Nat.mul_le_mul_right _ (Nat.le_succ idx.val)).trans_lt (room.trans_lt (by scalar_tac : 512<U32.size))
  step with process tree z blocks first _ (Array.repeat 17#usize 0#usize) indices _ _ _ (by simpa only [address.TREE,Spec.TREE,show (2#u32).val=2 from rfl] using addr)
    width blocksEq firstEq (by intro j hj; rw [Array.repeat_val,List.getElem!_replicate _ (show j<(17#usize).val by change j<17; omega)]; rfl) initial as ⟨buf,root⟩
  step as ⟨row,readRow⟩
  step as ⟨out,readOut⟩
  rw [readOut,←getElem!_pos,readRow,←getElem!_pos]
  exact root

end slhdsa.Buffered
