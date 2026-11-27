import Parallel.ForsTicketProgram
import ForsDriver.ForsIndices
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelForsTicket
open ShakeBatch
set_option allowUnsafeReducibility true in
attribute [local reducible] direct_ticket.closure split_ticket.closure

def treeAt (first active lane : Nat) := first+min lane (active-1)

def sibling (choices : alloc.vec.Vec U32) (a j : U32) (t : Nat) :=
  ForsDriver.sibling choices.slice a t j.val

theorem sibling_room (choices : alloc.vec.Vec U32) (a j : U32) (t : Nat)
    (ha : a.val ≤ 14) (below : j.val < a.val) (small : choices.length ≤ 35) (live : t < choices.length)
    (digit : choices.val[t]!.val < 2^a.val) :
    (sibling choices a j t+1)*2^j.val ≤ 1048576 := by
  have powers : 2^(a.val-j.val)*2^j.val=2^a.val := by rw [←Nat.pow_add];congr 1;omega
  have up : choices.val[t]!.val/2^j.val < 2^(a.val-j.val) := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm,powers]; exact digit
  have pos : 1 < 2^(a.val-j.val) := lt_of_lt_of_le (by decide : 1 < 2^1) (Nat.pow_le_pow_right (by decide) (by omega))
  have flipped := Nat.xor_lt_two_pow up pos
  have global : sibling choices a j t+1 ≤ (t+1)*2^(a.val-j.val) := by
    rw [sibling,ForsDriver.sibling_local _ _ _ _ below,Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add_left (Nat.succ_le_of_lt flipped) _
  have limit := Nat.mul_le_mul_right (2^j.val) global
  rw [Nat.mul_assoc,powers] at limit
  exact limit.trans (by
    have m := Nat.mul_le_mul (show t+1 ≤ 35 by omega) (Nat.pow_le_pow_right (by decide : 0 < 2) ha)
    exact m.trans (by decide))

def rootAt (first active : Usize) (a j : U32) (choices : alloc.vec.Vec U32) (lane : Usize) := do
  let last ← active-1#usize
  let off ← lift (core.cmp.impls.OrdUsize.min lane last)
  let t ← first+off
  let tree ← lift (UScalar.cast .U32 t)
  let level ← a-j
  let start ← tree <<< level
  let digit ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) choices t
  let high ← digit >>> j
  let flipped ← lift (high ^^^ 1#u32)
  start+flipped

theorem root_value (first active lane : Usize) (a j : U32) (choices : alloc.vec.Vec U32)
    (ha : a.val ≤ 14) (below : j.val < a.val) (count : choices.length ≤ 35)
    (enabled : 0 < active.val) (capacity : first.val+active.val ≤ choices.length)
    (digits : ∀ t < choices.length, choices.val[t]!.val < 2^a.val) :
    rootAt first active a j choices lane ⦃ r => r.val=sibling choices a j (treeAt first.val active.val lane.val) ⦄ := by
  let t := treeAt first.val active.val lane.val
  have live : t < choices.length := by
    change first.val+min lane.val (active.val-1)<choices.length
    have := Nat.min_le_right lane.val (active.val-1);omega
  have room := sibling_room choices a j t ha below count live (digits t live)
  have sibEq := ForsDriver.sibling_local choices.slice a t j.val below
  change sibling choices a j t=t*2^(a.val-j.val)+((choices.val[t]!.val/2^j.val)^^^1) at sibEq
  have sibBound : sibling choices a j t < 2^32 := by
    have plus := Nat.le_mul_of_pos_right (sibling choices a j t+1) (Nat.two_pow_pos j.val)
    omega
  unfold rootAt
  step as ⟨last,lv⟩
  simp only [lift,bind_ok]
  let off := core.cmp.impls.OrdUsize.min lane last
  have offv : off.val=min lane.val (active.val-1) := by
    change (if last < lane then last else lane).val=_
    rw [←lv]
    split <;> rename_i e
    · exact (min_eq_right (Nat.le_of_lt e)).symm
    · exact (min_eq_left (Nat.le_of_not_gt e)).symm
  step as ⟨idx,iv⟩
  change idx.val=first.val+off.val at iv
  have same : idx.val=t := by rw [iv,offv];rfl
  have cast : (UScalar.cast .U32 idx).val=t := (cast_u32_usize_val _ (by omega)).trans same
  step as ⟨level,lev⟩
  step with U32.ShiftLeft_spec (UScalar.cast .U32 idx) level (by omega) as ⟨start,shift,_⟩
  have startv : start.val=t*2^(a.val-j.val) := by
    have sh := fors_shl_arith level.val t (by omega) (by omega)
    rw [shift,cast];simpa [U32.size,U32.numBits,lev] using sh.1
  step as ⟨d,read⟩
  have dv : d.val=choices.val[t]!.val := by rw [read,←getElem!_pos,same]
  step as ⟨pref,div,_⟩
  have flip : (pref ^^^ 1#u32).val=((choices.val[t]!.val/2^j.val)^^^1) := by
    simp [UScalar.val_xor,div,dv,Nat.shiftRight_eq_div_pow]
  step as ⟨result,r⟩
  all_goals first | (rw [r,startv,flip];exact sibEq.symm) | scalar_tac

theorem root_bind {α : Type} (first active lane : Usize) (a j : U32) (choices : alloc.vec.Vec U32)
    {x : U32} (run : rootAt first active a j choices lane=ok x) (f : U32 → Result α) :
    (do let last ← active-1#usize
        let off ← lift (core.cmp.impls.OrdUsize.min lane last)
        let t ← first+off
        let tree ← lift (UScalar.cast .U32 t)
        let level ← a-j
        let start ← tree <<< level
        let digit ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) choices t
        let high ← digit >>> j
        let flipped ← lift (high ^^^ 1#u32)
        let result ← start+flipped
        f result) = f x := by
  have joined := congrArg (fun r : Result U32 => r >>= f) run
  simpa only [rootAt,Std.bind_assoc,bind_tc_eq,bind_ok] using joined

theorem direct_ids (N first active : Usize) (a j : U32) (choices : alloc.vec.Vec U32)
    (ha : a.val ≤ 14) (below : j.val < a.val) (count : choices.length ≤ 35)
    (enabled : 0 < active.val) (capacity : first.val+active.val ≤ choices.length)
    (digits : ∀ t < choices.length, choices.val[t]!.val < 2^a.val) :
    core.array.from_fn 3#usize (direct_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (first,active,a,j,choices) ⦃ ids => ∀ l<3, ids[l]!.val=sibling choices a j (treeAt first.val active.val l) ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! 3#usize _ _ (fun l (v : U32) => v.val=sibling choices a j (treeAt first.val active.val l))
  intro l _
  obtain ⟨x,run,value⟩ := spec_imp_exists (root_value first active l a j choices ha below count enabled capacity digits)
  have eq : (direct_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N).call_mut (first,active,a,j,choices) l =
      ok (x,first,active,a,j,choices) :=
    root_bind first active l a j choices run (fun x => ok (x,first,active,a,j,choices))
  rw [eq];simp only [step_simps];exact value

theorem sub_room (root j sub chunk : Nat) (room : (root+1)*2^j ≤ 1048576)
    (lower : sub≤j) (part : chunk<2^(j-sub)) :
    (root*2^(j-sub)+chunk+1)*2^sub≤1048576 := by
  calc
    _ ≤ ((root+1)*2^(j-sub))*2^sub := Nat.mul_le_mul_right _ (by rw [Nat.add_mul,Nat.one_mul];omega)
    _ = (root+1)*2^j := by rw [Nat.mul_assoc,←Nat.pow_add,Nat.sub_add_cancel lower]
    _ ≤ _ := room

theorem split_ids (N first active : Usize) (a j sub delta chunk : U32) (choices : alloc.vec.Vec U32)
    (ha : a.val ≤ 14) (below : j.val < a.val) (count : choices.length ≤ 35)
    (enabled : 0 < active.val) (capacity : first.val+active.val ≤ choices.length)
    (digits : ∀ t < choices.length, choices.val[t]!.val < 2^a.val)
    (lower : sub.val ≤ j.val) (diff : delta.val=j.val-sub.val) (part : chunk.val<2^delta.val) :
    core.array.from_fn 3#usize (split_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (first,active,a,j,choices,delta,chunk) ⦃ ids => ∀ l<3, ids[l]!.val=
        sibling choices a j (treeAt first.val active.val l)*2^delta.val+chunk.val ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! 3#usize _ _ (fun l (v : U32) =>
    v.val=sibling choices a j (treeAt first.val active.val l)*2^delta.val+chunk.val)
  intro l _
  obtain ⟨x,run,value⟩ := spec_imp_exists (root_value first active l a j choices ha below count enabled capacity digits)
  have live : treeAt first.val active.val l.val<choices.length := by
    unfold treeAt; have := Nat.min_le_right l.val (active.val-1);omega
  have room := sibling_room choices a j _ ha below count live (digits _ live)
  rw [←value] at room
  have bound := sub_room x.val j.val sub.val chunk.val room lower (diff ▸ part)
  rw [←diff] at bound
  have small := Nat.le_mul_of_pos_right (x.val*2^delta.val+chunk.val+1) (Nat.two_pow_pos sub.val)
  let after (r : U32) := do
    let id ← r <<< delta
    let v ← id+chunk
    ok (v,first,active,a,j,choices,delta,chunk)
  have eq : (split_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N).call_mut (first,active,a,j,choices,delta,chunk) l = after x :=
    root_bind first active l a j choices run after
  rw [eq];unfold after
  simp only [bind_tc_eq,step_simps]
  step with U32.ShiftLeft_spec x delta (by omega) as ⟨shift,eq,_⟩
  have sh : shift.val=x.val*2^delta.val := by
    rw [eq,Nat.shiftLeft_eq];rw [U32.size_eq]; exact Nat.mod_eq_of_lt (by omega)
  step as ⟨id,res⟩
  rw [res,sh,value]

end slhdsa.ParallelForsTicket
