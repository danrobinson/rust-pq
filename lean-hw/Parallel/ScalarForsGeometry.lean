import Parallel.ScalarForsTicket
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelScalarFors
set_option maxHeartbeats 800000

def sibling (t a j digit : Nat) := t*2^(a-j)+((digit/2^j)^^^1)

theorem sibling_room (t a j digit : Nat) (tree : t<35) (height : a≤14) (below : j<a)
    (selected : digit<2^a) : (sibling t a j digit+1)*2^j≤1048576 := by
  have powers : 2^(a-j)*2^j=2^a := by rw [←Nat.pow_add,Nat.sub_add_cancel below.le]
  have high : digit/2^j<2^(a-j) := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm,powers];exact selected)
  have one : 1<2^(a-j) := lt_of_lt_of_le (by decide : 1<2^1) (Nat.pow_le_pow_right (by decide) (by omega))
  have bound := Nat.xor_lt_two_pow high one
  have total := Nat.mul_le_mul_right (2^j) (show sibling t a j digit+1≤(t+1)*2^(a-j) by
    simp only [sibling,Nat.add_mul,Nat.one_mul];omega)
  rw [Nat.mul_assoc,powers] at total
  exact total.trans ((Nat.mul_le_mul (show t+1≤35 by omega) (Nat.pow_le_pow_right (by decide : 0<2) height)).trans (by decide))

private def recordRoot (t a j digit : U32) := do
  let d ← a-j
  let base ← t <<< d
  let high ← digit >>> j
  let flip ← lift (high ^^^ 1#u32)
  base+flip

private theorem record_spec (t a j digit : U32) (tree : t.val<35) (height : a.val≤14)
    (below : j.val<a.val) (selected : digit.val<2^a.val) :
    recordRoot t a j digit ⦃ r => r.val=sibling t.val a.val j.val digit.val ⦄ := by
  have room := sibling_room _ _ _ _ tree height below selected
  have pos := Nat.le_mul_of_pos_right (sibling t.val a.val j.val digit.val+1) (Nat.two_pow_pos j.val)
  unfold recordRoot
  step as ⟨shift,sv⟩
  step as ⟨base,bv,_⟩
  have start : base.val=t.val*2^(a.val-j.val) := by
    rw [bv,Nat.shiftLeft_eq,Nat.mod_eq_of_lt,sv]
    have low := Nat.le_add_right (t.val*2^(a.val-j.val)) ((digit.val/2^j.val)^^^1)
    change _≤sibling t.val a.val j.val digit.val at low
    rw [sv,U32.size_eq];omega
  step as ⟨high,hv,_⟩
  try simp only [lift,bind_ok]
  have flipped : (high^^^1#u32).val=(digit.val/2^j.val)^^^1 := by simp [UScalar.val_xor,hv,Nat.shiftRight_eq_div_pow]
  have vmax : sibling t.val a.val j.val digit.val ≤ U32.max := by rw [U32.max_eq];omega
  step as ⟨result,r⟩
  all_goals first | (rw [r,start,flipped];rfl) | (rw [start,flipped];exact vmax)

private theorem record_bind {α : Type} (t a j digit : U32) {r : U32} (eq : recordRoot t a j digit=ok r)
    (f : U32 → Result α) : (do
      let d ← a-j
      let base ← t <<< d
      let high ← digit >>> j
      let v ← base+(high ^^^ 1#u32)
      f v) = f r := by
  have h := congrArg (fun x : Result U32 => x >>= f) eq
  simpa only [recordRoot,Std.bind_assoc,bind_tc_eq,bind_ok,lift] using h

theorem direct_geometry (t a j digit : U32) (tree : t.val<35) (height : a.val≤14)
    (below : j.val<a.val) (selected : digit.val<2^a.val) :
    prepare_direct t a j digit ⦃ i z slot => i.val=sibling t.val a.val j.val digit.val ∧ z=j ∧
      slot.val=t.val*(a.val+1)+1+j.val ⦄ := by
  obtain ⟨i,eq,root⟩ := spec_imp_exists (record_spec t a j digit tree height below selected)
  unfold prepare_direct
  try simp only [lift,bind_ok]
  step as ⟨stride,sv⟩
  rw [record_bind t a j digit eq]
  try simp only [lift,bind_ok]
  have shape : stride.val=a.val+1 := by rw [sv];simp
  have cap := Nat.mul_le_mul tree.le (show a.val+1≤15 by omega)
  step as ⟨base,bv⟩
  step as ⟨col,cv⟩
  try simp only [lift,bind_ok]
  step as ⟨slot,v⟩
  all_goals first | exact ⟨root,rfl,by simp [v,cv,bv,shape]⟩ | (simp [shape] at *;scalar_tac)

theorem split_geometry (t a j digit sub : U32) (start chunk : Usize) (tree : t.val<35) (height : a.val≤14)
    (below : j.val<a.val) (selected : digit.val<2^a.val) (lower : sub.val<j.val) (part : chunk.val<2^(j.val-sub.val))
    (slots : start.val+chunk.val ≤ Usize.max) :
    prepare_split t a j digit sub start chunk ⦃ i z slot =>
      i.val=sibling t.val a.val j.val digit.val*2^(j.val-sub.val)+chunk.val ∧ z=sub ∧ slot.val=start.val+chunk.val ⦄ := by
  obtain ⟨i,eq,root⟩ := spec_imp_exists (record_spec t a j digit tree height below selected)
  let value := sibling t.val a.val j.val digit.val
  have room : (value*2^(j.val-sub.val)+chunk.val+1)*2^sub.val≤1048576 := by
    calc
      _ ≤ ((value+1)*2^(j.val-sub.val))*2^sub.val :=
        Nat.mul_le_mul_right _ (by rw [Nat.add_mul,Nat.one_mul];omega)
      _ = (value+1)*2^j.val := by rw [Nat.mul_assoc,←Nat.pow_add,Nat.sub_add_cancel lower.le]
      _ ≤ _ := sibling_room _ _ _ _ tree height below selected
  dsimp only [value] at room
  have limit := Nat.le_mul_of_pos_right (sibling t.val a.val j.val digit.val*2^(j.val-sub.val)+chunk.val+1) (Nat.two_pow_pos sub.val)
  unfold prepare_split
  try simp only [lift,bind_ok]
  step as ⟨stride,sv⟩
  rw [record_bind t a j digit eq]
  step as ⟨shift,sh⟩
  step as ⟨word,pv,_⟩
  have head : word.val=sibling t.val a.val j.val digit.val*2^(j.val-sub.val) := by
    rw [pv,Nat.shiftLeft_eq,root,sh,Nat.mod_eq_of_lt];rw [U32.size_eq];omega
  try simp only [lift,bind_ok]
  have c := cast_u32_usize_val chunk (by omega)
  step as ⟨idx,idxEq⟩
  step as ⟨slot,v⟩
  all_goals first | exact ⟨by rw [idxEq,head,c],rfl,v⟩ | scalar_tac
theorem saturating_eq (t a j digit sub : U32) (start chunk : Usize) (lower : sub.val≤j.val) :
    prepare_saturating t a j digit sub start chunk = prepare_split t a j digit sub start chunk := by
  have sat : (core.num.U32.saturating_sub j sub).val = j.val-sub.val := by
    change (0 ⊔ (j.val-sub.val)) % 2^32 = _
    rw [Nat.max_eq_right (Nat.zero_le _), Nat.mod_eq_of_lt (by have := j.bv.isLt; change j.val < 2^32 at this; omega)]
  have subSpec : (j-sub) ⦃ v => v.val = j.val-sub.val ⦄ := by step <;> scalar_tac
  obtain ⟨v,hv,eq⟩ := spec_imp_exists subSpec
  have val : v=core.num.U32.saturating_sub j sub := UScalar.eq_of_val_eq (eq.trans sat.symm)
  simp [prepare_saturating,prepare_split,hv,val,lift]

end slhdsa.ParallelScalarFors
