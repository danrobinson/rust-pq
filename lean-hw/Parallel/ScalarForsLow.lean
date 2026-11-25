import Parallel.ScalarForsLowProgram
import Parallel.ScalarForsGeometry
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelScalarFors
set_option maxHeartbeats 1200000

abbrev Journal (N : Usize) := Array (Usize × Array U8 N) 14#usize

def Rows {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (t h digit base count : Nat) (rows : Journal N) :=
  ∀ j<count, rows.val[j]!.1.val=base+1+j ∧ bytes rows.val[j]!.2.val=Spec.forsNode (Shake.params p)
    (bytes sk.val) (sibling t h j digit) j (bytes seed.val) (adrsS a)

section
variable [host : Host]

def GoodNodes {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) :=
  ∀ i j : U32, j.val≤14 → (i.val+1)*2^j.val≤1048576 →
    node sk i j seed a ⦃ out => bytes out.val=Spec.forsNode (Shake.params p)
      (bytes sk.val) i.val j.val (bytes seed.val) (adrsS a) ⦄

private theorem low_rows {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (t h digit low : U32) (base : Usize) (journal : Journal N) (nodes : GoodNodes p sk seed a)
    (tree : t.val<35) (height : h.val≤14) (selected : digit.val<2^h.val) (bound : low.val≤h.val)
    (position : base.val=t.val*(h.val+1)) :
    low_ticket_loop ⟨0#u32,low⟩ sk seed a t h journal digit base ⦃ rows => Rows p sk seed a t.val h.val digit.val base.val low.val rows ⦄ := by
  unfold low_ticket_loop
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Journal N => low.val-q.1.start.val)
    (inv := fun q => q.1.end=low ∧ q.1.start.val≤low.val ∧ Rows p sk seed a t.val h.val digit.val base.val q.1.start.val q.2)
  · rintro ⟨it,cur⟩ ⟨stop,lim,prior⟩
    simp only at stop lim prior ⊢
    unfold low_ticket_loop.body
    by_cases more : it.start.val < it.end.val
    · have live : it.start.val < low.val := stop ▸ more
      have below : it.start.val<h.val := by omega
      have room := sibling_room _ _ _ _ tree height below selected
      have small := Nat.le_mul_of_pos_right (sibling t.val h.val it.start.val digit.val+1) (Nat.two_pow_pos it.start.val)
      step with core.iter.range.IteratorRange.next_U32_some_spec it more as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      step as ⟨q,qv,_⟩
      try simp only [lift,bind_ok]
      have flip : (q^^^1#u32).val=(digit.val/2^it.start.val)^^^1 := by simp [UScalar.val_xor,qv,Nat.shiftRight_eq_div_pow]
      step as ⟨shift,sv⟩
      step as ⟨offset,ov,_⟩
      have pos : offset.val=t.val*2^(h.val-it.start.val) := by
        rw [ov,Nat.shiftLeft_eq,sv,Nat.mod_eq_of_lt];rw [U32.size_eq]
        unfold sibling at small room;omega
      have safe : offset.val+(q^^^1#u32).val≤U32.max := by rw [pos,flip,U32.max_eq];unfold sibling at small room;omega
      step as ⟨idx,iv⟩
      have idxEq : idx.val=sibling t.val h.val it.start.val digit.val := by rw [iv,pos,flip];rfl
      step with nodes idx it.start (by omega) (idxEq ▸ room) as ⟨v,val⟩
      have cap := Nat.mul_le_mul tree.le (show h.val+1≤15 by omega)
      step as ⟨head,pv⟩
      try simp only [lift,bind_ok]
      step as ⟨slot,slotVal⟩
      try simp only [lift,bind_ok]
      step as ⟨out,put⟩
      try simp only [step_simps]
      refine ⟨ends.trans stop,by omega,?_,by omega⟩
      intro k hk
      rw [put,Array.set_val_eq]
      simp only [U32.cast_Usize_val_eq]
      by_cases eq : k=it.start.val
      · subst k
        rw [ShakeBatch.setSame _ _ _ (by simp;omega)]
        exact ⟨by simp [slotVal,pv],by rw [val,idxEq]⟩
      · rw [ShakeBatch.setOther _ _ _ _ (Ne.symm eq)]
        exact prior k (by omega)
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      have eq : it.start.val=low.val := by rw [stop] at more;omega
      simpa only [eq] using prior
  · exact ⟨rfl,Nat.zero_le _,by intro j hj;exact False.elim (Nat.not_lt_zero _ hj)⟩

def LowValues {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (t h digit low : Nat) (out : (Usize × Array U8 N) × Journal N) :=
  out.1.1.val=t*(h+1) ∧ bytes out.1.2.val=Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) (t*2^h+digit) ∧
    Rows p sk seed a t h digit (t*(h+1)) low out.2

theorem low_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (choices : alloc.vec.Vec U32) (t h low : U32) (stride : Usize) (journal : Journal N)
    (nodes : GoodNodes p sk seed a) (existsDigit : t.val<choices.length) (tree : t.val<35) (height : h.val≤14)
    (selected : choices.val[t.val]!.val<2^h.val) (bound : low.val≤h.val) (size : stride.val=h.val+1) :
    low_ticket sk seed a choices t h low stride journal ⦃ out => LowValues p sk seed a t.val h.val choices.val[t.val]!.val low.val out ⦄ := by
  unfold low_ticket
  simp only [lift,bind_ok]
  step as ⟨digit,read⟩
  rw [←getElem!_pos] at read
  simp only [U32.cast_Usize_val_eq] at read
  have cap := Nat.mul_le_mul tree.le (show h.val+1≤15 by omega)
  have maxBase := Nat.mul_le_mul tree.le (Nat.pow_le_pow_right (by decide : 0<2) height)
  have pow : 2^h.val≤16384 := Nat.pow_le_pow_right (by decide) height
  step as ⟨base,bv⟩
  have position : base.val=t.val*(h.val+1) := by simp [bv,size]
  step as ⟨shifted,sv,_⟩
  have shift : shifted.val=t.val*2^h.val := by rw [sv,Nat.shiftLeft_eq,Nat.mod_eq_of_lt];rw [U32.size_eq];omega
  step as ⟨idx,iv⟩
  step with Shake.fors_sk_gen_spec p hp as ⟨secret,val⟩
  step with low_rows p sk seed a t h digit low base journal nodes tree height (read ▸ selected) bound position as ⟨out,rows⟩
  try simp only [step_simps]
  exact ⟨position,by rw [val,iv,shift,read],by simpa [position,read] using rows⟩

end
end slhdsa.ParallelScalarFors
