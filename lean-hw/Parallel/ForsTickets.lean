import Parallel.ForsTicketIndices
import Parallel.ForsTicketNodes
import Parallel.ForsTicketWrites
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelForsTicket
open ShakeBatch
set_option allowUnsafeReducibility true in
attribute [local reducible] direct_ticket.closure split_ticket.closure Kldisp.machine UScalar.cMax
variable [wide : Wide]

theorem direct_ticket_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (choices : alloc.vec.Vec U32) (first : U16) (active height : U8) (stride : Usize)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (ha : p.a.val≤14) (below : height.val<p.a.val) (count : choices.length ≤ 35)
    (enabled : 0 < active.val) (width : active.val≤3) (capacity : first.val+active.val≤choices.length)
    (digits : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (shape : stride.val=p.a.val+1) :
    direct_ticket sk seed a choices p.a first active height stride ⦃ out => ∀ l<active.val,
      out.val[l]!.1.val=(first.val+l)*stride.val+1+height.val ∧
      bytes out.val[l]!.2.val = Spec.forsNode (Shake.params p) (bytes sk.val)
        (ForsDriver.sibling choices.slice p.a (first.val+l) height.val) height.val (bytes seed.val) (adrsS a) ⦄ := by
  let f := UScalar.cast .Usize first
  let n := UScalar.cast .Usize active
  let j := core.convert.num.FromU32U8.from height
  have fv : f.val=first.val := U16.cast_Usize_val_eq _
  have nv : n.val=active.val := U8.cast_Usize_val_eq _
  have jv : j.val=height.val := core.convert.num.FromU32U8.from_val_eq _
  have live (l : Nat) : treeAt f.val n.val l<choices.length := by
    unfold treeAt; have := Nat.min_le_right l (n.val-1);omega
  unfold direct_ticket
  simp only [lift,bind_ok]
  step with direct_ids N f n p.a j choices ha (by omega) count (by omega) (by omega) digits as ⟨ids,valid⟩
  have bounds (l : Nat) (hl : l<3) : (ids.val[l]!.val+1)*2^j.val<2^32 := by
    have id := valid l hl
    simp only [Array.getElem!_Nat_eq] at id
    rw [id]
    have limit := sibling_room choices p.a j _ ha (by omega) count (live l) (digits _ (live l))
    exact lt_of_le_of_lt limit (by decide : 1048576<2^32)
  step with nodes_spec p hp sk seed a ids n j domain (by omega) bounds as ⟨rows,values⟩
  have fit (l : Nat) (hl : l<n.val) : (f.val+l)*stride.val+1+j.val ≤ Usize.max := by
    have lim := Nat.mul_le_mul (show f.val+l≤35 by omega) (show stride.val≤15 by omega)
    have mx : 2^32-1 ≤ Usize.max := by agrind
    omega
  step with direct_writes n stride f j rows _ (by omega) (by omega) fit as ⟨out,writes⟩
  rename_i l hl
  have enabledLane : l<n.val := by omega
  obtain ⟨slot,row⟩ := writes l enabledLane
  have id := valid l (by omega : l<3)
  simp only [Array.getElem!_Nat_eq] at id
  have tv : treeAt f.val n.val l=first.val+l := by unfold treeAt;rw [fv,min_eq_left (by omega)]
  change ids.val[l]!.val=sibling choices p.a j (treeAt f.val n.val l) at id
  rw [row,values l enabledLane,id,tv]
  simpa [sibling,ForsDriver.sibling,fv,jv] using slot

theorem split_ticket_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (choices : alloc.vec.Vec U32) (first : U16) (active height : U8) (sub : U8) (chunk : U32) (base chunks : Usize)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (ha : p.a.val≤14) (below : height.val<p.a.val) (count : choices.length ≤ 35)
    (enabled : 0 < active.val) (width : active.val≤3) (capacity : first.val+active.val≤choices.length)
    (digits : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (lower : sub.val ≤ height.val) (shape : chunks.val=2^(height.val-sub.val))
    (part : chunk.val < chunks.val) (room : base.val+active.val*chunks.val ≤ Usize.max) :
    split_ticket sk seed a choices p.a first active height sub chunk base chunks ⦃ out => ∀ l<active.val,
      out.val[l]!.1.val=base.val+l*chunks.val+chunk.val ∧
      bytes out.val[l]!.2.val = Spec.forsNode (Shake.params p) (bytes sk.val)
        (ForsDriver.sibling choices.slice p.a (first.val+l) height.val * chunks.val+chunk.val) sub.val (bytes seed.val) (adrsS a) ⦄ := by
  let f := UScalar.cast .Usize first
  let n := UScalar.cast .Usize active
  let j := core.convert.num.FromU32U8.from height
  have fv : f.val=first.val := U16.cast_Usize_val_eq _
  have nv : n.val=active.val := U8.cast_Usize_val_eq _
  have jv : j.val=height.val := core.convert.num.FromU32U8.from_val_eq _
  have live (l : Nat) : treeAt f.val n.val l<choices.length := by
    unfold treeAt; have := Nat.min_le_right l (n.val-1);omega
  unfold split_ticket
  simp only [lift,bind_ok]
  let h := core.convert.num.FromU32U8.from sub
  have hv : h.val=sub.val := core.convert.num.FromU32U8.from_val_eq _
  step as ⟨delta,dv⟩
  change delta.val=j.val-h.val at dv
  have splitCount : 2^delta.val=chunks.val := by rw [dv,jv,hv,shape]
  step with split_ids N f n p.a j h delta chunk choices ha (by omega) count (by omega) (by omega) digits
    (by omega) dv (by omega) as ⟨ids,valid⟩
  have bounds (l : Nat) (hl : l<3) : (ids.val[l]!.val+1)*2^h.val<2^32 := by
    have id := valid l hl
    simp only [Array.getElem!_Nat_eq] at id
    rw [id]
    have limit := sibling_room choices p.a j _ ha (by omega) count (live l) (digits _ (live l))
    have lim := sub_room _ j.val h.val chunk.val limit (by omega) (by rw [←dv,splitCount];exact part)
    rw [←dv] at lim;exact lt_of_le_of_lt lim (by decide : 1048576<2^32)
  step with nodes_spec p hp sk seed a ids n h domain (by omega) bounds as ⟨rows,values⟩
  have fit (l : Nat) (hl : l<n.val) : base.val+l*chunks.val+chunk.val≤Usize.max := by
    have lim := Nat.mul_le_mul_right chunks.val (show l+1≤active.val by omega)
    rw [Nat.add_mul,Nat.one_mul] at lim;omega
  step with split_writes n chunk base chunks rows _ (by omega) fit as ⟨out,writes⟩
  rename_i l hl
  have enabledLane : l<n.val := by omega
  obtain ⟨slot,row⟩ := writes l enabledLane
  have id := valid l (by omega : l<3)
  simp only [Array.getElem!_Nat_eq] at id
  have tv : treeAt f.val n.val l=first.val+l := by unfold treeAt;rw [fv,min_eq_left (by omega)]
  change ids.val[l]!.val=sibling choices p.a j (treeAt f.val n.val l)*2^delta.val+chunk.val at id
  rw [row,values l enabledLane,id,tv]
  simpa [sibling,ForsDriver.sibling,fv,jv,hv,splitCount] using slot

end slhdsa.ParallelForsTicket
