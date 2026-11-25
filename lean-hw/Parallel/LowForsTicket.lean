import Parallel.LowForsRows
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelLowFors
open ShakeBatch NativeVerify
variable [machine : Machine] [host : Host machine] [wide : Wide]
set_option allowUnsafeReducibility true in
attribute [local reducible] ticket.closure ticket.closure_1

theorem ticket_spec {N} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (addr : address.Adrs)
    (choices : alloc.vec.Vec U32) (first : U16) (active low : U8) (stride : Usize)
    (correct : ActiveCorrect machine host.perm)
    (domain : addr.typ=address.FORS_TREE ∧ addr.word2=0#u32 ∧ addr.word3=0#u32)
    (ha : p.a.val≤14) (count : choices.length≤35) (digits : ∀ t<choices.length, choices.val[t]!.val<2^p.a.val)
    (enabled : 0<active.val) (width : active.val≤machine.width.val) (capacity : first.val+active.val≤choices.length)
    (height : low.val≤p.a.val) (narrow : machine.width≠8#usize ∨ low.val≤3) (shape : stride.val=p.a.val+1) :
    ticket sk seed addr choices p.a first active low stride ⦃ out =>
      Fields first.val active.val stride.val (low.val+1) (field p sk seed addr choices) out ⦄ := by
  let f := UScalar.cast .Usize first
  let n := UScalar.cast .Usize active
  let h := core.convert.num.FromU32U8.from low
  have fv : f.val=first.val := U16.cast_Usize_val_eq _
  have nv : n.val=active.val := U8.cast_Usize_val_eq _
  have hv : h.val=low.val := core.convert.num.FromU32U8.from_val_eq _
  unfold ticket
  simp only [lift,bind_ok]
  step with absolute_indices N f n p.a choices ha count (by omega) (by omega) digits as ⟨ids,index⟩
  have positions (i : Nat) (hi : i<machine.width.val) :
      ids.val[i]!.val=absolute choices p.a (ParallelForsTicket.treeAt f.val n.val i) := by
    simpa only [Array.getElem!_Nat_eq] using index i hi
  step with secrets_spec p hp sk seed addr ids n (by omega) correct as ⟨secret,rows⟩
  let init := alloc.vec.Vec.new (Usize × Array U8 N)
  have empty : init.length=0 := by rfl
  have mx : 2^32-1≤Usize.max := by agrind
  have fit (l : Nat) (hl : l<n.val) : (f.val+l)*stride.val≤Usize.max := by
    have lim := Nat.mul_le_mul (show f.val+l≤35 by omega) (show stride.val≤15 by omega)
    omega
  step with secret_writes n f stride init secret (by omega) (by omega) (by omega) fit as ⟨journal,writes⟩
  have start : Fields f.val n.val stride.val 1 (field p sk seed addr choices) journal := by
    apply extend f.val n.val stride.val 0 _ init journal secret (by simp [Fields,empty])
    · simpa only [Nat.add_zero] using writes
    · intro l hl
      have t : ParallelForsTicket.treeAt f.val n.val l=f.val+l := by
        unfold ParallelForsTicket.treeAt;rw [min_eq_left (by omega)]
      rw [rows l hl,positions l (by omega),t];rfl
  apply WP.spec_mono (rounds_spec p hp sk seed addr choices f n stride h ids journal correct domain ha count digits
    (by omega) (by omega) (by omega) (by omega) (by simpa only [hv] using narrow) shape positions start)
  intro out result;simpa only [fv,nv,hv] using result
end slhdsa.ParallelLowFors
