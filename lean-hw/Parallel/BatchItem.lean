import Facade.Suite
import Parallel.Batch

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelBatchItem

structure Item where
  msg : Slice Std.U8
  sig : Slice Std.U8
  ctx : Slice Std.U8
  pk : Slice Std.U8

instance : Inhabited Item :=
  let empty : Slice U8 := Slice.from [] (by simp)
  ⟨⟨empty,empty,empty,empty⟩⟩

set_option maxRecDepth 4096

/-- The shared body of the four extracted verification closures. -/
def item (family : Spec.HashFamily) {N : Std.Usize} (c : params.Params) (tupled_args : Item) :
    Result Bool := do
  let i := Slice.len tupled_args.pk
  let i1 ← 2#usize * N
  if i = i1 then
    Suite.verify family N c tupled_args.msg tupled_args.sig tupled_args.ctx tupled_args.pk
  else ok false

def verdict (family : Spec.HashFamily) (p : params.Params) (i : Item) :=
  decide (i.pk.length = 2*p.n.val) &&
    Spec.slhVerify (Suite.view family p) (bytes i.msg.val) (bytes i.sig.val) (bytes i.ctx.val) (bytes i.pk.val)

theorem item_spec (family : Spec.HashFamily) {N : Usize} (p : params.Params) (hp : PN p N) (i : Item)
    (room : Room i.msg.length (msgSlack N.val+257)) :
    item family (N:=N) p i = ok (verdict family p i) := by
  have width := hp.le32
  unfold item verdict
  obtain ⟨n,mul,vs⟩ := spec_imp_exists (show 2#usize*N ⦃ r => r.val=2*N.val ⦄ by step <;> scalar_tac)
  simp only [mul,bind_ok,hp.n_eq]
  by_cases fit : i.pk.len=n
  · have size : i.pk.length=2*N.val := by change i.pk.len.val=_; rw [fit,vs]
    simp only [fit,ite_true,size,decide_true,Bool.true_and]
    obtain ⟨b,returned,rfl⟩ := spec_imp_exists (Suite.api_verify_spec family p hp i.msg i.sig i.ctx i.pk size room)
    exact returned
  · have size : i.pk.length≠2*N.val := by
      intro eq
      exact fit (UScalar.eq_of_val_eq (eq.trans vs.symm))
    simp [fit,size]

/-- Observe the Boolean returned by the extracted item callback. Under the message
size hypothesis, `item_spec` establishes that the callback always returns. -/
noncomputable def accepted (family : Spec.HashFamily) (N : Usize) (p : params.Params) (i : Item) : Bool := by
  classical exact decide (item family (N:=N) p i = ok true)

theorem accepted_spec (family : Spec.HashFamily) {N : Usize} (p : params.Params) (hp : PN p N) (i : Item)
    (room : Room i.msg.length (msgSlack N.val+257)) :
    accepted family N p i = verdict family p i := by
  classical
  simp only [accepted,item_spec family p hp i room]
  cases verdict family p i <;> simp

noncomputable abbrev atItem (family : Spec.HashFamily) (N : Usize) (p : params.Params)
    (items : Slice Item) (j : Nat) := accepted family N p items.val[j]!

/-- Actual callback values for every in-range claim fix the order of all outputs
after a normally drained dispatch, for any relative completion times. -/
theorem each (family : Spec.HashFamily) {N : Usize} (p : params.Params) (hp : PN p N)
    (items : Slice Item) (k : Nat) (done : List Nat)
    (room : ∀ j < items.length, Room items.val[j]!.msg.length (msgSlack N.val+257))
    (trace : ParallelSigning.Trace items.length k [] done) (drained : items.length < k)
    (j : Nat) (hj : j < items.length) :
    ParallelBatch.results (atItem family N p items) done j = verdict family p items.val[j]! := by
  rw [ParallelBatch.verify_each trace drained _ j hj]
  exact accepted_spec family p hp _ (room j hj)

/-- An early false result only needs one rejecting item. The concrete callback
fixes what constitutes rejection for each item, including an ill-sized key. -/
theorem all (family : Spec.HashFamily) {N : Usize} (p : params.Params) (hp : PN p N)
    (items : Slice Item) (k : Nat) (flag : Bool)
    (room : ∀ j < items.length, Room items.val[j]!.msg.length (msgSlack N.val+257))
    (trace : ParallelBatch.Run items.length (atItem family N p items) k (fun _ => False) flag)
    (stopped : flag=true → items.length≤k) :
    flag=true ↔ ∀ j < items.length, verdict family p items.val[j]! = true := by
  have same (j) (hj : j < items.length) : atItem family N p items j = verdict family p items.val[j]! :=
    accepted_spec family p hp _ (room j hj)
  rw [ParallelBatch.verify_all trace stopped]
  exact ⟨fun h j hj => (same j hj).symm.trans (h j hj),fun h j hj => (same j hj).trans (h j hj)⟩

end slhdsa.ParallelBatchItem
