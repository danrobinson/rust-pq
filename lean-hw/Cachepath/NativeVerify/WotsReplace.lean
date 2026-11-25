import Cachepath.NativeVerify.WotsAdvance
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch Shakeopt.WotsRefill
set_option linter.concreteInstances false
variable [machine : Machine]

def replaced (g : RefillState) (cur id : Nat) (init : Nat → Spec.Bytes) (start finish : Nat → Nat) : RefillState :=
  {active := g.active, next := g.next+1,
   laneId := fun l => if l=cur then id else g.laneId l,
   laneStep := fun l => if l=cur then start id else g.laneStep l,
   laneEnd := fun l => if l=cur then finish id else g.laneEnd l,
   laneVal := fun l => if l=cur then init id else g.laneVal l,
   out := wrote g cur}

omit machine in
theorem post_replace (g : RefillState) (cur : Nat) (init : Nat → Spec.Bytes) (start finish : Nat → Nat)
    (order : List Nat) (live : cur<g.active) (done : g.laneStep cur+1 = g.laneEnd cur)
    (pending : g.next<order.length) : postLoop init start finish order cur g =
      postLoop init start finish order (cur+1) (replaced g cur order[g.next]! init start finish) := by
  rw [postLoop]
  simp only [dite_eq_left live,ite_eq_left done,ite_eq_left pending]
  rfl

theorem replace_matches {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips tips' : Tips N} {ids : Ids} {steps : Steps} {v v' : LaneValues machine.width} {s : State}
    (prior : Matches len g cur.val tips next active ids steps v s) (live : cur.val<active.val)
    (init : Nat → Spec.Bytes) (start : Nat → Nat)
    (next' nid : Usize) (digit bump : U32) (incr : next'.val=g.next+1)
    (domain : nid.val<len) (startEq : digit.val=start nid.val) (positive : start nid.val<15)
    (newValue : Packed N v' cur.val (init nid.val))
    (other : ∀ l, l≠cur.val → ∀ k<N.val/8, laneWord v' l k = laneWord v l k)
    (output : ∀ i<len, bytes tips'.val[i]!.val=wrote g cur.val i) :
    Matches len (replaced g cur.val nid.val init start (fun _=>15)) (cur.val+1) tips' next' active
      (ids.set cur nid) ((steps.set cur bump).set cur digit) v' s := by
  have within := live.trans_le prior.room
  refine ⟨prior.act,incr,prior.room,?_,?_,?_,?_,?_,?_,?_,output⟩
  · intro l hl
    rw [slot _ _ _ _ within]
    by_cases eq : l=cur.val <;> simp [replaced,eq,prior.ident l hl]
    simpa using prior.ident l hl
  · intro l hl
    rw [slot _ _ _ _ within,slot _ _ _ _ within]
    by_cases eq : l=cur.val <;> simp [replaced,eq,startEq,prior.step l hl]
    simpa using prior.step l hl
  · intro l hl
    by_cases eq : l=cur.val <;> simp [replaced,eq,domain,prior.inside l hl]
  · intro l hl
    by_cases eq : l=cur.val <;> simp [replaced,eq,positive,prior.valid l hl]
  · intro l hl
    by_cases eq : l=cur.val <;> simp [replaced,eq,prior.ends l hl]
  · intro l hl used
    by_cases eq : l=cur.val
    · simpa [replaced,eq] using newValue
    · simpa [replaced,eq] using packed_congr (prior.prepared l hl (by omega)) (other l eq)
  · intro l hl skip
    have eq : l≠cur.val := by omega
    simpa [replaced,eq] using prior.pending l hl (by omega)

end slhdsa.NativeVerify.Wots
