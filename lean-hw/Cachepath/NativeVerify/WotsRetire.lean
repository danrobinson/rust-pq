import Cachepath.NativeVerify.WotsReplace
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch Shakeopt.WotsRefill
set_option linter.concreteInstances false
variable [machine : Machine]

def removed (g : RefillState) (cur : Nat) : RefillState :=
  {g with active := g.active-1,out:=wrote g cur}

def swapped (g : RefillState) (cur : Nat) : RefillState :=
  let last := g.active-1
  {active:=last, next:=g.next, out:=wrote g cur,
   laneId:=fun l=> if l=cur then g.laneId last else g.laneId l,
   laneStep:=fun l=> if l=cur then g.laneStep last else g.laneStep l,
   laneEnd:=fun l=> if l=cur then g.laneEnd last else g.laneEnd l,
   laneVal:=fun l=> if l=cur then g.laneVal last else g.laneVal l}

omit machine in
theorem post_remove (g : RefillState) (cur : Nat) (init : Nat → Spec.Bytes) (start finish : Nat → Nat)
    (order : List Nat) (live : cur<g.active) (done : g.laneStep cur+1 = g.laneEnd cur)
    (none : ¬g.next<order.length) : postLoop init start finish order cur g =
      postLoop init start finish order cur (if cur<g.active-1 then swapped g cur else removed g cur) := by
  rw [postLoop]
  simp only [dite_eq_left live,ite_eq_left done,ite_eq_right none]
  rfl

theorem remove_matches {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips tips' : Tips N} {ids : Ids} {steps : Steps} {v : LaneValues machine.width} {s : State}
    (prior : Matches len g cur.val tips next active ids steps v s) (live : cur.val<active.val)
    (smaller : Usize) (bump : U32) (dec : smaller.val=active.val-1) (last : smaller.val≤cur.val)
    (output : ∀ i<len, bytes tips'.val[i]!.val=wrote g cur.val i) :
    Matches len (removed g cur.val) cur.val tips' next smaller ids (steps.set cur bump) v s := by
  have within := live.trans_le prior.room
  have less : smaller.val < active.val := by omega
  refine ⟨by simp [removed,dec,prior.act],prior.idx,less.le.trans prior.room,?_,?_,?_,?_,?_,?_,?_,output⟩
  · intro l hl; exact prior.ident _ (hl.trans less)
  · intro l hl; rw [slot _ _ _ _ within,ite_eq_right (by omega)]; exact prior.step _ (hl.trans less)
  · intro l hl; exact prior.inside _ (hl.trans less)
  · intro l hl; exact prior.valid _ (hl.trans less)
  · intro l hl; exact prior.ends _ (hl.trans less)
  · intro l hl passed; exact prior.prepared _ (hl.trans less) passed
  · intro l hl skip; omega

theorem swap_matches {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips tips' : Tips N} {ids : Ids} {steps : Steps} {v : LaneValues machine.width} {s s' : State}
    (prior : Matches len g cur.val tips next active ids steps v s) (live : cur.val<active.val)
    (smaller lastId : Usize) (bump lastStep : U32) (dec : smaller.val=active.val-1) (moving : cur.val<smaller.val)
    (lastIdEq : lastId.val=g.laneId smaller.val) (lastStepEq : lastStep.val=g.laneStep smaller.val)
    (small : N.val≤32) (align : N.val%8=0)
    (moved : ∀ k l, cell s' k l = if k<N.val/8 ∧ l=cur.val then cell s k smaller.val else cell s k l)
    (output : ∀ i<len, bytes tips'.val[i]!.val=wrote g cur.val i) :
    Matches len (swapped g cur.val) cur.val tips' next smaller (ids.set cur lastId)
      ((steps.set cur bump).set cur lastStep) v s' := by
  have within := live.trans_le prior.room
  have less : smaller.val<active.val := by omega
  have index : g.active-1=smaller.val := by rw [← prior.act,dec]
  refine ⟨by simp [swapped,index],prior.idx,less.le.trans prior.room,?_,?_,?_,?_,?_,?_,?_,output⟩
  · intro l hl
    rw [slot _ _ _ _ within]
    by_cases eq : l=cur.val <;> simp [swapped,index,eq,lastIdEq,prior.ident l (hl.trans less)]
    simpa using prior.ident l (hl.trans less)
  · intro l hl
    rw [slot _ _ _ _ within,slot _ _ _ _ within]
    by_cases eq : l=cur.val <;> simp [swapped,index,eq,lastStepEq,prior.step l (hl.trans less)]
    simpa using prior.step l (hl.trans less)
  · intro l hl
    by_cases eq : l=cur.val <;> simp [swapped,index,eq,prior.inside _ less,prior.inside _ (hl.trans less)]
  · intro l hl
    by_cases eq : l=cur.val <;> simp [swapped,index,eq,prior.valid _ less,prior.valid _ (hl.trans less)]
  · intro l hl
    by_cases eq : l=cur.val <;> simp [swapped,index,eq,prior.ends _ less,prior.ends _ (hl.trans less)]
  · intro l hl visited
    simpa [swapped,show l≠cur.val by omega] using prior.prepared l (hl.trans less) visited
  · intro l hl waiting
    by_cases eq : l=cur.val
    · rw [show (swapped g cur.val).laneVal l=g.laneVal smaller.val by simp [swapped,eq,index],
        ← prior.pending smaller.val less moving.le]
      exact digest_congr small align (fun k hk=>by simp [moved,eq,hk])
    · rw [show (swapped g cur.val).laneVal l=g.laneVal l by simp [swapped,eq],← prior.pending l (hl.trans less) waiting]
      exact digest_congr small align (fun k _=>by simp [moved,eq])

end slhdsa.NativeVerify.Wots
