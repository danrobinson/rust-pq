import Cachepath.NativeShakeWots.SignState
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots.Signer
open ShakeBatch Shakeopt.WotsRefill NativeVerify NativeVerify.Wots
set_option linter.concreteInstances false
variable [machine : Machine]

theorem advance_matches {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips : Signature} {ids : Ids} {steps ends : Steps} {v v' : LaneValues machine.width} {s : State}
    (prior : Matches (N:=N) len g cur.val tips next active ids steps ends v s) (live : cur.val<active.val)
    (increment : U32) (add : increment.val=g.laneStep cur.val+1) (more : increment.val<g.laneEnd cur.val)
    (small : N.val≤32) (align : N.val%8=0)
    (saved : ∀ l k, laneWord v' l k=if l=cur.val ∧ k<N.val/8 then cell s k l else laneWord v l k) :
    Matches (N:=N) len (advanced g cur.val) (cur.val+1) tips next active ids (steps.set cur increment) ends v' s := by
  have within := live.trans_le prior.room
  refine ⟨prior.act,prior.idx,prior.room,prior.ident,?_,prior.inside,?_,prior.endsAt,prior.bound,?_,?_,prior.lenEq,prior.output⟩
  · intro l hl
    rw [slot _ _ _ _ within]
    by_cases h : l=cur.val
    · simpa [advanced,h] using add
    · simpa [advanced,h] using prior.step l hl
  · intro l hl
    by_cases h : l=cur.val
    · simpa [advanced,h,add] using more
    · simpa [advanced,h] using prior.valid l hl
  · intro l hl passed
    by_cases here : l=cur.val
    · subst l
      rw [show (advanced g cur.val).laneVal cur.val = digest N s cur.val from (prior.pending _ live (by omega)).symm]
      exact packed_of_digest s v' cur.val small align within (fun k hk => by simp [saved,hk])
    · exact packed_congr (prior.prepared l hl (by omega)) (fun k _ => by simp [saved,here])
  · intro l hl pending
    exact prior.pending l hl (by omega)

theorem replace_matches {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips tips' : Signature} {ids : Ids} {steps ends : Steps} {v v' : LaneValues machine.width} {s : State}
    (prior : Matches (N:=N) len g cur.val tips next active ids steps ends v s) (live : cur.val<active.val)
    (init : Nat → Spec.Bytes) (finish : Nat → Nat)
    (next' nid : Usize) (digit bump : U32) (incr : next'.val=g.next+1)
    (domain : nid.val<len) (endEq : digit.val=finish nid.val) (positive : 0<finish nid.val) (bound : finish nid.val≤15)
    (newValue : Packed N v' cur.val (init nid.val))
    (other : ∀ l, l≠cur.val → ∀ k<N.val/8, laneWord v' l k = laneWord v l k)
    (lenEq : tips'.length=len*N.val) (output : ∀ i<len, ∀ b<N.val, Block tips' N.val i b=(wrote g cur.val i)[b]!) :
    Matches (N:=N) len (replaced g cur.val nid.val init (fun _=>0) finish) (cur.val+1) tips' next' active
      (ids.set cur nid) ((steps.set cur bump).set cur 0#u32) (ends.set cur digit) v' s := by
  have within := live.trans_le prior.room
  refine ⟨prior.act,incr,prior.room,?_,?_,?_,?_,?_,?_,?_,?_,lenEq,output⟩
  · intro l hl
    rw [slot _ _ _ _ within]
    by_cases eq : l=cur.val <;> simp [replaced,eq,prior.ident l hl]
    simpa using prior.ident l hl
  · intro l hl
    rw [slot _ _ _ _ within,slot _ _ _ _ within]
    by_cases eq : l=cur.val <;> simp [replaced,eq,prior.step l hl]
    simpa using prior.step l hl
  · intro l hl
    by_cases eq : l=cur.val <;> simp [replaced,eq,domain,prior.inside l hl]
  · intro l hl
    by_cases eq : l=cur.val <;> simp [replaced,eq,positive,prior.valid l hl]
  · intro l hl
    rw [slot _ _ _ _ within]
    by_cases eq : l=cur.val <;> simp [replaced,eq,endEq,prior.endsAt l hl]
    simpa using prior.endsAt l hl
  · intro l hl
    by_cases eq : l=cur.val <;> simp [replaced,eq,bound,prior.bound l hl]
  · intro l hl used
    by_cases eq : l=cur.val
    · simpa [replaced,eq] using newValue
    · simpa [replaced,eq] using packed_congr (prior.prepared l hl (by omega)) (other l eq)
  · intro l hl skip
    have eq : l≠cur.val := by omega
    simpa [replaced,eq] using prior.pending l hl (by omega)

theorem remove_matches {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips tips' : Signature} {ids : Ids} {steps ends : Steps} {v : LaneValues machine.width} {s : State}
    (prior : Matches (N:=N) len g cur.val tips next active ids steps ends v s) (live : cur.val<active.val)
    (smaller : Usize) (bump : U32) (dec : smaller.val=active.val-1) (last : smaller.val≤cur.val)
    (lenEq : tips'.length=len*N.val) (output : ∀ i<len, ∀ b<N.val, Block tips' N.val i b=(wrote g cur.val i)[b]!) :
    Matches (N:=N) len (removed g cur.val) cur.val tips' next smaller ids (steps.set cur bump) ends v s := by
  have within := live.trans_le prior.room
  have less : smaller.val < active.val := by omega
  refine ⟨by simp [removed,dec,prior.act],prior.idx,less.le.trans prior.room,?_,?_,?_,?_,?_,?_,?_,?_,lenEq,output⟩
  · intro l hl; exact prior.ident _ (hl.trans less)
  · intro l hl; rw [slot _ _ _ _ within,ite_eq_right (by omega)]; exact prior.step _ (hl.trans less)
  · intro l hl; exact prior.inside _ (hl.trans less)
  · intro l hl; exact prior.valid _ (hl.trans less)
  · intro l hl; exact prior.endsAt _ (hl.trans less)
  · intro l hl; exact prior.bound _ (hl.trans less)
  · intro l hl passed; exact prior.prepared _ (hl.trans less) passed
  · intro l hl skip; omega

theorem swap_matches {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips tips' : Signature} {ids : Ids} {steps ends : Steps} {v : LaneValues machine.width} {s s' : State}
    (prior : Matches (N:=N) len g cur.val tips next active ids steps ends v s) (live : cur.val<active.val)
    (smaller lastId : Usize) (bump lastStep lastEnd : U32) (dec : smaller.val=active.val-1) (moving : cur.val<smaller.val)
    (lastIdEq : lastId.val=g.laneId smaller.val) (lastStepEq : lastStep.val=g.laneStep smaller.val)
    (lastEndEq : lastEnd.val=g.laneEnd smaller.val) (small : N.val≤32) (align : N.val%8=0)
    (moved : ∀ k l, cell s' k l = if k<N.val/8 ∧ l=cur.val then cell s k smaller.val else cell s k l)
    (lenEq : tips'.length=len*N.val) (output : ∀ i<len, ∀ b<N.val, Block tips' N.val i b=(wrote g cur.val i)[b]!) :
    Matches (N:=N) len (swapped g cur.val) cur.val tips' next smaller (ids.set cur lastId)
      ((steps.set cur bump).set cur lastStep) (ends.set cur lastEnd) v s' := by
  have within := live.trans_le prior.room
  have less : smaller.val<active.val := by omega
  have index : g.active-1=smaller.val := by rw [← prior.act,dec]
  refine ⟨by simp [swapped,index],prior.idx,less.le.trans prior.room,?_,?_,?_,?_,?_,?_,?_,?_,lenEq,output⟩
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
    rw [slot _ _ _ _ within]
    by_cases eq : l=cur.val <;> simp [swapped,index,eq,lastEndEq,prior.endsAt _ less,prior.endsAt _ (hl.trans less)]
    simpa using prior.endsAt l (hl.trans less)
  · intro l hl
    by_cases eq : l=cur.val <;> simp [swapped,index,eq,prior.bound _ less,prior.bound _ (hl.trans less)]
  · intro l hl visited
    simpa [swapped,show l≠cur.val by omega] using prior.prepared l (hl.trans less) visited
  · intro l hl waiting
    by_cases eq : l=cur.val
    · rw [show (swapped g cur.val).laneVal l=g.laneVal smaller.val by simp [swapped,eq,index],
        ← prior.pending smaller.val less moving.le]
      exact digest_congr small align (fun k hk=>by simp [moved,eq,hk])
    · rw [show (swapped g cur.val).laneVal l=g.laneVal l by simp [swapped,eq],← prior.pending l (hl.trans less) waiting]
      exact digest_congr small align (fun k _=>by simp [moved,eq])

end slhdsa.NativeShakeWots.Signer
