import Cachepath.NativeVerify.WotsState
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch Shakeopt.WotsRefill
set_option linter.concreteInstances false
variable [machine : Machine]

theorem slot {α} [Inhabited α] {n : Usize} (xs : Array α n) (atI : Usize) (value : α) (l : Nat)
    (within : atI.val<n.val) : (xs.set atI value).val[l]! = if l=atI.val then value else xs.val[l]! := by
  rw [Array.set_val_eq]
  by_cases eq : l=atI.val
  · subst l; rw [setSame _ _ _ (by simpa),ite_eq_left rfl]
  · rw [setOther _ _ _ _ (Ne.symm eq),ite_eq_right eq]

def advanced (g : RefillState) (cur : Nat) : RefillState :=
  {g with laneStep := fun l => if l=cur then g.laneStep cur+1 else g.laneStep l}

theorem post_advance (g : RefillState) (cur : Nat) (init : Nat → Spec.Bytes) (start finish : Nat → Nat)
    (order : List Nat) (live : cur<g.active) (more : g.laneStep cur+1 ≠ g.laneEnd cur) :
    postLoop init start finish order cur g = postLoop init start finish order (cur+1) (advanced g cur) := by
  rw [postLoop]
  simp only [dif_pos live,ite_eq_right more]
  rfl

theorem advance_matches {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips : Tips N} {ids : Ids} {steps : Steps} {v v' : LaneValues machine.width} {s : State}
    (prior : Matches len g cur.val tips next active ids steps v s) (live : cur.val<active.val)
    (increment : U32) (add : increment.val=g.laneStep cur.val+1) (more : increment.val<15)
    (small : N.val≤32) (align : N.val%8=0)
    (saved : ∀ l k, laneWord v' l k=if l=cur.val ∧ k<N.val/8 then cell s k l else laneWord v l k) :
    Matches len (advanced g cur.val) (cur.val+1) tips next active ids (steps.set cur increment) v' s := by
  have within := live.trans_le prior.room
  refine ⟨prior.act,prior.idx,prior.room,prior.ident,?_,prior.inside,?_,prior.ends,?_,?_,prior.output⟩
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

def wrote (g : RefillState) (cur i : Nat) := if i=g.laneId cur then g.laneVal cur else g.out i

theorem write_endpoint {N : Usize} {len : Nat} {g : RefillState} {cur next active : Usize}
    {tips : Tips N} {ids : Ids} {steps : Steps} {v : LaneValues machine.width} {s : State}
    (prior : Matches len g cur.val tips next active ids steps v s) (live : cur.val<active.val)
    (id : Usize) (same : id.val=g.laneId cur.val) (bound : len≤67)
    (blob : Array U8 N) (hash : bytes blob.val=digest N s cur.val) :
    ∀ i<len, bytes (tips.set id blob).val[i]!.val=wrote g cur.val i := by
  intro i hi
  have h := prior.inside _ live
  rw [slot _ _ _ _ (by change _<67;omega)]
  unfold wrote
  by_cases x : i=id.val
  · rw [ite_eq_left x,ite_eq_left (x.trans same),hash,prior.pending _ live (by omega)]
  · rw [ite_eq_right x,ite_eq_right (by omega)]; exact prior.output i hi

end slhdsa.NativeVerify.Wots
