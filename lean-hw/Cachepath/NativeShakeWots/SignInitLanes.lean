import Cachepath.NativeShakeWots.SignInitPrf
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots.Signer
open ShakeBatch NativeVerify NativeVerify.Wots Shakeopt.WotsRefill
set_option linter.concreteInstances false
variable [machine : Machine]

def Initial {N : Usize} (c : Schedule N) (live : Nat) (ids : Ids) (steps ends : Steps)
    (values : LaneValues machine.width) : Prop :=
  ∀ l<live, let id := c.order.val[l]!
            ids.val[l]! = id ∧ steps.val[l]! = 0#u32 ∧ ends.val[l]! = c.digits.val[id.val]! ∧
            values.val[l]! = c.secrets.val[id.val]!

theorem initialize_lanes {N : Usize} (c : Schedule N) (active : Usize) (ids : Ids) (steps ends : Steps)
    (values : LaneValues machine.width) (room : active.val≤machine.width.val) (cap : active.val≤c.total.val) :
    sign_loop1 ⟨0#usize,active⟩ c.digits c.secrets c.order 0#usize ids steps ends values ⦃ out =>
      out.1.val=active.val ∧ Initial c active.val out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2 ⦄ := by
  unfold sign_loop1
  apply range_fold (fun it (q : Usize × Ids × Steps × Steps × LaneValues machine.width) =>
    sign_loop1.body c.digits c.secrets c.order it q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) active
    (0#usize,ids,steps,ends,values) (fun l q => q.1.val=l ∧ Initial c l q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
  · simp [Initial]
  · rintro it ⟨pos,ids,steps,ends,vals⟩ stop live ⟨cursor,prior⟩
    change pos.val=it.start.val at cursor
    unfold sign_loop1.body
    have limit := c.size
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,last⟩
    simp only [tag]
    step as ⟨id,atId⟩
    rw [← getElem!_pos] at atId
    have idEq : id=c.order.val[it.start.val]! := by simpa [cursor] using atId
    have good : id.val<c.digits.length := idEq ▸ (c.queued _ (live.trans_le cap)).1
    have bound := c.bound
    step as ⟨nextId,pv⟩
    step as ⟨ids',i0⟩
    step as ⟨steps',s0⟩
    step as ⟨digit,rd⟩
    step as ⟨ends',e0⟩
    step as ⟨saved,rv⟩
    step as ⟨vals',v0⟩
    rw [← getElem!_pos] at rd rv
    refine ⟨next,(nextId,ids',steps',ends',vals'),rfl,last.trans stop,inc,by change nextId.val=next.start.val; omega,?_⟩
    intro l hl
    simp only [i0,s0,e0,v0,Array.set_val_eq]
    by_cases eq : l=it.start.val
    · subst l
      rw [setSame _ _ _ (by simpa using live.trans_le room),setSame _ _ _ (by simpa using live.trans_le room),
        setSame _ _ _ (by simpa using live.trans_le room),setSame _ _ _ (by simpa using live.trans_le room)]
      simp [idEq,rd,rv]
    · simp only [setOther _ _ _ _ (Ne.symm eq)]
      exact prior _ (by omega)
  · rintro it ⟨pos,ids,steps,ends,vals⟩ last stop
    unfold sign_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

def sigChunk (sig : Signature) (n id : Nat) : Spec.Bytes :=
  List.ofFn (fun b : Fin n => Block sig n id b.val)

theorem chunk_byte (sig : Signature) (n id b : Nat) (hb : b<n) :
    (sigChunk sig n id)[b]! = Block sig n id b := by
  unfold sigChunk
  rw [getElem!_pos _ _ (by simpa using hb)]
  simp

def initialGhost {N : Usize} (c : Schedule N) (sig : Signature) : RefillState :=
  {initRefill machine.width.val c.source (fun _ => 0) c.ending c.ids with out := sigChunk sig N.val}

theorem initial_matches {N : Usize} (c : Schedule N) (sig : Signature) (next active : Usize)
    (ids : Ids) (steps ends : Steps) (v : LaneValues machine.width) (state : State)
    (count : active.val=min c.total.val machine.width.val) (position : next.val=active.val)
    (lanes : Initial c active.val ids steps ends v) (length : sig.length=c.digits.length*N.val) :
    Matches (N:=N) c.digits.length (initialGhost c sig) active.val sig next active ids steps ends v state := by
  have room : active.val≤machine.width.val := count ▸ Nat.min_le_right _ _
  have size : active.val≤c.total.val := count ▸ Nat.min_le_left _ _
  have act : active.val=(initialGhost c sig).active := by simpa only [initialGhost,initRefill,c.length] using count
  refine ⟨act,position.trans act,room,?_,?_,?_,?_,?_,?_,?_,by intro _ _ h;omega,length,?_⟩
  · intro l hl; exact congrArg UScalar.val (lanes l hl).1 |>.trans (c.get l (hl.trans_le size)).symm
  · intro l hl; exact congrArg UScalar.val (lanes l hl).2.1
  · intro l hl; simpa only [initialGhost,initRefill,c.get l (hl.trans_le size)] using (c.queued l (hl.trans_le size)).1
  · intro l hl; simpa only [initialGhost,initRefill,Schedule.ending,c.get l (hl.trans_le size)] using (c.queued l (hl.trans_le size)).2.1
  · intro l hl; simpa only [initialGhost,initRefill,Schedule.ending,c.get l (hl.trans_le size)] using congrArg UScalar.val (lanes l hl).2.2.1
  · intro l hl; simpa only [initialGhost,initRefill,Schedule.ending,c.get l (hl.trans_le size)] using (c.queued l (hl.trans_le size)).2.2.1
  · intro l hl _
    obtain ⟨b,hval,hwords⟩ := (c.queued l (hl.trans_le size)).2.2.2
    refine ⟨b,by simpa only [initialGhost,initRefill,c.get _ (hl.trans_le size)] using hval,?_⟩
    intro k hk
    simp only [laneWord,(lanes l hl).2.2.2]
    exact hwords k hk
  · intro i _ b hb;exact (chunk_byte _ _ _ _ hb).symm

end slhdsa.NativeShakeWots.Signer
