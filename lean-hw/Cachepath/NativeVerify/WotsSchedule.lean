import Cachepath.NativeVerify.WotsOuter
import Cachepath.NativeVerify.WotsPrepare
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch Shakeopt.WotsRefill
set_option linter.concreteInstances false
variable [machine : Machine]

def OrderCorrect (digits : Slice U32) (order : Array Usize 67#usize) (total : Usize) : Prop :=
  total.val≤digits.length ∧
  (∀ j < total.val, let id:=order.val[j]!.val
                    id<digits.length ∧ digits.val[id]!.val<15) ∧
  ((order.val.take total.val).map UScalar.val).Nodup ∧
  (∀ id, id ∈ (order.val.take total.val).map UScalar.val ↔ id<digits.length ∧ digits.val[id]!.val<15)

omit machine in
theorem schedule_sort {N : Usize} (sig : Slice U8) (digits slice : Slice U32)
    (tips : Tips N) (remain : Array U32 67#usize) (bound : digits.length≤67)
    (prepared : Prepared sig digits digits.length tips remain)
    (len : slice.length=digits.length) (view : slice.val=remain.val.slice 0 digits.length) :
    ShakeoptSort.shake.batch.sort_descending slice ⦃ out => OrderCorrect digits out.1 out.2 ⦄ := by
  have each (i : Nat) (hi : i<digits.length) : slice.val[i]!.val=15-digits.val[i]!.val := by
    rw [view,slice0_getElem! _ _ _ hi (by simpa using bound)]
    exact (prepared _ hi).1
  apply WP.spec_mono (sort_descending_spec slice (by omega) (by intro i hi;rw [each _ (by omega)];omega))
  rintro ⟨order,total⟩ ⟨_,size,forward,back,unique,_⟩
  dsimp only at size forward back unique
  have queued (j : Nat) (hj : j<total.val) : order.val[j]!.val<digits.length ∧
      digits.val[order.val[j]!.val]!.val<15 := by
    obtain ⟨inside,positive,_⟩ := back j hj
    have valid : order.val[j]!.val<digits.length := by omega
    rw [each _ valid] at positive
    exact ⟨valid,by omega⟩
  refine ⟨size.trans (by rw [len]),queued,unique,?_⟩
  intro id
  let queue := (order.val.take total.val).map UScalar.val
  have length : queue.length=total.val := by simp [queue];omega
  have atIndex (i : Nat) (hi : i<total.val) : queue[i]! = order.val[i]!.val := by
    rw [getElem!_pos queue i (by omega)]
    simp only [queue,List.getElem_map,List.getElem_take]
    rw [getElem!_pos order.val i (by simp;omega)]
  constructor
  · intro found
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp (show id∈queue from found)
    rw [← getElem!_pos,atIndex i (by omega)] at eq
    rw [← eq]
    exact queued i (by omega)
  · rintro ⟨inside,short⟩
    have positive : 0<slice.val[id]!.val := by rw [each _ inside];omega
    obtain ⟨inside',found⟩ := forward id (by omega) positive
    let i := descRank slice.val id
    have atId : queue[i] = id := by rw [← getElem!_pos,atIndex i inside',found]
    exact List.mem_iff_getElem.mpr ⟨i,by change i<queue.length;rw [length];exact inside',atId⟩

def initialGhost {N : Usize} (c : Schedule N) (tips : Tips N) : RefillState :=
  {initRefill machine.width.val c.init c.start (fun _=>15) c.ids with out:=fun id=>bytes tips.val[id]!.val}

theorem initial_matches {N : Usize} (c : Schedule N) (tips : Tips N) (next active : Usize)
    (ids : Ids) (steps : Steps) (v : LaneValues machine.width) (s : State)
    (count : active.val=min c.total.val machine.width.val) (position : next.val=active.val)
    (lanes : InitialLanes N c.n c.sig c.digits c.order active.val ids steps v) :
    Matches c.digits.length (initialGhost c tips) active.val tips next active ids steps v s := by
  have room : active.val≤machine.width.val := count ▸ Nat.min_le_right _ _
  have size : active.val≤c.total.val := count ▸ Nat.min_le_left _ _
  have act : active.val=(initialGhost c tips).active := by simpa only [initialGhost,initRefill,c.size] using count
  refine ⟨act,position.trans act,room,?_,?_,?_,?_,?_,?_,?_,(by intro i _;rfl)⟩
  · intro l hl; exact congrArg UScalar.val (lanes l hl).1 |>.trans (c.get l (hl.trans_le size)).symm
  · intro l hl
    simpa only [initialGhost,initRefill,Schedule.start,c.get _ (hl.trans_le size)] using congrArg UScalar.val (lanes l hl).2.1
  · intro l hl
    simpa only [initialGhost,initRefill,c.get _ (hl.trans_le size)] using (c.queued l (hl.trans_le size)).1
  · intro l hl
    simpa only [initialGhost,initRefill,Schedule.start,c.get _ (hl.trans_le size)] using (c.queued l (hl.trans_le size)).2
  · intro _ _;rfl
  · intro l hl _
    let id := c.order.val[l]!.val
    let data := (c.sig.val.drop (id*N.val)).take N.val
    have enough := (Nat.mul_le_mul_right N.val (c.queued l (hl.trans_le size)).1).trans c.fits
    have fit : id*N.val+N.val≤c.sig.length := by simpa only [id,Nat.succ_mul] using enough
    have len : data.length=N.val := by simp [data];change N.val≤c.sig.length-id*N.val;omega
    let b : Array U8 N := Array.from data len
    have bv : b.val=data := Array.from_val _ _
    refine ⟨b,?_,?_⟩
    · simp only [initialGhost,initRefill,Schedule.init,c.get _ (hl.trans_le size),bv,data,id]
    · intro k hk
      simpa only [bv,data,id] using (lanes l hl).2.2 k (by rw [c.count];exact hk)
  · intro l hl waiting;omega

end slhdsa.NativeVerify.Wots
