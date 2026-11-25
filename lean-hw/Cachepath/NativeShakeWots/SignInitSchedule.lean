import Cachepath.NativeShakeWots.SignInitLanes
import Cachepath.NativeShakeWots.SignEngine
import Cachepath.NativeVerify.WotsSchedule
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots.Signer
open ShakeBatch Shakeopt.WotsRefill NativeVerify NativeVerify.Wots
set_option linter.concreteInstances false
variable [machine : Machine] [accel : Dispatch machine]

def OrderCorrect (digits : Slice U32) (order : Array Usize 67#usize) (total : Usize) : Prop :=
  total.val≤digits.length ∧
  (∀ j<total.val, let id:=order.val[j]!.val
                  id<digits.length ∧ 0<digits.val[id]!.val) ∧
  ((order.val.take total.val).map UScalar.val).Nodup ∧
  (∀ id, id ∈ (order.val.take total.val).map UScalar.val ↔ id<digits.length ∧ 0<digits.val[id]!.val)

omit machine accel in
theorem schedule_sort (digits : Slice U32) (bound : digits.length≤67)
    (valid : ∀ i<digits.length, digits.val[i]!.val<16) :
    ShakeoptSort.shake.batch.sort_descending digits ⦃ out => OrderCorrect digits out.1 out.2 ⦄ := by
  apply WP.spec_mono (sort_descending_spec digits bound valid)
  rintro ⟨order,total⟩ ⟨_,size,forward,back,unique,_⟩
  dsimp only at size forward back unique
  have queued (j : Nat) (hj : j<total.val) : order.val[j]!.val<digits.length ∧
      0<digits.val[order.val[j]!.val]!.val := ⟨(back j hj).1,(back j hj).2.1⟩
  refine ⟨size,queued,unique,?_⟩
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
  · rintro ⟨inside,positive⟩
    obtain ⟨inside',found⟩ := forward id (by omega) positive
    let i := descRank digits.val id
    have atId : queue[i] = id := by rw [← getElem!_pos,atIndex i inside',found]
    exact List.mem_iff_getElem.mpr ⟨i,by change i<queue.length;rw [length];exact inside',atId⟩

def makeSchedule {N : Usize} (digits : Slice U32) (n : Usize) (order : Array Usize 67#usize)
    (total : Usize) (table : Secrets) (source : Nat → Spec.Bytes) (sig : Signature)
    (small : N.val≤32) (align : N.val%8=0) (count : n.val=N.val/8) (bound : digits.length≤67)
    (valid : ∀ i<digits.length, digits.val[i]!.val<16) (sorted : OrderCorrect digits order total)
    (prepared : Prepared N digits source digits.length sig table) : Schedule N where
  digits := digits
  n := n
  order := order
  total := total
  secrets := table
  source := source
  small := small
  align := align
  count := count
  bound := bound
  size := sorted.1.trans bound
  queued := by
    intro j hj
    obtain ⟨inside,positive⟩ := sorted.2.1 j hj
    have bounded := valid _ inside
    exact ⟨inside,positive,by omega,(prepared.2 _ inside).2 (by omega)⟩

theorem launch {N : Usize} (p : params.Params) (hp : PN p N) (c : Schedule N)
    (seed : Array U8 N) (a : address.Adrs) (offset pad : Usize) (sw aw : Array U64 4#usize)
    (sig : Signature) (next active : Usize) (ids : Ids) (steps ends : Steps)
    (v : LaneValues machine.width) (s : State)
    (count : active.val=min c.total.val machine.width.val) (position : next.val=active.val)
    (lanes : Initial c active.val ids steps ends v)
    (prepared : Prepared N c.digits c.source c.digits.length sig c.secrets)
    (sourceLen : ∀ i<c.digits.length, (c.source i).length=N.val) (positive : 0<machine.width.val)
    (off : offset.val=c.n.val+4) (padding : pad.val=offset.val+c.n.val)
    (seedWords : ∀ k<c.n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addrWords : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (unique : c.ids.Nodup)
    (ordered : ∀ i, i ∈ c.ids ↔ (i<c.digits.length ∧ 0<c.ending i)) (permutes : ActiveCorrect machine accel.permute) :
    sign_loop2 N c.digits c.n offset sw aw sig c.secrets s c.order c.total next active ids steps ends v pad
      ⦃ out => out.length=c.digits.length*N.val ∧ ∀ i<c.digits.length, ∀ b<N.val, Block out N.val i b=(expected c p seed a i)[b]! ⦄ := by
  apply engine p hp c seed a offset pad sw aw (initialGhost c sig) sig next active ids steps ends v s
    (initial_matches c sig next active ids steps ends v s count position lanes prepared.1) _ off padding
    seedWords addrWords unique ordered permutes
  apply initial_outer machine.width.val positive _ _ _ _ _ _ _ _ unique (fun i h=>(ordered i).mp h)
  intro i hi zero
  change sigChunk sig N.val i=c.source i
  apply List.ext_getElem
  · simp [sigChunk,sourceLen _ hi]
  · intro b hb hb'
    have within : b<N.val := by simpa [sigChunk] using hb
    rw [← getElem!_pos,← getElem!_pos,chunk_byte _ _ _ _ within]
    exact (prepared.2 i hi).1 (Eq.symm zero) b within

end slhdsa.NativeShakeWots.Signer
