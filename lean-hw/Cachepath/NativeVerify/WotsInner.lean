import Cachepath.NativeVerify.WotsRetire
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch Shakeopt.WotsRefill
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [machine : Machine]

structure Schedule (N : Usize) where
  sig : Slice U8
  digits : Slice U32
  n : Usize
  order : Array Usize 67#usize
  total : Usize
  small : N.val≤32
  align : N.val%8=0
  count : n.val=N.val/8
  bound : digits.length≤67
  fits : digits.length*N.val≤sig.length
  orderSize : total.val≤67
  queued : ∀ i<total.val, let id:=order.val[i]!.val
                          id<digits.length ∧ digits.val[id]!.val<15

def Schedule.ids {N : Usize} (c : Schedule N) := (c.order.val.take c.total.val).map UScalar.val
def Schedule.init {N : Usize} (c : Schedule N) (id : Nat) := bytes ((c.sig.val.drop (id*N.val)).take N.val)
def Schedule.start {N : Usize} (c : Schedule N) (id : Nat) := c.digits.val[id]!.val

omit machine in
theorem Schedule.size {N : Usize} (c : Schedule N) : c.ids.length=c.total.val := by simp [Schedule.ids,c.orderSize]

omit machine in
theorem Schedule.get {N : Usize} (c : Schedule N) (i : Nat) (lt : i<c.total.val) :
    c.ids[i]! =c.order.val[i]!.val := by
  have valid : i<c.ids.length := by rw [c.size]; exact lt
  rw [getElem!_pos c.ids i valid]
  simp only [Schedule.ids,List.getElem_map,List.getElem_take]
  rw [getElem!_pos c.order.val i (by simp;have := c.orderSize;omega)]

abbrev InnerTuple (N : Usize) := Tips N × Usize × Usize × Ids × Steps × LaneValues machine.width × State × Usize

def Schedule.finalState {N : Usize} (c : Schedule N) (i : Nat) (g : RefillState) :=
  postLoop c.init c.start (fun _=>15) c.ids i g

theorem scan {N : Usize} (c : Schedule N) (g : RefillState)
    (tips : Tips N) (next active : Usize) (ids : Ids) (steps : Steps)
    (values : LaneValues machine.width) (s : State) (cur : Usize)
    (prior : Matches c.digits.length g cur.val tips next active ids steps values s) (cursor : cur.val≤active.val) :
    recover_loop2_loop3 c.sig c.digits c.n tips c.order c.total next active ids steps values s cur
      ⦃ tips' next' active' ids' steps' vals' s' => Matches c.digits.length (c.finalState cur.val g) active'.val
        tips' next' active' ids' steps' vals' s' ⦄ := by
  let final := c.finalState cur.val g
  let inv : InnerTuple N → Prop := fun ⟨tips,next,active,ids,steps,v,s,l⟩ => ∃ st,
    Matches c.digits.length st l.val tips next active ids steps v s ∧ l.val≤active.val ∧ c.finalState l.val st=final
  unfold recover_loop2_loop3
  apply loop.spec_decr_nat (measure := fun x : InnerTuple N => x.2.2.1.val-x.2.2.2.2.2.2.2.val) (inv := inv)
  · rintro ⟨tips,next,active,ids,steps,v,s,l⟩ ⟨st,match',cursor,target⟩
    change Matches c.digits.length st l.val tips next active ids steps v s at match'
    change l.val≤active.val at cursor
    change c.finalState l.val st=final at target
    unfold recover_loop2_loop3.body
    by_cases live : l<active
    · simp only [live,ite_true]
      have alive : l.val<active.val := live
      have bounded := c.bound
      have ordered := c.orderSize
      have width := match'.room
      have within := alive.trans_le match'.room
      have value := match'.step l.val alive
      have limit := match'.valid l.val alive
      have ending := match'.ends l.val alive
      step as ⟨old,getOld⟩
      rw [← getElem!_pos] at getOld
      step as ⟨bump,bi⟩
      have bumpEq : bump.val=st.laneStep l.val+1 := by rw [bi,getOld,value]
      step as ⟨steps',wroteStep⟩
      step as ⟨bump',readBack⟩
      have rb : bump'=bump := by
        rw [← getElem!_pos,wroteStep,slot _ _ _ _ within,ite_eq_left rfl] at readBack
        exact readBack
      simp only [W_eq,show (16#u32-1#u32 : Result U32)=ok 15#u32 from rfl,bind_ok,rb]
      subst steps'
      by_cases done : bump=15#u32
      · rw [ite_eq_left done]
        have finished : st.laneStep l.val+1=st.laneEnd l.val := by rw [← bumpEq,done,ending];rfl
        step as ⟨id,which⟩
        rw [← getElem!_pos] at which
        have idEq : id.val=st.laneId l.val := by simpa [which] using match'.ident _ alive
        have inside := match'.inside _ alive
        step with extract_digest N s l c.small c.align within as ⟨blob,digestEq⟩
        step as ⟨_,back,_,write⟩
        have output := write_endpoint match' alive id idEq c.bound blob digestEq
        by_cases pending : next<c.total
        · simp only [pending,ite_true]
          have left : next.val<c.total.val := pending
          have queued := c.queued next.val left
          step as ⟨nid,read⟩
          rw [← getElem!_pos] at read
          have nidEq : nid.val=c.ids[st.next]! := by rw [← match'.idx,c.get _ left,read]
          have good : nid.val<c.digits.length := by simpa [read] using queued.1
          have positive : c.start nid.val<15 := by simpa [Schedule.start,read] using queued.2
          have sigFits := (Nat.mul_le_mul_right N.val good).trans c.fits
          step as ⟨next',inc⟩
          step as ⟨ids',setId⟩
          step as ⟨digit,dig⟩
          rw [← getElem!_pos] at dig
          step as ⟨steps',setDigit⟩
          step as ⟨base,bv⟩
          step as ⟨succ,sv⟩
          step as ⟨stop,ev⟩
          step as ⟨blk,view,blockLen⟩
          have delta : stop.val=base.val+N.val := by rw [ev,sv,bv,Nat.add_mul];simp
          have nval := c.count
          have small := c.small
          have align := c.align
          step with refill_load_lane v l c.n blk within (by omega) (by omega) as ⟨v',saved⟩
          step as ⟨l',incr⟩
          let newer := replaced st l.val nid.val c.init c.start (fun _=>15)
          have block : blk.val=(c.sig.val.drop (nid.val*N.val)).take N.val := by simp [view,List.slice,bv,delta]
          have exactLen : blk.length=N.val := by omega
          let a : Array U8 N := Array.from_slice (Array.repeat N 0#u8) blk
          have aEq : a.val=blk.val := Array.from_slice_val _ _ (by simpa using exactLen)
          have pack : Packed N v' l.val (c.init nid.val) := by
            exact ⟨a,by rw [aEq,block];rfl, fun k hk=>by simp [saved,nval,hk,aEq]⟩
          refine ⟨⟨newer,?_,by omega,?_⟩,by omega⟩
          · rw [write,setId,setDigit,incr]
            exact replace_matches match' alive c.init c.start next' nid digit bump (by rw [inc,match'.idx])
              good (by rw [dig];rfl) positive pack (fun x ne k _=>by simp [saved,ne]) output
          · change c.finalState l'.val newer=final
            rw [← target,incr]
            unfold Schedule.finalState
            rw [post_replace st l.val c.init c.start (fun _=>15) c.ids (by rw [← match'.act];exact alive) finished
              (by rw [← match'.idx,c.size];exact left),← nidEq]
        · simp only [pending,ite_false]
          step as ⟨act',dec⟩
          by_cases relocate : l<act'
          · simp only [relocate,ite_true]
            have moving : l.val<act'.val := relocate
            have less : act'.val<active.val := by omega
            step as ⟨nid,readId⟩
            rw [← getElem!_pos] at readId
            step as ⟨ids',setId⟩
            step as ⟨digit,readDigit⟩
            rw [← getElem!_pos,slot _ _ _ _ within,ite_eq_right (by omega)] at readDigit
            step as ⟨steps',setDigit⟩
            have cap := c.small
            step with move_digest s act' l c.n (less.trans_le match'.room) within (by have := c.count;omega) as ⟨s',moved⟩
            refine ⟨⟨swapped st l.val,?_,by omega,?_⟩,by omega⟩
            · rw [write,setId,setDigit]
              apply swap_matches match' alive act' nid bump digit dec moving
                (by rw [readId,match'.ident _ less]) (by rw [readDigit,match'.step _ less]) c.small c.align _ output
              simpa only [c.count] using moved
            · rw [← target]
              unfold Schedule.finalState
              rw [post_remove st l.val c.init c.start (fun _=>15) c.ids (by rw [← match'.act];exact alive) finished
                (by rw [← match'.idx,c.size];exact pending),ite_eq_left (by rw [← match'.act,← dec];exact moving)]
          · simp only [relocate,ite_false,WP.spec_ok]
            have last : act'.val≤l.val := Nat.le_of_not_lt relocate
            refine ⟨⟨removed st l.val,?_,by omega,?_⟩,by omega⟩
            · rw [write]
              exact remove_matches match' alive act' bump dec last output
            · rw [← target]
              unfold Schedule.finalState
              rw [post_remove st l.val c.init c.start (fun _=>15) c.ids (by rw [← match'.act];exact alive) finished
                (by rw [← match'.idx,c.size];exact pending),ite_eq_right (by rw [← match'.act,← dec];exact relocate)]
      · simp only [done,ite_false]
        have nonzero : bump.val≠15 := fun eq => done (UScalar.eq_of_val_eq eq)
        have cap := c.small
        step with save_digest s v l c.n within (by have := c.count;omega) as ⟨v',saved⟩
        step as ⟨l',incr⟩
        refine ⟨⟨advanced st l.val,?_,by omega,?_⟩,by omega⟩
        · rw [incr]
          exact advance_matches match' alive bump bumpEq (by omega) c.small c.align (by simpa only [c.count] using saved)
        · rw [← target]
          unfold Schedule.finalState
          rw [post_advance st l.val c.init c.start (fun _=>15) c.ids (by rw [← match'.act];exact alive) (by omega),incr]
    · simp only [live,ite_false,step_simps]
      have eq : l.val=active.val := Nat.le_antisymm cursor (Nat.le_of_not_lt live)
      have finalEq : st=final := by
        rw [← target,Schedule.finalState,postLoop,dite_eq_right (by rw [← match'.act];exact live)]
      change Matches c.digits.length final active.val tips next active ids steps v s
      rw [← finalEq,← eq]
      exact match'
  · exact ⟨g,prior,cursor,rfl⟩

end slhdsa.NativeVerify.Wots
