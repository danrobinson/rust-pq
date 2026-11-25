import Cachepath.NativeShakeWots.SignMoves
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots.Signer
open ShakeBatch Shakeopt.WotsRefill NativeVerify NativeVerify.Wots
set_option linter.concreteInstances false
set_option maxHeartbeats 1800000
variable [machine : Machine]

abbrev InnerTuple (N : Usize) := Signature × State × Usize × Usize × Ids × Steps × Steps × LaneValues machine.width × Usize

def Schedule.finalState {N : Usize} (c : Schedule N) (i : Nat) (g : RefillState) :=
  postLoop c.source (fun _=>0) c.ending c.ids i g

theorem scan {N : Usize} (c : Schedule N) (g : RefillState)
    (tips : Signature) (next active : Usize) (ids : Ids) (steps ends : Steps)
    (values : LaneValues machine.width) (s : State) (cur : Usize)
    (prior : Matches (N:=N) c.digits.length g cur.val tips next active ids steps ends values s) (cursor : cur.val≤active.val) :
    sign_loop2_loop3 N c.digits c.n tips c.secrets s c.order c.total next active ids steps ends values cur
      ⦃ tips' s' next' active' ids' steps' ends' vals' => Matches (N:=N) c.digits.length (c.finalState cur.val g) active'.val
        tips' next' active' ids' steps' ends' vals' s' ⦄ := by
  let final := c.finalState cur.val g
  let inv : InnerTuple N → Prop := fun ⟨tips,s,next,active,ids,steps,ends,v,l⟩ => ∃ st,
    Matches (N:=N) c.digits.length st l.val tips next active ids steps ends v s ∧ l.val≤active.val ∧ c.finalState l.val st=final
  unfold sign_loop2_loop3
  apply loop.spec_decr_nat (measure := fun x : InnerTuple N => x.2.2.2.1.val-x.2.2.2.2.2.2.2.2.val) (inv := inv)
  · rintro ⟨tips,s,next,active,ids,steps,ends,v,l⟩ ⟨st,match',cursor,target⟩
    change Matches (N:=N) c.digits.length st l.val tips next active ids steps ends v s at match'
    change l.val≤active.val at cursor
    change c.finalState l.val st=final at target
    unfold sign_loop2_loop3.body
    by_cases live : l<active
    · simp only [live,ite_true]
      have alive : l.val<active.val := live
      have bounded := c.bound
      have ordered := c.size
      have width := match'.room
      have within := alive.trans_le match'.room
      have value := match'.step l.val alive
      have limit := match'.valid l.val alive
      have ending := match'.endsAt l.val alive
      have maxStep := match'.bound l.val alive
      step as ⟨old,getOld⟩
      rw [← getElem!_pos] at getOld
      step as ⟨bump,bi⟩
      have bumpEq : bump.val=st.laneStep l.val+1 := by rw [bi,getOld,value]
      step as ⟨steps',wroteStep⟩
      step as ⟨bump',readBack⟩
      have rb : bump'=bump := by
        rw [← getElem!_pos,wroteStep,slot _ _ _ _ within,ite_eq_left rfl] at readBack
        exact readBack
      step as ⟨endAt,readEnd⟩
      rw [← getElem!_pos] at readEnd
      rw [rb]
      subst steps'
      by_cases done : bump=endAt
      · rw [ite_eq_left done]
        have finished : st.laneStep l.val+1=st.laneEnd l.val := by rw [← bumpEq,done,readEnd,ending]
        step as ⟨id,which⟩
        rw [← getElem!_pos] at which
        have idEq : id.val=st.laneId l.val := by simpa [which] using match'.ident _ alive
        have inside := match'.inside _ alive
        have cap : c.digits.length*N.val≤67*32 := Nat.mul_le_mul c.bound c.small
        have inside' : id.val<c.digits.length := idEq ▸ inside
        have fits : (id.val+1)*N.val ≤ tips.length := match'.lenEq ▸ Nat.mul_le_mul_right N.val inside'
        step as ⟨pos,pv⟩
        all_goals try scalar_tac
        step as ⟨up,uv⟩
        step as ⟨stop,sv⟩
        all_goals try scalar_tac
        step as ⟨slice,back,read,len,wr⟩
        step with extract_digest N s l c.small c.align within as ⟨blob,digestEq⟩
        simp only [lift,bind_ok]
        step as ⟨stored,cp⟩
        all_goals try (simp [pv,sv,uv,Nat.add_mul] at *;omega)
        have write : (back stored).val=tips.val.setSlice! (id.val*N.val) blob.val := by
          rw [wr,cp];simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,Array.val_to_slice,pv]
        obtain ⟨lenEq,updated⟩ := block_store blob tips (back stored) _ id.val match'.lenEq inside' write
        have output : ∀ j<c.digits.length, ∀ b<N.val, Block (back stored) N.val j b=(wrote st l.val j)[b]! := by
          intro j hj b hb
          rw [updated j hj b hb,wrote]
          by_cases h : j=id.val
          · rw [ite_eq_left h,ite_eq_left (h.trans idEq),digestEq,match'.pending l.val alive (by omega)]
          · rw [ite_eq_right h,ite_eq_right (by omega)];exact match'.output j hj b hb
        by_cases pending : next<c.total
        · simp only [pending,ite_true]
          have left : next.val<c.total.val := pending
          have ⟨nidGood,nonzero,boundedDigit,secret⟩ := c.queued next.val left
          step as ⟨nid,readNid⟩
          rw [← getElem!_pos] at readNid
          have nidEq : nid.val=c.ids[st.next]! := by rw [← match'.idx,c.get _ left,readNid]
          have good : nid.val<c.digits.length := by simpa only [readNid] using nidGood
          step as ⟨next',inc⟩
          step as ⟨ids',setId⟩
          step as ⟨steps',setStep⟩
          step as ⟨digit,readDigit⟩
          rw [← getElem!_pos] at readDigit
          step as ⟨ends',setEnd⟩
          step as ⟨word,row⟩
          rw [← getElem!_pos] at row
          step as ⟨v',setVal⟩
          step as ⟨l',incr⟩
          refine ⟨⟨replaced st l.val nid.val c.source (fun _=>0) c.ending,?_,by omega,?_⟩,by omega⟩
          · rw [incr,setId,setStep,setEnd,setVal]
            apply replace_matches match' alive c.source c.ending next' nid digit bump (by rw [inc,match'.idx]) good
              (by rw [readDigit];rfl) (by simpa [Schedule.ending,readNid] using nonzero)
              (by simpa [Schedule.ending,readNid] using boundedDigit) _ _ lenEq output
            · obtain ⟨buf,eq,ws⟩ := secret
              refine ⟨buf,by simpa only [readNid] using eq,?_⟩
              intro k hk
              unfold laneWord
              rw [slot _ _ _ _ within,ite_eq_left rfl,row,readNid,ws k hk]
            · intro j ne k hk; unfold laneWord;rw [slot _ _ _ _ within,ite_eq_right ne]
          · rw [← target,incr]
            unfold Schedule.finalState
            rw [post_replace st l.val c.source (fun _=>0) c.ending c.ids (by rw [← match'.act];exact alive) finished
              (by rw [← match'.idx,c.length];exact left),← nidEq]
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
            step as ⟨lastEnd,ee⟩
            rw [← getElem!_pos] at ee
            step as ⟨ends',setEnd⟩
            have cap := c.small
            rw [show sign_loop2_loop3_loop0 ⟨0#usize,c.n⟩ s act' l = recover_loop2_loop3_loop1 ⟨0#usize,c.n⟩ act' s l from rfl]
            step with move_digest s act' l c.n (less.trans_le match'.room) within (by have := c.count;omega) as ⟨s',moved⟩
            refine ⟨⟨swapped st l.val,?_,by omega,?_⟩,by omega⟩
            · rw [setId,setDigit,setEnd]
              apply swap_matches match' alive act' nid bump digit lastEnd dec moving
                (by rw [readId,match'.ident _ less]) (by rw [readDigit,match'.step _ less]) (by rw [ee,match'.endsAt _ less]) c.small c.align _ lenEq output
              simpa only [c.count] using moved
            · rw [← target]
              unfold Schedule.finalState
              rw [post_remove st l.val c.source (fun _=>0) c.ending c.ids (by rw [← match'.act];exact alive) finished
                (by rw [← match'.idx,c.length];exact pending),ite_eq_left (by rw [← match'.act,← dec];exact moving)]
          · simp only [relocate,ite_false,WP.spec_ok]
            have last : act'.val≤l.val := Nat.le_of_not_lt relocate
            refine ⟨⟨removed st l.val,?_,by omega,?_⟩,by omega⟩
            · exact remove_matches match' alive act' bump dec last lenEq output
            · rw [← target]
              unfold Schedule.finalState
              rw [post_remove st l.val c.source (fun _=>0) c.ending c.ids (by rw [← match'.act];exact alive) finished
                (by rw [← match'.idx,c.length];exact pending),ite_eq_right (by rw [← match'.act,← dec];exact relocate)]
      · simp only [done,ite_false]
        have nonzero : bump.val≠st.laneEnd l.val := fun eq => done (UScalar.eq_of_val_eq (by rw [readEnd,ending,eq]))
        have cap := c.small
        rw [show sign_loop2_loop3_loop1 ⟨0#usize,c.n⟩ s v l = recover_loop2_loop3_loop2 ⟨0#usize,c.n⟩ v s l from rfl]
        step with save_digest s v l c.n within (by have := c.count;omega) as ⟨v',saved⟩
        step as ⟨l',incr⟩
        refine ⟨⟨advanced st l.val,?_,by omega,?_⟩,by omega⟩
        · rw [incr]
          exact advance_matches match' alive bump bumpEq (by omega) c.small c.align (by simpa only [c.count] using saved)
        · rw [← target]
          unfold Schedule.finalState
          rw [post_advance st l.val c.source (fun _=>0) c.ending c.ids (by rw [← match'.act];exact alive) (by omega),incr]
    · simp only [live,ite_false,step_simps]
      have eq : l.val=active.val := Nat.le_antisymm cursor (Nat.le_of_not_lt live)
      have finalEq : st=final := by
        rw [← target,Schedule.finalState,postLoop,dite_eq_right (by rw [← match'.act];exact live)]
      change Matches (N:=N) c.digits.length final active.val tips next active ids steps ends v s
      rw [← finalEq,← eq]
      exact match'
  · exact ⟨g,prior,cursor,rfl⟩

end slhdsa.NativeShakeWots.Signer
