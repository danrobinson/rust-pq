import Cachepath.NativeVerify.WotsInner
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch Shakeopt.WotsRefill
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [machine : Machine] [accel : Dispatch machine]

def work {N : Usize} (c : Schedule N) (next active : Usize) (steps : Steps) : Nat :=
  ((List.range active.val).map (fun l=>15-steps.val[l]!.val)).sum + queuedRem c.start (fun _=>15) c.ids next.val

theorem work_eq {N : Usize} (c : Schedule N) {g : RefillState} {cursor : Nat} {tips : Tips N}
    {next active : Usize} {ids : Ids} {steps : Steps} {v : LaneValues machine.width} {s : State}
    (prior : Matches c.digits.length g cursor tips next active ids steps v s) :
    work c next active steps=totalRem c.start (fun _=>15) c.ids g := by
  unfold work totalRem activeRem
  rw [prior.idx,← prior.act]
  congr 2
  apply List.map_congr_left
  intro l hl
  have valid := List.mem_range.mp hl
  rw [prior.step _ valid,prior.ends _ valid]

theorem after_round {N : Usize} (p : params.Params) (hp : PN p N) (c : Schedule N)
    (seed : Array U8 N) (a : address.Adrs) (offset pad : Usize) (sw aw : Array U64 4#usize)
    (g : RefillState) (tips : Tips N) (next active : Usize) (ids : Ids) (steps : Steps)
    (v : LaneValues machine.width) (s out : State)
    (prior : Matches c.digits.length g active.val tips next active ids steps v s)
    (off : offset.val=c.n.val+4) (padding : pad.val=offset.val+c.n.val)
    (seedWords : ∀ k<c.n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addrWords : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (layout : RoundLayout c.n offset pad active sw aw ids steps v out) :
    Matches c.digits.length (permuteActiveStep (Shake.params p) (bytes seed.val) (adrsS a) g)
      0 tips next active ids steps v out := by
  refine ⟨prior.act,prior.idx,prior.room,prior.ident,prior.step,prior.inside,prior.valid,prior.ends,
    (by intro l _ h;omega),?_,prior.output⟩
  intro l live _
  obtain ⟨b,data,words⟩ := prior.prepared l live live
  have hash := round_fips seed a c.n offset pad active sw aw ids steps v out c.small c.align c.count
    off padding seedWords addrWords layout l live b (by simpa only [c.count] using words)
  have id := prior.ident l live
  have step := prior.step l live
  have inside := prior.inside l live
  have bounded := c.bound
  have cast : (UScalar.cast .U32 ids.val[l]!).val=g.laneId l := by
    rw [UScalar.cast_val_eq,Nat.mod_eq_of_lt (by change _<4294967296;omega),id]
  have dom : (adrsS {a with word2:=UScalar.cast .U32 ids.val[l]!,word3:=steps.val[l]!}) =
      {adrsS a with word2:=g.laneId l,word3:=g.laneStep l} := by simp only [adrsS,cast,step]
  simp only [permuteActiveStep,ite_eq_left (by rw [← prior.act];exact live : l<g.active)]
  simpa only [digest,dom,data,Spec.F,Shake.params,paramsS_n,hp.n_eq,List.append_assoc] using hash

def Schedule.semantic {N : Usize} (c : Schedule N) (p : params.Params) (seed : Array U8 N) (a : address.Adrs) :=
  OuterInv (Shake.params p) (bytes seed.val) (adrsS a) c.digits.length c.init c.start (fun _=>15) c.ids

theorem finish {N : Usize} (c : Schedule N) (p : params.Params) (seed : Array U8 N) (a : address.Adrs)
    (g : RefillState) (semantic : c.semantic p seed a g) (empty : g.active=0)
    (small : ∀ i<c.digits.length, c.start i≤15)
    (ordered : ∀ i, i ∈ c.ids ↔ (i<c.digits.length ∧ c.start i<15)) :
    ∀ i<c.digits.length, g.out i=recoveredChain p c.sig seed a c.digits.val i := by
  intro i hi
  by_cases more : c.start i<15
  · have member := (ordered i).mpr ⟨hi,more⟩
    have allDone := semantic.2.1 empty
    exact semantic.2.2.2.2.1 i (by simpa [allDone] using member) (by intro l live;omega)
  · have last : c.start i=15 := by have := small i hi;omega
    rw [semantic.2.2.2.2.2 i hi last]
    change _ = Spec.chain _ _ (c.start i) (15-c.start i) _ _
    simp [last,Spec.chain,Schedule.init]

abbrev OuterTuple (N : Usize) := Tips N × Usize × Usize × Ids × Steps × LaneValues machine.width × State

theorem engine {N : Usize} (p : params.Params) (hp : PN p N) (c : Schedule N)
    (seed : Array U8 N) (a : address.Adrs) (offset pad : Usize) (sw aw : Array U64 4#usize)
    (g : RefillState) (tips : Tips N) (next active : Usize) (ids : Ids) (steps : Steps)
    (v : LaneValues machine.width) (s : State)
    (prior : Matches c.digits.length g active.val tips next active ids steps v s)
    (semantic : c.semantic p seed a g) (off : offset.val=c.n.val+4) (padding : pad.val=offset.val+c.n.val)
    (seedWords : ∀ k<c.n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addrWords : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (small : ∀ i<c.digits.length, c.start i≤15) (unique : c.ids.Nodup)
    (ordered : ∀ i, i ∈ c.ids ↔ (i<c.digits.length ∧ c.start i<15)) (permutes : ActiveCorrect machine accel.permute) :
    recover_loop2 c.sig c.digits c.n offset sw aw tips c.order c.total next active ids steps v s pad
      ⦃ out => ∀ i<c.digits.length, bytes out.val[i]!.val=recoveredChain p c.sig seed a c.digits.val i ⦄ := by
  let inv : OuterTuple N → Prop := fun ⟨tips,next,active,ids,steps,v,s⟩=>∃ st,
    Matches c.digits.length st active.val tips next active ids steps v s ∧ c.semantic p seed a st
  unfold recover_loop2
  apply loop.spec_decr_nat (measure := fun x : OuterTuple N => work c x.2.1 x.2.2.1 x.2.2.2.2.1) (inv:=inv)
  · rintro ⟨tips,next,active,ids,steps,v,s⟩ ⟨st,mat,sem⟩
    change Matches c.digits.length st active.val tips next active ids steps v s at mat
    change c.semantic p seed a st at sem
    change recover_loop2.body c.sig c.digits c.n offset sw aw c.order c.total pad tips next active ids steps v s ⦃ r => _ ⦄
    rw [body_round]
    by_cases live : active>0#usize
    · simp only [live,ite_true]
      apply round_layout c.n offset pad active sw aw ids steps v s (by have := c.small;have := c.count;omega)
        off padding mat.room permutes
      intro out hash
      let stepped := permuteActiveStep (Shake.params p) (bytes seed.val) (adrsS a) st
      have inner : Matches c.digits.length stepped 0 tips next active ids steps v out :=
        after_round p hp c seed a offset pad sw aw st tips next active ids steps v s out mat off padding seedWords addrWords hash
      let final := c.finalState 0 stepped
      obtain ⟨⟨tt,nn,aa,ii,ss,vv,state⟩,run,done⟩ := spec_imp_exists
        (scan c stepped tips next active ids steps v out 0#usize inner (by simp))
      rw [run]
      simp only [bind_ok,step_simps]
      change Matches c.digits.length final aa.val tt nn aa ii ss vv state at done
      have progress := outer_progress (Shake.params p) (bytes seed.val) (adrsS a) c.digits.length c.init c.start
        (fun _=>15) c.ids unique (fun i hi=>(ordered i).mp hi) st sem
      refine ⟨⟨final,done,progress.1⟩,?_⟩
      change work c nn aa ss<work c next active steps
      rw [work_eq c done,work_eq c mat]
      have decrease : totalRem c.start (fun _=>15) c.ids final + st.active=totalRem c.start (fun _=>15) c.ids st := progress.2
      have positive : st.active>0 := by rw [← mat.act];exact live
      omega
    · simp only [live,ite_false,step_simps]
      have empty : st.active=0 := by rw [← mat.act];change ¬0<active.val at live;omega
      intro i hi
      rw [mat.output _ hi,finish c p seed a st sem empty small ordered i hi]
  · exact ⟨g,prior,semantic⟩

end slhdsa.NativeVerify.Wots
