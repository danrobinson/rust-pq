import Cachepath.NativeShakeWots.SignScan
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots.Signer
open ShakeBatch Shakeopt.WotsRefill NativeVerify NativeVerify.Wots
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [machine : Machine] [accel : Dispatch machine]

def work {N : Usize} (c : Schedule N) (next active : Usize) (steps ends : Steps) : Nat :=
  ((List.range active.val).map (fun l=>ends.val[l]!.val-steps.val[l]!.val)).sum + queuedRem (fun _=>0) c.ending c.ids next.val

theorem work_eq {N : Usize} (c : Schedule N) {g : RefillState} {cursor : Nat} {tips : Signature}
    {next active : Usize} {ids : Ids} {steps ends : Steps} {v : LaneValues machine.width} {s : State}
    (prior : Matches (N:=N) c.digits.length g cursor tips next active ids steps ends v s) :
    work c next active steps ends=totalRem (fun _=>0) c.ending c.ids g := by
  unfold work totalRem activeRem
  rw [prior.idx,← prior.act]
  congr 2
  apply List.map_congr_left
  intro l hl
  have valid := List.mem_range.mp hl
  rw [prior.step _ valid,prior.endsAt _ valid]

theorem after_round {N : Usize} (p : params.Params) (hp : PN p N) (c : Schedule N)
    (seed : Array U8 N) (a : address.Adrs) (offset pad : Usize) (sw aw : Array U64 4#usize)
    (g : RefillState) (tips : Signature) (next active : Usize) (ids : Ids) (steps ends : Steps)
    (v : LaneValues machine.width) (s out : State)
    (prior : Matches (N:=N) c.digits.length g active.val tips next active ids steps ends v s)
    (off : offset.val=c.n.val+4) (padding : pad.val=offset.val+c.n.val)
    (seedWords : ∀ k<c.n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addrWords : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (layout : RoundLayout c.n offset pad active sw aw ids steps v out) :
    Matches (N:=N) c.digits.length (permuteActiveStep (Shake.params p) (bytes seed.val) (adrsS a) g)
      0 tips next active ids steps ends v out := by
  refine ⟨prior.act,prior.idx,prior.room,prior.ident,prior.step,prior.inside,prior.valid,prior.endsAt,prior.bound,
    (by intro l _ h;omega),?_,prior.lenEq,prior.output⟩
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
  OuterInv (Shake.params p) (bytes seed.val) (adrsS a) c.digits.length c.source (fun _=>0) c.ending c.ids

def expected {N : Usize} (c : Schedule N) (p : params.Params) (seed : Array U8 N) (a : address.Adrs) (id : Nat) :=
  Spec.chain (Shake.params p) (c.source id) 0 (c.ending id) (bytes seed.val) {adrsS a with word2:=id}

theorem finish {N : Usize} (c : Schedule N) (p : params.Params) (seed : Array U8 N) (a : address.Adrs)
    (g : RefillState) (semantic : c.semantic p seed a g) (empty : g.active=0)
    (ordered : ∀ i, i ∈ c.ids ↔ (i<c.digits.length ∧ 0<c.ending i)) :
    ∀ i<c.digits.length, g.out i=expected c p seed a i := by
  intro i hi
  by_cases more : 0<c.ending i
  · have member := (ordered i).mpr ⟨hi,more⟩
    have allDone := semantic.2.1 empty
    simpa [expected] using semantic.2.2.2.2.1 i (by simpa [allDone] using member) (by intro l live;omega)
  · have zero : c.ending i=0 := by omega
    rw [semantic.2.2.2.2.2 i hi zero.symm]
    simp [expected,zero,Spec.chain]

abbrev OuterTuple := Signature × State × Usize × Usize × Ids × Steps × Steps × LaneValues machine.width

theorem body_round {N : Usize} (c : Schedule N) (offset pad : Usize) (sw aw : Array U64 4#usize)
    (sig : Signature) (next active : Usize) (ids : Ids) (steps ends : Steps) (v : LaneValues machine.width)
    (s : State) : sign_loop2.body N c.digits c.n offset sw aw c.secrets c.order c.total pad sig s next active ids steps ends v =
      (do if active>0#usize then
            round c.n offset sw aw pad active ids steps v s fun st => do
              let (sig',st',next',active',ids',steps',ends',vals') ← sign_loop2_loop3 N c.digits c.n sig c.secrets st c.order
                c.total next active ids steps ends v 0#usize
              ok (cont (sig',st',next',active',ids',steps',ends',vals'))
          else ok (done sig)) := by rfl

theorem engine {N : Usize} (p : params.Params) (hp : PN p N) (c : Schedule N)
    (seed : Array U8 N) (a : address.Adrs) (offset pad : Usize) (sw aw : Array U64 4#usize)
    (g : RefillState) (tips : Signature) (next active : Usize) (ids : Ids) (steps ends : Steps)
    (v : LaneValues machine.width) (s : State)
    (prior : Matches (N:=N) c.digits.length g active.val tips next active ids steps ends v s)
    (semantic : c.semantic p seed a g) (off : offset.val=c.n.val+4) (padding : pad.val=offset.val+c.n.val)
    (seedWords : ∀ k<c.n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addrWords : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (unique : c.ids.Nodup)
    (ordered : ∀ i, i ∈ c.ids ↔ (i<c.digits.length ∧ 0<c.ending i)) (permutes : ActiveCorrect machine accel.permute) :
    sign_loop2 N c.digits c.n offset sw aw tips c.secrets s c.order c.total next active ids steps ends v pad
      ⦃ out => out.length=c.digits.length*N.val ∧ ∀ i<c.digits.length, ∀ b<N.val, Block out N.val i b=(expected c p seed a i)[b]! ⦄ := by
  let inv : OuterTuple → Prop := fun ⟨tips,s,next,active,ids,steps,ends,v⟩=>∃ st,
    Matches (N:=N) c.digits.length st active.val tips next active ids steps ends v s ∧ c.semantic p seed a st
  unfold sign_loop2
  apply loop.spec_decr_nat (measure := fun x : OuterTuple => work c x.2.2.1 x.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1) (inv:=inv)
  · rintro ⟨tips,s,next,active,ids,steps,ends,v⟩ ⟨st,mat,sem⟩
    change Matches (N:=N) c.digits.length st active.val tips next active ids steps ends v s at mat
    change c.semantic p seed a st at sem
    change sign_loop2.body N c.digits c.n offset sw aw c.secrets c.order c.total pad tips s next active ids steps ends v ⦃ r => _ ⦄
    rw [body_round c]
    by_cases live : active>0#usize
    · simp only [live,ite_true]
      apply round_layout c.n offset pad active sw aw ids steps v s (by have := c.small;have := c.count;omega)
        off padding mat.room permutes
      intro out hash
      let stepped := permuteActiveStep (Shake.params p) (bytes seed.val) (adrsS a) st
      have inner : Matches (N:=N) c.digits.length stepped 0 tips next active ids steps ends v out :=
        after_round p hp c seed a offset pad sw aw st tips next active ids steps ends v s out mat off padding seedWords addrWords hash
      let final := c.finalState 0 stepped
      obtain ⟨⟨tt,state,nn,aa,ii,ss,ee,vv⟩,run,done⟩ := spec_imp_exists
        (scan c stepped tips next active ids steps ends v out 0#usize inner (by simp))
      rw [run]
      simp only [bind_ok,step_simps]
      change Matches (N:=N) c.digits.length final aa.val tt nn aa ii ss ee vv state at done
      have progress := outer_progress (Shake.params p) (bytes seed.val) (adrsS a) c.digits.length c.source (fun _=>0)
        c.ending c.ids unique (fun i hi=>(ordered i).mp hi) st sem
      refine ⟨⟨final,done,progress.1⟩,?_⟩
      change work c nn aa ss ee < work c next active steps ends
      rw [work_eq c done,work_eq c mat]
      have decrease : totalRem (fun _=>0) c.ending c.ids final + st.active=totalRem (fun _=>0) c.ending c.ids st := progress.2
      have positive : st.active>0 := by rw [← mat.act];exact live
      omega
    · simp only [live,ite_false,step_simps]
      have empty : st.active=0 := by rw [← mat.act];change ¬0<active.val at live;omega
      refine ⟨mat.lenEq,?_⟩
      intro i hi b hb
      rw [mat.output i hi b hb,finish c p seed a st sem empty ordered i hi]
  · exact ⟨g,prior,semantic⟩

end slhdsa.NativeShakeWots.Signer
