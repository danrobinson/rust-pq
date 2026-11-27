import Parallel.WorkerPayloadHeap

open Aeneas Aeneas.Std Result
namespace slhdsa.WorkerPayload
open WidthEight.Ticket ParallelWorkerHeap ParallelSignJoin

def forestHost : Host → ParallelRootWalk.Host
  | .apple sha3 => .apple sha3
  | .x86 => .x86
  | .linuxArm => .linuxArm

noncomputable def prepare (host : Host) (schedule : Schedules) : PhaseOne :=
  match host with
  | .apple sha3 => rootsFrom (.apple sha3) (ParallelRawWorker.native (.apple sha3) schedule)
  | .x86 => rootsFrom .x86 (ParallelRawWorker.native .x86 schedule)
  | .linuxArm => ThreeLane.slhdsa.WidthEight.Ticket.rootsFrom .linuxArm (ParallelRawWorker.native .linuxArm schedule)

private theorem bind_success (x : Result α) (f : α → Result β) {b}
    (eq : (x >>= f) = ok b) : ∃ a, x = ok a ∧ f a = ok b := by
  cases x with
  | ret a => exact ⟨a,rfl,by simpa using eq⟩
  | div => simp_all
  | vis e k => cases e with | fail e => simp_all

private theorem native_order {N : Usize} (host : ParallelRootWalk.Host) (schedule : Schedules) (p : params.Params)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32)
    (threads : Usize) {s} (ran : ParallelRawWorker.native host schedule p md sk seed a r tree leaf threads = ok s) :
    s.completed = (schedule.wots p.d.val).completed := by
  unfold ParallelRawWorker.native ParallelRawWorker.inputsFrom ParallelRawWorker.assemble at ran
  obtain ⟨_,_,ran⟩ := bind_success _ _ ran
  obtain ⟨_,_,ran⟩ := bind_success _ _ ran
  obtain ⟨⟨_,_⟩,_,ran⟩ := bind_success _ _ ran
  obtain ⟨_,_,ran⟩ := bind_success _ _ ran
  obtain ⟨_,_,ran⟩ := bind_success _ _ ran
  cases Result.ok_injective ran
  rfl

noncomputable def rootValues {N : Usize} (host : Host) (p : params.Params) (md : Slice U8)
    (seed : Array U8 N) (a : address.Adrs) (tree : U64) (leaf : U32) (s : ForestInputs N) :=
  match host with
  | .apple sha3 => rootInputs (.apple sha3) p md seed a tree leaf s
  | .x86 => rootInputs .x86 p md seed a tree leaf s
  | .linuxArm => ThreeLane.slhdsa.WidthEight.Ticket.rootInputs .linuxArm p md seed a tree leaf s

private theorem root_order {N : Usize} (host : Host) (p : params.Params) (md : Slice U8)
    (seed : Array U8 N) (a : address.Adrs) (tree : U64) (leaf : U32) (s : ForestInputs N)
    {t} (ran : rootValues host p md seed a tree leaf s = ok t) : t.completed=s.completed := by
  cases host <;> unfold rootValues at ran
  all_goals unfold rootInputs at ran
  all_goals
    obtain ⟨_,_,ran⟩ := bind_success _ _ ran
    obtain ⟨_,_,ran⟩ := bind_success _ _ ran
    cases Result.ok_injective ran
    rfl

/-- Native phase-one preparation computes the actual reducer values and carries
the exact WOTS completion order selected by the shared ticket session. -/
theorem prepare_native (host : Host) (schedule : Schedules) {N : Usize} (p : params.Params) (hp : PN p N)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32)
    (threads : Usize) (enabled : 2≤threads.val) (mdLen : md.length=(Shake.params p).mdBytes)
    (treeLt : tree.val<2^(p.h.val-p.hp.val)) (leafLt : leaf.val<2^p.hp.val)
    (address : adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear Spec.FORS_TREE with keypair:=leaf.val}) :
    ∃ s, prepare host schedule p md sk seed a r tree leaf threads=ok s ∧
      InputsCorrect p md sk seed a tree leaf s ∧ s.completed = (schedule.wots p.d.val).completed := by
  have domain : a.typ=slhdsa.address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32 :=
    ⟨UScalar.eq_of_val_eq (by simpa [adrsS,Spec.Adrs.setTypeAndClear,Spec.FORS_TREE,global_simps] using congrArg Spec.Adrs.typ address),
      UScalar.eq_of_val_eq (congrArg Spec.Adrs.word2 address),UScalar.eq_of_val_eq (congrArg Spec.Adrs.word3 address)⟩
  obtain ⟨s,ran,good⟩ := spec_imp_exists
    (ParallelRawWorker.native_law (forestHost host) schedule p hp md sk seed a r tree leaf threads
      enabled mdLen treeLt leafLt address)
  change ParallelRawWorker.native (forestHost host) schedule p md sk seed a r tree leaf threads = ok s at ran
  have stored := native_order (forestHost host) schedule p md sk seed a r tree leaf threads ran
  have rootsOk : rootValues host p md seed a tree leaf s ⦃ t => InputsCorrect p md sk seed a tree leaf t ⦄ := by
    cases host with
    | apple f => exact root_inputs (.apple f) p hp md sk seed a tree leaf s mdLen leafLt domain good
    | x86 => exact root_inputs .x86 p hp md sk seed a tree leaf s mdLen leafLt domain good
    | linuxArm => exact ThreeLane.slhdsa.WidthEight.Ticket.root_inputs .linuxArm p hp md sk seed a tree leaf s mdLen leafLt domain good
  obtain ⟨t,root,correct⟩ := spec_imp_exists rootsOk
  have eq : prepare host schedule p md sk seed a r tree leaf threads =
      (do let q ← ParallelRawWorker.native (forestHost host) schedule p md sk seed a r tree leaf threads
          rootValues host p md seed a tree leaf q) := by cases host <;> rfl
  exact ⟨t,by rw [eq,ran,bind_ok,root],correct,(root_order host p md seed a tree leaf s root).trans stored⟩

noncomputable def nativeJoin (host : Host) (schedule : Schedules) : Join :=
  match host with
  | .apple sha3 => ParallelApple.slhdsa.WidthEight.ParallelSign.joinedPlan (.apple sha3) schedule
  | .x86 => ParallelX86.slhdsa.WidthEight.ParallelSign.joinedPlan .x86 schedule
  | .linuxArm => linuxJoin schedule

private theorem join_eq {N : Usize} (host : Host) (schedule : Schedules) (p : params.Params)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32)
    (threads : Usize) {s} (prepared : prepare host schedule p md sk seed a r tree leaf threads=ok s)
    {out} (complete : nativePhaseTwo host p sk seed s.layers s.roots s.completed=ok out) :
    nativeJoin host schedule p md sk seed a r tree leaf threads=ok (some s.forest,some s.auth,out) := by
  have body : nativeJoin host schedule p md sk seed a r tree leaf threads = (do
      let t ← prepare host schedule p md sk seed a r tree leaf threads
      let w ← nativePhaseTwo host p sk seed t.layers t.roots t.completed
      ok (some t.forest,some t.auth,w)) := by cases host <;> rfl
  rw [body,prepared,bind_ok,complete,bind_ok]

/-- The host's full native preparation supplies the reducer outputs. A successful
Rust wait and the specified queue history admit a shared-heap execution whose
actual extracted public worker returns the same bytes as the heap reader. -/
theorem wait_to_native_signature {N : Usize} (host : Host) (p : params.Params) (hp : PN p N)
    (runs : WorkerFetch.SigningRuns p) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs)
    (r : Array U8 N) (tree : U64) (leaf : U32) (threads : Usize) (enabled : 2≤threads.val)
    (mdLen : md.length=(Shake.params p).mdBytes) (treeLt : tree.val<2^(p.h.val-p.hp.val))
    (leafLt : leaf.val<2^p.hp.val)
    (address : adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear Spec.FORS_TREE with keypair:=leaf.val}) :
    ∃ s, prepare host runs.toSession.schedules p md sk seed a r tree leaf threads=ok s ∧
      ∀ (base : Heap N) {h : Monitor N} {g decode facts pc seen} (_cert : WorkerBarrierMir.Certified g decode facts),
        WorkerBarrierMir.Interleaved s.forest s.auth s.roots g decode h pc seen →
        ∀ (valid : pc<g.length), decode g[pc].ops = .accept →
        base.cells .sigFors=none → base.cells .xmssAuth=none → base.cells .roots=none →
        base.counts .phase2Next=0 → (∀ i, base.cells (.wotsSigs i)=none) →
        ∃ final : Heap N, Relation.ReflTransGen BarrierAction base (barrierHeap base h) ∧
          Relation.ReflTransGen WotsAction (barrierHeap base h) final ∧
          ∃ signature,
            ParallelSignJoin.run (ok threads) (nativeJoin host runs.toSession.schedules) p md sk seed a r tree leaf=ok (some signature) ∧
            ParallelSignJoin.run (ok threads) (heapJoin final) p md sk seed a r tree leaf=ok (some signature) ∧
            bytes signature.val=bytes r.val ++ Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val)
              (bytes seed.val) (adrsS a) ++ Spec.htSign (Shake.params p)
                (Spec.forsPkFromSig (Shake.params p)
                  (Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a))
                  (bytes md.val) (bytes seed.val) (adrsS a)) (bytes sk.val) (bytes seed.val) tree.val leaf.val := by
  let schedule := runs.toSession.schedules
  obtain ⟨s,prepared,correct,order⟩ := prepare_native host schedule p hp md sk seed a r tree leaf threads enabled mdLen treeLt leafLt address
  refine ⟨s,prepared,?_⟩
  intro base h g decode facts pc seen cert exec valid accept fc ac rc zero fresh
  have exactOrder : s.completed=runs.phaseTwo.log := order.trans runs.toSession.orders.2.2.2
  obtain ⟨final,barrier,path,forest,auth,computed,sig,heapReturn,signature⟩ := wait_to_signature
    host p hp base md sk seed a r tree leaf leafLt s correct cert exec valid accept fc ac rc zero fresh
    runs.phaseTwo.run runs.positive runs.phaseTwo.retired threads enabled
  have native := join_eq host schedule p md sk seed a r tree leaf threads prepared (exactOrder.symm ▸ computed)
  have observed : nativeJoin host schedule p md sk seed a r tree leaf threads =
      heapJoin final p md sk seed a r tree leaf threads := by simpa [heapJoin,forest,auth] using native
  refine ⟨final,barrier,path,sig,?_,heapReturn,signature⟩
  change ParallelSignJoin.run (ok threads) (nativeJoin host schedule) p md sk seed a r tree leaf=_
  simpa only [ParallelSignJoin.run,bind_ok,observed] using heapReturn

/-- The production gate exhibits an accepting wait run for arbitrary reducer outputs. -/
def Accepting (N : Usize) (g : ParallelWorkerMir.Graph) (decode : Nat → WorkerBarrierMir.Op) : Prop :=
  ∀ (f : alloc.vec.Vec U8) (a r : alloc.vec.Vec (Array U8 N)),
    ∃ (h : Monitor N) (pc : Nat) (seen : WorkerBarrierMir.Seen),
      WorkerBarrierMir.Interleaved f a r g decode h pc seen ∧ ∃ valid : pc<g.length, decode g[pc].ops=.accept

/-- The accepting CFG witness eliminates the control-flow premise. For every
normal queue schedule, derive the native phase-one outputs and exhibit a
complete barrier-to-signature execution, together with the exact FIPS bytes. -/
theorem native_signature {N : Usize} {g decode facts} (cert : WorkerBarrierMir.Certified g decode facts)
    (accepts : Accepting N g decode) (host : Host) (p : params.Params) (hp : PN p N)
    (runs : WorkerFetch.SigningRuns p) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs)
    (r : Array U8 N) (tree : U64) (leaf : U32) (threads : Usize) (enabled : 2≤threads.val)
    (mdLen : md.length=(Shake.params p).mdBytes) (treeLt : tree.val<2^(p.h.val-p.hp.val))
    (leafLt : leaf.val<2^p.hp.val)
    (address : adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear Spec.FORS_TREE with keypair:=leaf.val})
    (base : Heap N) (fc : base.cells .sigFors=none) (ac : base.cells .xmssAuth=none)
    (rc : base.cells .roots=none) (zero : base.counts .phase2Next=0) (fresh : ∀ i, base.cells (.wotsSigs i)=none) :
    ∃ (s : PublishedInputs N) (h : Monitor N) (pc : Nat) (seen : WorkerBarrierMir.Seen) (final : Heap N) (signature : alloc.vec.Vec U8),
      prepare host runs.toSession.schedules p md sk seed a r tree leaf threads=ok s ∧
      WorkerBarrierMir.Interleaved s.forest s.auth s.roots g decode h pc seen ∧
      (∃ valid : pc<g.length, decode g[pc].ops=.accept) ∧
      Relation.ReflTransGen BarrierAction base (barrierHeap base h) ∧
      Relation.ReflTransGen WotsAction (barrierHeap base h) final ∧
      ParallelSignJoin.run (ok threads) (nativeJoin host runs.toSession.schedules) p md sk seed a r tree leaf=ok (some signature) ∧
      ParallelSignJoin.run (ok threads) (heapJoin final) p md sk seed a r tree leaf=ok (some signature) ∧
      bytes signature.val=bytes r.val ++ Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val)
        (bytes seed.val) (adrsS a) ++ Spec.htSign (Shake.params p)
          (Spec.forsPkFromSig (Shake.params p)
            (Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a))
            (bytes md.val) (bytes seed.val) (adrsS a)) (bytes sk.val) (bytes seed.val) tree.val leaf.val := by
  obtain ⟨s,prepared,run⟩ := wait_to_native_signature host p hp runs md sk seed a r tree leaf threads enabled mdLen treeLt leafLt address
  obtain ⟨h,pc,seen,exec,valid,accept⟩ := accepts s.forest s.auth s.roots
  obtain ⟨final,barrier,path,sig,native,heap,signature⟩ := run base cert exec valid accept fc ac rc zero fresh
  exact ⟨s,h,pc,seen,final,sig,prepared,exec,⟨valid,accept⟩,barrier,path,native,heap,signature⟩

end slhdsa.WorkerPayload
