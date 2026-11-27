import Parallel.WorkerFetchPublic
import Parallel.SigningSlots

namespace slhdsa.WorkerPayload
open ParallelCached.Tickets

abbrev Rows (V : Type) := List (Nat × V)

/-- A worker retains the actual payload computed for each outstanding store. -/
inductive Frame (V : Type) where
  | claim
  | fetched (ticket : Nat)
  | write (rows : Rows V)

structure Machine (V : Type) where
  counter : Nat
  threads : List (Frame V)
  cells : Nat → Option V

def start {V} (workers : Nat) : Machine V :=
  ⟨0, List.replicate workers .claim, fun _ => none⟩

def pending (jobs : List (Rows V)) : Frame V → Option (Rows V)
  | .claim => some []
  | .fetched i => jobs[i]?
  | .write rows => some rows

def view (jobs : List (Rows V)) (m : Machine V) : State Nat V :=
  ⟨min m.counter jobs.length, m.counter, m.threads.filterMap (pending jobs), m.cells⟩

inductive Event (jobs : List (Rows V)) :
    Machine V → Rows V → Machine V → Rows V → Prop where
  | fetch (l r c cells log) :
    Event jobs ⟨c,l ++ .claim :: r,cells⟩ log ⟨c+1,l ++ .fetched c :: r,cells⟩ log
  | found (l r c cells log i rows) (lookup : jobs[i]? = some rows) :
    Event jobs ⟨c,l ++ .fetched i :: r,cells⟩ log ⟨c,l ++ .write rows :: r,cells⟩ log
  | exhausted (l r c cells log i) (lookup : jobs[i]? = none) :
    Event jobs ⟨c,l ++ .fetched i :: r,cells⟩ log ⟨c,l ++ r,cells⟩ log
  | set (l r c cells log k v tail) (empty : cells k = none) :
    Event jobs ⟨c,l ++ .write ((k,v)::tail) :: r,cells⟩ log
      ⟨c,l ++ .write tail :: r,fun j => if j=k then some v else cells j⟩ ((k,v)::log)
  | finish (l r c cells log) :
    Event jobs ⟨c,l ++ .write [] :: r,cells⟩ log ⟨c,l ++ .claim :: r,cells⟩ log

inductive Execution (jobs : List (Rows V)) (workers : Nat) : Machine V → Rows V → Prop where
  | begin : Execution jobs workers (start workers) []
  | next {m log m' log'} (before : Execution jobs workers m log) (step : Event jobs m log m' log') :
      Execution jobs workers m' log'

theorem Execution.reach {jobs : List (Rows V)} {workers m log} (run : Execution jobs workers m log) :
    Reach jobs workers (view jobs m) := by
  induction run with
  | begin =>
    simpa [start,view,initial,pending,List.filterMap_replicate] using
      (Reach.start : Reach jobs workers (initial workers))
  | next _ event ih =>
    cases event with
    | fetch l r c cells log =>
      by_cases live : c < jobs.length
      · have le : c+1 ≤ jobs.length := by omega
        simp [view,pending,List.getElem?_eq_getElem live,Nat.min_eq_left live.le,
          Nat.min_eq_left le] at ih ⊢
        exact ih.next (.claim _ _ _ _ _ live)
      · have last : jobs.length ≤ c := by omega
        have after : jobs.length ≤ c+1 := by omega
        simp [view,pending,List.getElem?_eq_none last,Nat.min_eq_right last,
          Nat.min_eq_right after] at ih ⊢
        exact ih.next (.retire _ _ _ _ _ rfl)
    | found l r c cells log i rows lookup => simpa [view,pending,lookup] using ih
    | exhausted l r c cells log i lookup => simpa [view,pending,lookup] using ih
    | set l r c cells log k v tail empty =>
      simp [view,pending] at ih ⊢
      exact ih.next (.store _ _ _ _ _ _ _ _ empty)
    | finish => simpa [view,pending] using ih

def eraseRows (xs : Rows V) : WorkerFetch.Rows := xs.map fun (k,_) => (k,())

def Frame.erase : Frame V → WorkerFetch.Frame
  | .claim => .claim
  | .fetched i => .fetched i
  | .write rows => .write (eraseRows rows)

def Machine.erase (m : Machine V) : WorkerFetch.Machine :=
  ⟨m.counter, m.threads.map Frame.erase, fun k => (m.cells k).map fun _ => ()⟩

theorem Event.erase {jobs : List (Rows V)} {m log m' log'}
    (step : Event jobs m log m' log') :
    WorkerFetch.Event (jobs.map eraseRows) m.erase (log.map Prod.fst) m'.erase (log'.map Prod.fst) := by
  cases step with
  | fetch => simpa [Machine.erase,Frame.erase] using WorkerFetch.Event.fetch ..
  | found l r c cells log i rows lookup =>
    simp [Machine.erase,Frame.erase]
    exact .found _ _ _ _ _ _ _ (by simp [lookup])
  | exhausted l r c cells log i lookup =>
    simp [Machine.erase,Frame.erase]
    exact .exhausted _ _ _ _ _ _ (by simp [lookup])
  | finish => simpa [Machine.erase,Frame.erase,eraseRows] using WorkerFetch.Event.finish ..
  | set l r c cells log k v tail empty =>
    simp [Machine.erase, Frame.erase,eraseRows]
    convert WorkerFetch.Event.set (jobs := jobs.map eraseRows) (l.map Frame.erase) (r.map Frame.erase)
      c (fun j => (cells j).map fun _ => ()) (log.map Prod.fst) k (eraseRows tail)
      (by simp [empty]) using 1 <;> try rfl
    apply congrArg (WorkerFetch.Machine.mk c (l.map Frame.erase ++ .write (eraseRows tail) :: r.map Frame.erase))
    funext j
    split <;> simp_all

theorem Execution.erase {jobs : List (Rows V)} {workers m log} (run : Execution jobs workers m log) :
    WorkerFetch.Execution (jobs.map eraseRows) workers m.erase (log.map Prod.fst) := by
  induction run with
  | begin => simpa [Machine.erase,start,Frame.erase,WorkerFetch.start] using WorkerFetch.Execution.begin
  | next _ step ih => exact ih.next step.erase

def decorateRows (value : Nat → V) (rows : WorkerFetch.Rows) : Rows V :=
  rows.map fun (k,_) => (k,value k)

def decorateFrame (value : Nat → V) : WorkerFetch.Frame → Frame V
  | .claim => .claim
  | .fetched i => .fetched i
  | .write rows => .write (decorateRows value rows)

def decorate (value : Nat → V) (m : WorkerFetch.Machine) : Machine V :=
  ⟨m.counter,m.threads.map (decorateFrame value),fun k => (m.cells k).map fun _ => value k⟩

private theorem decorate_step {jobs m log m' log'} (value : Nat → V)
    (step : WorkerFetch.Event jobs m log m' log') :
    Event (jobs.map (decorateRows value)) (decorate value m) (log.map fun k => (k,value k))
      (decorate value m') (log'.map fun k => (k,value k)) := by
  cases step with
  | fetch => simpa [decorate,decorateFrame] using Event.fetch ..
  | found l r c cells log i rows lookup =>
    simp [decorate,decorateFrame]
    exact .found _ _ _ _ _ _ _ (by simp [lookup])
  | exhausted l r c cells log i lookup =>
    simp [decorate,decorateFrame]
    exact .exhausted _ _ _ _ _ _ (by simp [lookup])
  | finish => simpa [decorate,decorateFrame,decorateRows] using Event.finish ..
  | set l r c cells log k tail empty =>
    simp only [decorate,List.map_append,List.map_cons,decorateFrame,decorateRows]
    convert Event.set (jobs := jobs.map (decorateRows value))
      (l.map (decorateFrame value)) (r.map (decorateFrame value)) c
      (fun j => (cells j).map fun _ => value j) (log.map fun j => (j,value j))
      k (value k) (decorateRows value tail) (by simp [empty]) using 1 <;> try rfl
    apply congrArg (Machine.mk c (l.map (decorateFrame value) ++ .write (decorateRows value tail) :: r.map (decorateFrame value)))
    funext j
    by_cases hj : j=k <;> simp [hj]

/-- Every split-fetch schedule, including pauses between fetch and lookup, is
realizable with its actual deterministic per-slot payload. -/
theorem realize {jobs workers m log} (value : Nat → V) (run : WorkerFetch.Execution jobs workers m log) :
    Execution (jobs.map (decorateRows value)) workers (decorate value m) (log.map fun k => (k,value k)) := by
  induction run with
  | begin => simpa [decorate,decorateFrame,start,WorkerFetch.start] using Execution.begin
  | next _ step ih => exact ih.next (decorate_step _ step)

theorem joined_stopped {jobs : List (Rows V)} {m : Machine V} (retired : m.threads = []) :
    ¬ ∃ next, Step jobs (view jobs m) next := by
  have noThreads : (view jobs m).live=[] := by simp [view,retired]
  rintro ⟨next,step⟩
  have live {s t : State Nat V} (h : Step jobs s t) : s.live ≠ [] := by cases h <;> simp
  exact live step noThreads



private def Frame.valid (good : Nat → V → Prop) : Frame V → Prop
  | .write rows => ∀ kv ∈ rows, good kv.1 kv.2
  | _ => True

private theorem validFrames {jobs : List (Rows V)} {workers m log}
    (run : Execution jobs workers m log) (good : Nat → V → Prop)
    (plan : ∀ rows ∈ jobs, ∀ kv ∈ rows, good kv.1 kv.2) :
    ∀ f ∈ m.threads, f.valid good := by
  induction run with
  | begin => simp [start, Frame.valid, List.mem_replicate]
  | next _ step ih =>
    cases step with
    | fetch | finish =>
      intro f hf
      simp only [List.mem_append,List.mem_cons] at hf
      rcases hf with hl | rfl | hr
      · exact ih _ (by simp [hl])
      · trivial
      · exact ih _ (by simp [hr])
    | exhausted =>
      intro f hf
      rcases List.mem_append.mp hf with hl | hr
      · exact ih _ (by simp [hl])
      · exact ih _ (by simp [hr])
    | found l r c cells log i rows lookup =>
      intro f hf
      simp only [List.mem_append,List.mem_cons] at hf
      rcases hf with hl | rfl | hr
      · exact ih _ (by simp [hl])
      · exact plan rows (List.mem_of_getElem? lookup)
      · exact ih _ (by simp [hr])
    | set l r c cells log k v tail empty =>
      intro f hf
      simp only [List.mem_append,List.mem_cons] at hf
      rcases hf with hl | rfl | hr
      · exact ih _ (by simp [hl])
      · intro kv hkv
        exact ih (.write ((k,v)::tail)) (by simp) kv (.tail _ hkv)
      · exact ih _ (by simp [hr])

open Aeneas Aeneas.Std Result

/-- Replay with the existing Rust ticket computation. At *every prefix*, the
successful OnceLock stores agree, slot for slot, with the array produced by
writeRows. Failed computations and out-of-range stores cannot be hidden. -/
theorem Execution.replay {jobs : List (Rows V)} {workers m log}
    (run : Execution jobs workers m log) (n : Nat) (compute : Nat → Result V)
    (plan : ∀ rows ∈ jobs, ∀ kv ∈ rows, kv.1<n ∧ compute kv.1=ok kv.2) :
    ∃ rows, WidthEight.Ticket.writeRows n compute (log.map Prod.fst) = ok rows ∧
      rows.length=n ∧ ∀ j<n, rows[j]?=some (m.cells j) := by
  induction run with
  | begin => exact ⟨_,rfl,by simp,by simp [start,List.getElem?_replicate]⟩
  | next prior step ih =>
    obtain ⟨rows,ran,len,agree⟩ := ih
    cases step with
    | set l r c cells log k v tail empty =>
      have frame := validFrames prior (fun k v => k<n ∧ compute k=ok v) plan (.write ((k,v)::tail)) (by simp)
      obtain ⟨within,value⟩ := frame (k,v) (by simp)
      have reads := agree k within
      change rows[k]?=some (cells k) at reads
      rw [empty] at reads
      refine ⟨rows.set k (some v),?_,by simpa using len,?_⟩
      · simp [WidthEight.Ticket.writeRows,ran,reads,value]
      · intro j hj
        by_cases eq : j=k
        · subst j
          simp [show k<rows.length by omega]
        · simpa [eq,List.getElem?_set_ne (Ne.symm eq)] using agree j hj
    | _ => exact ⟨rows,ran,len,agree⟩

inductive Host where
  | apple (sha3 : Bool)
  | x86
  | linuxArm

noncomputable def nativeTicket (host : Host) {N : Usize} (p : params.Params)
    (layers : ParallelXmssTicket.Layers) (roots : alloc.vec.Vec (Array U8 N)) (j : Usize)
    (sk seed : Array U8 N) : Result (alloc.vec.Vec U8) :=
  match host with
  | .apple sha3 => TicketApple.slhdsa.WidthEight.Ticket.ticket (.apple sha3) p layers roots j sk seed
  | .x86 => TicketX86.slhdsa.WidthEight.Ticket.ticket .x86 p layers roots j sk seed
  | .linuxArm => ParallelSignTicket.ticket layers roots j sk seed

noncomputable def nativePhaseTwo (host : Host) {N : Usize} (p : params.Params)
    (sk seed : Array U8 N) (layers : ParallelXmssTicket.Layers)
    (roots : alloc.vec.Vec (Array U8 N)) (completed : List Nat) :=
  match host with
  | .apple sha3 => ParallelApple.slhdsa.WidthEight.Ticket.phaseTwo (.apple sha3) p sk seed layers roots completed
  | .x86 => ParallelX86.slhdsa.WidthEight.Ticket.phaseTwo .x86 p sk seed layers roots completed
  | .linuxArm => ThreeLane.slhdsa.WidthEight.Ticket.phaseTwo .linuxArm p sk seed layers roots completed

noncomputable def compute (host : Host) {N : Usize} (p : params.Params) (sk seed : Array U8 N)
    (layers : ParallelXmssTicket.Layers) (roots : alloc.vec.Vec (Array U8 N)) (j : Nat) :=
  if h : j < 2^UScalarTy.Usize.numBits then
    nativeTicket host p layers roots (Usize.ofNatCore j h) sk seed else fail .panic

/-- The native post-join WOTS projection returns exactly the corresponding physical heap,
even for a finite prefix, with the three callers' own native ticket programs. -/
theorem phase_two_heap
    (host : Host) {N : Usize} (p : params.Params) (sk seed : Array U8 N)
    (layers : ParallelXmssTicket.Layers) (roots : alloc.vec.Vec (Array U8 N))
    {jobs : List (Rows (alloc.vec.Vec U8))} {workers m log} (run : Execution jobs workers m log)
    (plan : ∀ rows ∈ jobs, ∀ kv ∈ rows, kv.1<p.d.val ∧
      compute host p sk seed layers roots kv.1=ok kv.2) :
    ∃ out, nativePhaseTwo host p sk seed layers roots (log.map Prod.fst)=ok out ∧
      out.length=p.d.val ∧ ∀ j<p.d.val, out.val[j]?=some (m.cells j) := by
  obtain ⟨rows,ran,len,agree⟩ := run.replay p.d.val (compute host p sk seed layers roots) plan
  have size : rows.length ≤ Usize.max := by rw [len]; scalar_tac
  refine ⟨alloc.vec.Vec.from rows size,?_,?_,?_⟩
  · have joined : (do
        let vs ← WidthEight.Ticket.writeRows p.d.val (compute host p sk seed layers roots) (log.map Prod.fst)
        if h : vs.length≤Usize.max then ok (alloc.vec.Vec.from vs h) else fail .panic) =
        ok (alloc.vec.Vec.from rows size) := by rw [ran]; simp only [bind_ok,dite_eq_left size]
    cases host <;> exact joined
  · simpa [alloc.vec.Vec.length,alloc.vec.Vec.from_val] using len
  · simpa [alloc.vec.Vec.from_val] using agree

theorem compute_succeeds (host : Host) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (layers : ParallelXmssTicket.Layers) (roots : alloc.vec.Vec (Array U8 N))
    (j : Nat) (_inside : j<p.d.val) (hasLayer : j<layers.length) (hasRoot : j<roots.length) :
    ∃ row, compute host p sk seed layers roots j = ok row ∧
      bytes row.val = Spec.wotsSign (Shake.params p) (bytes roots.val[j]!.val) (bytes sk.val) (bytes seed.val)
        { (adrsS layers.val[j]!.1).setTypeAndClear Spec.WOTS_HASH with keypair := layers.val[j]!.2.val } := by
  have small : j < 2^UScalarTy.Usize.numBits := by scalar_tac
  let i := Usize.ofNatCore j small
  unfold compute
  rw [dite_eq_left small]
  cases host with
  | apple sha3 =>
    exact spec_imp_exists (TicketApple.slhdsa.WidthEight.Ticket.ticket_spec (.apple sha3) p hp layers roots i sk seed hasLayer hasRoot)
  | x86 =>
    exact spec_imp_exists (TicketX86.slhdsa.WidthEight.Ticket.ticket_spec .x86 p hp layers roots i sk seed hasLayer hasRoot)
  | linuxArm =>
    exact spec_imp_exists (ParallelSignTicket.ticket_spec p hp layers roots i sk seed hasLayer hasRoot)

/-- For every concrete split-fetch history and every valid layer, the native call
supplies the value placed in the cell. This constructs the valued run and
discharges its plan premise from the actual host ticket computation. -/
theorem native_run (host : Host) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (layers : ParallelXmssTicket.Layers) (roots : alloc.vec.Vec (Array U8 N))
    (layerCount : p.d.val≤layers.length) (rootCount : p.d.val≤roots.length)
    {workers m log} (run : WorkerFetch.Execution (MaximalWorker.single p.d.val).jobs workers m log) :
    ∃ value : Nat → alloc.vec.Vec U8,
      (∀ j<p.d.val, compute host p sk seed layers roots j=ok (value j) ∧
        bytes (value j).val = Spec.wotsSign (Shake.params p) (bytes roots.val[j]!.val)
          (bytes sk.val) (bytes seed.val)
          { (adrsS layers.val[j]!.1).setTypeAndClear Spec.WOTS_HASH with keypair := layers.val[j]!.2.val }) ∧
      Execution ((MaximalWorker.single p.d.val).jobs.map (decorateRows value)) workers
        (decorate value m) (log.map fun j => (j,value j)) ∧
      ∃ out, nativePhaseTwo host p sk seed layers roots log=ok out ∧ out.length=p.d.val ∧
        ∀ j<p.d.val, out.val[j]?=some ((decorate value m).cells j) := by
  classical
  let choice j (h : j<p.d.val) := compute_succeeds host p hp sk seed layers roots j h
    (lt_of_lt_of_le h layerCount) (lt_of_lt_of_le h rootCount)
  let value (j : Nat) : alloc.vec.Vec U8 := if h : j<p.d.val then Classical.choose (choice j h) else default
  have law j (h : j<p.d.val) := Classical.choose_spec (choice j h)
  have run' := realize value run
  refine ⟨value,fun j h => by simpa [value,h] using law j h,run',?_⟩
  have plan : ∀ rows ∈ (MaximalWorker.single p.d.val).jobs.map (decorateRows value), ∀ kv ∈ rows,
      kv.1<p.d.val ∧ compute host p sk seed layers roots kv.1=ok kv.2 := by
    simp only [MaximalWorker.single,List.map_map,Function.comp_def,decorateRows,List.map_cons,
      List.map_nil,List.mem_map,List.mem_range,forall_exists_index,and_imp]
    intro rows j hj eq kv hv
    subst rows
    simp only [List.mem_singleton] at hv
    subst kv
    exact ⟨hj,by simpa [value,hj] using (law j hj).1⟩
  simpa [Function.comp_def] using phase_two_heap host p sk seed layers roots run' plan

open Spec _root_.ParallelSigning ParallelCached ParallelFused.Slots

/-- Assembly reads the same payload heap produced by this particular interleaved run.
Phase-one inputs specify the forest, authentication paths and signing leaves. -/
theorem joined_signature (p : Params) (valid : p.Valid) (md sk pk : Bytes) (a : Adrs)
    (r : Bytes) (tree leaf : Nat) (bounded : leaf < 2^p.hp)
    (forest : List Bytes) (auth leaves : Nat → Bytes)
    (rows : forest = forsRows p md sk pk a)
    (sibs : ∀ j<p.d, ∀ h<p.hp,
      let pos := loc p.hp tree leaf j
      auth (j*p.hp+h)=xmssNode p sk ((pos.2/2^h)^^^1) h pk (addr j pos.1))
    (lvs : ∀ j, j+1<p.d →
      let pos := loc p.hp tree leaf j
      leaves j=xmssNode p sk pos.2 0 pk (addr j pos.1)) :
    let first := forsPkFromSig p forest.flatten md pk a
    let want := wots p sk pk tree leaf (signerInput p pk first tree leaf leaves auth)
    ∀ {workers m log}, 0<workers →
      Execution (valued ((List.range p.d).map fun j => [j]) want) workers m log →
      m.threads=[] →
      assemble p r forest auth m.cells =
        r ++ forsSign p md sk pk a ++
          htSign p (forsPkFromSig p (forsSign p md sk pk a) md pk a) sk pk tree leaf := by
  intro first want workers m log positive run retired
  apply output_fips _ valid _ _ _ _ _ _ _ _ bounded
  exact ⟨forest,auth,leaves,rows,sibs,lvs,workers,_,positive,run.reach,joined_stopped retired,rfl⟩

end slhdsa.WorkerPayload
