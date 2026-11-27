import Parallel.WorkerRuntime

open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave
set_option backward.isDefEq.respectTransparency false
namespace ParallelPhaseOne

structure Plan (N : Usize) (J : Type) where
  jobs : alloc.vec.Vec J
  total : Usize
  dispatch : J → Program (Shared N) Unit
  reduce : Program (Shared N) Unit

def Plan.finished (p : Plan N J) (old : Usize) : Program (Shared N) (ControlFlow Unit Unit) := do
  let n ← liftM (old + 1#usize)
  if n = p.total then
    p.reduce
    publish
    pure (cont ())
  else pure (cont ())

def Plan.body (p : Plan N J) : Program (Shared N) (ControlFlow Unit Unit) := do
  let old ← rmw .phase1Next 1#usize
  match p.jobs.val[old.val]? with
  | none => pure (done ())
  | some job =>
    p.dispatch job
    let n ← rmw .phase1Done 1#usize
    p.finished n

def Plan.worker (p : Plan N J) : Program (Shared N) Unit := runLoop (fun _ : Unit => p.body) ()
def Plan.resume (p : Plan N J) : ControlFlow Unit Unit → Program (Shared N) Unit
  | cont u => runLoop (fun _ : Unit => p.body) u
  | done u => pure u

def Plan.counter (p : Plan N J) := rmw .phase1Done 1#usize >>= fun n => p.finished n >>= p.resume
def Plan.reducing (p : Plan N J) : Program (Shared N) Unit := do p.reduce; publish; p.worker

theorem fetch_job (p : Plan N J) (h : Shared N) (peers : List (Program (Shared N) Unit))
    (j : J) (found : p.jobs.val[(oldTicket h .phase1Next).val]? = some j) :
    Step h (p.worker :: peers) (increment h .phase1Next 1#usize)
      ((p.dispatch j >>= fun () => p.counter) :: peers) := by
  have entry : p.worker = (p.body >>= p.resume) := by
    unfold Plan.worker
    rw [runLoop_unfold]
    congr 1
    funext x
    cases x <;> rfl
  rw [entry]
  unfold Plan.body
  simp only [bind_assoc]
  have step := rmw_step .phase1Next 1#usize h (fun old => (match p.jobs.val[old.val]? with
    | none => pure (done ())
    | some job => do p.dispatch job; let n ← rmw .phase1Done 1#usize; p.finished n) >>= p.resume)
    [] peers
  simpa only [List.nil_append,found,bind_assoc,Plan.counter] using step

theorem finished_job (p : Plan N J) (h : Shared N) (peers : List (Program (Shared N) Unit))
    (n : Usize) (advanced : oldTicket h .phase1Done + 1#usize = ok n) :
    Step h (p.counter :: peers) (increment h .phase1Done 1#usize)
      ((if n = p.total then p.reducing else p.worker) :: peers) := by
  unfold Plan.counter
  have step := rmw_step .phase1Done 1#usize h (fun i => p.finished i >>= p.resume) [] peers
  by_cases same : n = p.total <;>
    simpa only [List.nil_append,Plan.finished,advanced,lifted_ok,pure_bind,same,ite_true,ite_false,
      bind_assoc,Plan.resume,Plan.reducing,Plan.worker] using step

/-- Every ticket visits the same physical heap as the next. The trace for a
job starts with its actual code and stops just before its completion RMW.
Peer steps during the job are permitted by the scheduler. -/
inductive Schedule (p : Plan N J) : Shared N → List (Program (Shared N) Unit) →
    Shared N → List (Program (Shared N) Unit) → Prop where
  | last {h middle out peers peers'} {job : J}
      (lookup : p.jobs.val[(oldTicket h .phase1Next).val]? = some job)
      (dispatch : Steps (increment h .phase1Next 1#usize)
        ((p.dispatch job >>= fun () => p.counter) :: peers) middle (p.counter :: peers'))
      (test : oldTicket middle .phase1Done + 1#usize = ok p.total)
      (finish : out = increment middle .phase1Done 1#usize) : Schedule p h peers out peers'
  | more {h middle out peers peers' finalPeers} {job : J} {n : Usize}
      (lookup : p.jobs.val[(oldTicket h .phase1Next).val]? = some job)
      (dispatch : Steps (increment h .phase1Next 1#usize)
        ((p.dispatch job >>= fun () => p.counter) :: peers) middle (p.counter :: peers'))
      (test : oldTicket middle .phase1Done + 1#usize = ok n) (again : n ≠ p.total)
      (rest : Schedule p (increment middle .phase1Done 1#usize) peers' out finalPeers) :
      Schedule p h peers out finalPeers

private theorem thenSteps {H A : Type} {s m t : H} {xs ys zs : List (Program H A)}
    (first : Steps s xs m ys) (second : Steps m ys t zs) : Steps s xs t zs :=
  Relation.ReflTransGen.trans first second

theorem Schedule.executes {p : Plan N J} {h out peers finalPeers}
    (schedule : Schedule p h peers out finalPeers) :
    Steps h (p.worker :: peers) out (p.reducing :: finalPeers) := by
  induction schedule with
  | last lookup dispatch test finish =>
    subst_vars
    exact thenSteps
      (thenSteps (fetch_job _ _ _ _ lookup).single dispatch)
      (by simpa using (finished_job p _ _ _ test).single)
  | more lookup dispatch test cont rest ih =>
    exact thenSteps
      (thenSteps
        (thenSteps (fetch_job _ _ _ _ lookup).single dispatch)
        (by simpa [cont] using (finished_job p _ _ _ test).single)) ih

private theorem ticket (h : Shared N) (c : Counter) (fits : h.counts c < 2^System.Platform.numBits) :
    (oldTicket h c).val = h.counts c :=
  (BitVec.toNat_ofNat ..).trans (Nat.mod_eq_of_lt fits)

private theorem inc_count (h : Shared N) (c : Counter) (fits : h.counts c+1 < 2^System.Platform.numBits) :
    (increment h c 1#usize).counts c = h.counts c + 1 := by
  simp only [increment, UScalar.wrapping_add_val_eq,ticket h c (by omega)]
  change (h.counts c+1) % (UScalar.size .Usize) = _
  exact Nat.mod_eq_of_lt (by simpa [UScalar.size_def] using fits)

private theorem spec_imp_exists_local {T : Type} {m : Result T} {p : T → Prop} (h : WP.spec m p) :
    ∃ v, m = ok v ∧ p v := by cases m <;> simp_all

/-- A complete fixed plan of direct FORS jobs reaches the first reducer
instruction with the bytes from every dispatch in their addressed cells. -/
theorem direct_plan {N : Usize} (p : Plan N J) (values : Nat → Array U8 N)
    (length : p.jobs.length = p.total.val)
    (job : ∀ i (live : i < p.total.val) (s : Shared N),
      s.cells (.forsDirect i) = none →
      Step s [p.dispatch (p.jobs.val[i]'(by change i < p.jobs.length; omega))]
        ((slot N (.forsDirect i)).write (values i) s) [pure ()])
    (i : Nat) (h : Shared N) (peers : List (Program (Shared N) Unit))
    (live : i < p.total.val) (next : h.counts .phase1Next = i) (doneCount : h.counts .phase1Done = i)
    (cells : ∀ j, h.cells (.forsDirect j) = if j < i then some (values j) else none) :
    ∃ dest, Schedule p h peers dest peers ∧ dest.counts .phase1Done = p.total.val ∧
      ∀ j, dest.cells (.forsDirect j) = if j < p.total.val then some (values j) else none := by
  have limit : p.total.val < 2^System.Platform.numBits := p.total.bv.isLt
  have tk := ticket h .phase1Next (by omega)
  rw [next] at tk
  let begun := increment h .phase1Next 1#usize
  let filled := (slot N (.forsDirect i)).write (values i) begun
  let finished := increment filled .phase1Done 1#usize
  have fetched : p.jobs.val[(oldTicket h .phase1Next).val]? =
      some (p.jobs.val[i]'(by change i < p.jobs.length; omega)) := by rw [tk,List.getElem?_eq_getElem]
  have empty : begun.cells (.forsDirect i) = none := by
    change h.cells (.forsDirect i) = none
    rw [cells,ite_eq_right (Nat.lt_irrefl _)]
  have dispatched : Steps begun ((p.dispatch (p.jobs.val[i]'(by change i < p.jobs.length; omega)) >>= fun () => p.counter) :: peers)
      filled (p.counter :: peers) := by
    have progress := (job i live begun empty).continuation (fun () => p.counter) [] peers
    simpa only [List.nil_append,pure_bind] using progress.single
  have same : filled.counts .phase1Done = i := by simpa [filled,begun,slot,write,increment] using doneCount
  have next' : finished.counts .phase1Next = i+1 := by
    change begun.counts .phase1Next = i+1
    rw [show begun.counts .phase1Next = h.counts .phase1Next+1 from inc_count _ _ (by omega),next]
  have done' : finished.counts .phase1Done = i+1 := (inc_count _ _ (by omega)).trans (by rw [same])
  have stored (j : Nat) : finished.cells (.forsDirect j) = if j < i+1 then some (values j) else none := by
    change (ParallelWorkerHeap.write begun.toHeap (.forsDirect i) (values i)).cells (.forsDirect j) = _
    by_cases eq : i = j
    · subst j
      rw [ite_eq_left (Nat.lt_succ_self _)]; exact read_after_write _ _ _
    · erw [frame begun.toHeap (.forsDirect j) (.forsDirect i) (by simp [eq]) (values i)]
      change h.cells (.forsDirect j) = _
      rw [cells]
      by_cases g : j < i
      · rw [ite_eq_left g,ite_eq_left (Nat.lt_succ_of_lt g)]
      · rw [ite_eq_right g,ite_eq_right (by omega)]
  have prev : (oldTicket filled .phase1Done).val = i := (ticket _ _ (by omega)).trans same
  obtain ⟨n,add,nv⟩ := spec_imp_exists_local (UScalar.add_spec (x:=oldTicket filled .phase1Done) (y:=1#usize)
    (by rw [UScalar.max_USize_eq,prev]; change i+1 ≤ Usize.max; exact (Nat.succ_le_of_lt live).trans (by rw [Usize.max,Usize.numBits]; change _ ≤ 2^System.Platform.numBits-1; omega)))
  change n.val = (oldTicket filled .phase1Done).val + 1 at nv
  rw [prev] at nv
  by_cases last : i+1 = p.total.val
  · have nt : n = p.total := UScalar.eq_of_val_eq (nv.trans last)
    subst n
    exact ⟨finished,.last fetched dispatched add rfl,done'.trans last,by simpa only [last] using stored⟩
  · obtain ⟨dest,rest,completed,contents⟩ := direct_plan p values length job (i+1) finished peers
      (by omega) next' done' stored
    exact ⟨dest,.more fetched dispatched add (by rintro rfl; omega) rest,completed,contents⟩
termination_by p.total.val-i

end ParallelPhaseOne
