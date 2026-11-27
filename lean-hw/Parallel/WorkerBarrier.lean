import Parallel.LastFinisher

namespace slhdsa.WorkerBarrier

/-- The three reducer-owned OnceLocks of an uncached signing invocation. -/
structure Cells (F A R : Type) where
  fors : Option F
  auth : Option A
  roots : Option R
  deriving DecidableEq

inductive Writer where
  | reducing | setFors | setAuth | setRoots | locked | ready | notified | unlocked
  deriving DecidableEq

inductive Waiter where
  | spin (count : Nat)
  | lock | checking | sleeping | confirm | reading
  deriving DecidableEq

structure Heap (F A R : Type) where
  cells : Cells F A R
  writer : Writer
  workers : Nat → Waiter

def initial : Heap F A R :=
  ⟨⟨none, none, none⟩, .reducing, fun _ => .spin 0⟩

def Writer.released : Writer → Bool
  | .ready | .notified | .unlocked => true
  | _ => false

def Writer.holdsLock : Writer → Bool
  | .locked | .ready | .notified => true
  | _ => false

def Waiter.holdsLock : Waiter → Bool
  | .checking | .confirm => true
  | _ => false

def awaken : Waiter → Waiter
  | .sleeping => .lock
  | w => w

def Heap.move (h : Heap F A R) (i : Nat) (next : Waiter) : Heap F A R :=
  {h with workers := fun j => if j = i then next else h.workers j}

/-- Normal return. A stale spin poll may consume another spin or start parking.
The protected recheck is serialized with the sender's store and notification.
Condvar.wait atomically releases the mutex and enqueues its caller. -/
inductive Step (f : F) (a : A) (r : R) : Heap F A R → Heap F A R → Prop where
  | setFors (h) : h.writer = .reducing → h.cells.fors = none →
      Step f a r h {h with cells.fors := some f, writer := .setFors}
  | setAuth (h) : h.writer = .setFors → h.cells.auth = none →
      Step f a r h {h with cells.auth := some a, writer := .setAuth}
  | setRoots (h) : h.writer = .setAuth → h.cells.roots = none →
      Step f a r h {h with cells.roots := some r, writer := .setRoots}
  | senderLock (h) : h.writer = .setRoots → (∀ j, (h.workers j).holdsLock = false) →
      Step f a r h {h with writer := .locked}
  | release (h) : h.writer = .locked → Step f a r h {h with writer := .ready}
  | notifyAll (h) : h.writer = .ready →
      Step f a r h {h with workers := fun j => awaken (h.workers j), writer := .notified}
  | unlock (h) : h.writer = .notified → Step f a r h {h with writer := .unlocked}
  | poll (h i n) : h.workers i = .spin n → n < 256 → Step f a r h (h.move i (.spin (n+1)))
  | tryLock (h i) : h.workers i = .spin 256 → Step f a r h (h.move i .lock)
  | observe (h i n) : h.workers i = .spin n → h.writer.released = true →
      Step f a r h (h.move i .reading)
  | takeLock (h i) : h.workers i = .lock → h.writer.holdsLock = false →
      (∀ j, (h.workers j).holdsLock = false) → Step f a r h (h.move i .checking)
  | wait (h i) : h.workers i = .checking → h.writer.released = false →
      Step f a r h (h.move i .sleeping)
  | spurious (h i) : h.workers i = .sleeping → Step f a r h (h.move i .lock)
  | checkReady (h i) : h.workers i = .checking → h.writer.released = true →
      Step f a r h (h.move i .confirm)
  | confirm (h i) : h.workers i = .confirm → h.writer.released = true →
      Step f a r h (h.move i .reading)

/-- Expected contents after each individual successful OnceLock::set. -/
def installed (f : F) (a : A) (r : R) : Writer → Cells F A R
  | .reducing => ⟨none, none, none⟩
  | .setFors => ⟨some f, none, none⟩
  | .setAuth => ⟨some f, some a, none⟩
  | _ => ⟨some f, some a, some r⟩

def Writer.wokeAll : Writer → Bool
  | .notified | .unlocked => true
  | _ => false

structure Valid (f : F) (a : A) (r : R) (h : Heap F A R) : Prop where
  cells : h.cells = installed f a r h.writer
  ready : ∀ i, h.workers i = .reading → h.writer.released = true
  woke : h.writer.wokeAll = true → ∀ i, h.workers i ≠ .sleeping

private theorem installed_step {f : F} {a : A} {r : R} {h h' : Heap F A R}
    (s : Step f a r h h') (v : Valid f a r h) :
    h'.cells = installed f a r h'.writer := by
  have old := v.cells
  cases s <;> simp_all [installed,Heap.move]

private theorem preserves {f : F} {a : A} {r : R} {h h' : Heap F A R}
    (s : Step f a r h h') (v : Valid f a r h) : Valid f a r h' := by
  refine ⟨installed_step s v, ?_, ?_⟩
  · intro j read
    have old := v.ready j
    cases s <;> simp_all [Heap.move,Writer.released]
    all_goals split at read <;> simp_all
  · intro sent j
    have old : h.writer.wokeAll = true → h.workers j ≠ .sleeping := fun pub => v.woke pub j
    have pre : h.writer.released = false → h.writer.wokeAll = false := by
      cases h.writer <;> decide
    cases s <;> simp_all [Heap.move,Writer.wokeAll,awaken]
    all_goals split <;> try simp_all
    all_goals exact v.woke sent j

abbrev Run (f : F) (a : A) (r : R) := Relation.ReflTransGen (Step f a r) initial

theorem invariant {f : F} {a : A} {r : R} {h : Heap F A R} (run : Run f a r h) :
    Valid f a r h := by
  induction run with
  | refl => exact ⟨rfl, by simp [initial], by simp [initial,Writer.wokeAll]⟩
  | tail _ step ih => exact preserves step ih

theorem read_cells {f : F} {a : A} {r : R} {h : Heap F A R} (run : Run f a r h)
    {i} (read : h.workers i = .reading) : h.cells = ⟨some f,some a,some r⟩ := by
  have v := invariant run
  have seen := v.ready i read
  rw [v.cells]
  cases hw : h.writer <;> simp_all [Writer.released,installed]

theorem no_lost_notification {f : F} {a : A} {r : R} {h : Heap F A R}
    (run : Run f a r h) (done : h.writer = .unlocked) (j : Nat) :
    h.workers j ≠ .sleeping :=
  (invariant run).woke (by rw [done]; rfl) j

/-- The reducer can install arbitrary payloads before any waiting worker runs. -/
theorem can_publish (f : F) (a : A) (r : R) :
    ∃ h, Run f a r h ∧ h.writer = .ready := by
  have first := Step.setFors (f:=f) (a:=a) (r:=r) initial rfl rfl
  exact ⟨_, ((((Relation.ReflTransGen.single first).tail (.setAuth _ rfl rfl)).tail
    (.setRoots _ rfl rfl)).tail (.senderLock _ rfl (fun _ => rfl))).tail (.release _ rfl), rfl⟩

private theorem keeps_mutex {f : F} {a : A} {r : R} {h h' : Heap F A R}
    (action : Step f a r h h')
    (old : h.writer.holdsLock = true → ∀ j, (h.workers j).holdsLock = false) :
    h'.writer.holdsLock = true → ∀ j, (h'.workers j).holdsLock = false := by
  intro owns j
  cases action with
  | setFors | setAuth | setRoots | unlock => contradiction
  | senderLock _ free => exact free j
  | release st => exact old (by rw [st]; rfl) j
  | notifyAll st =>
    have before := old (by rw [st]; rfl) j
    change (awaken (h.workers j)).holdsLock = false
    cases w : h.workers j <;> simp [w,awaken,Waiter.holdsLock] at before ⊢
  | takeLock _ _ free _ =>
    change h.writer.holdsLock = true at owns
    simp [free] at owns
  | checkReady i checking _ =>
    have exclude := old owns i
    rw [checking] at exclude
    contradiction
  | poll | tryLock | observe | wait | spurious | confirm =>
    simp only [Heap.move]
    split <;> first | rfl | exact old owns j

theorem sender_owns_mutex {f : F} {a : A} {r : R} {h : Heap F A R}
    (run : Run f a r h) :
    h.writer.holdsLock = true → ∀ i, (h.workers i).holdsLock = false := by
  induction run with
  | refl => simp [initial,Writer.holdsLock]
  | tail _ step ih => exact keeps_mutex step ih

/-- If a worker is queued when notify_all executes, it is eligible to reacquire.
After the sender drops the guard it can take the lock and pass both acquire
checks whenever other waiters allow it to acquire the mutex. -/
theorem wake_to_reader (h : Heap F A R) (f : F) (a : A) (r : R) (i : Nat)
    (ready : h.writer = .ready) (queued : h.workers i = .sleeping)
    (run : Run f a r h) :
    ∃ after, Relation.ReflTransGen (Step f a r) h after ∧ after.workers i = .reading ∧
      after.cells = h.cells := by
  let signaled := {h with workers := fun j => awaken (h.workers j), writer := .notified}
  let unlocked := {signaled with writer := .unlocked}
  have wake : Step f a r h signaled := .notifyAll h ready
  have drop : Step f a r signaled unlocked := .unlock _ rfl
  have take : Step f a r unlocked (unlocked.move i .checking) := by
    apply Step.takeLock
    · simp [unlocked,signaled,queued,awaken]
    · rfl
    · intro j
      have before := sender_owns_mutex run (by rw [ready]; rfl) j
      change (awaken (h.workers j)).holdsLock = false
      cases atJ : h.workers j <;> simp [atJ,awaken,Waiter.holdsLock] at before ⊢
  have recheck := Step.checkReady (f:=f) (a:=a) (r:=r) (unlocked.move i .checking) i
    (by simp [Heap.move]) (by rfl)
  have confirm := Step.confirm (f:=f) (a:=a) (r:=r) ((unlocked.move i .checking).move i .confirm) i
    (by simp [Heap.move]) (by rfl)
  exact ⟨_, ((((Relation.ReflTransGen.single wake).tail drop).tail take).tail recheck).tail confirm,
    by simp [Heap.move], rfl⟩

/-- Every successful reader obtains precisely the three reducer outputs on the
reference completed phase-one table. The actual and reference completion
orders can differ, and the barrier can have any number of spurious wakes. -/
theorem read_at_last_finisher {S V F A R : Type} [DecidableEq S]
    {jobs : List (List (S × V))} {i active done cells}
    (history : ParallelFused.LastFinisher.History jobs i active done cells)
    (last : done.length = jobs.length) (ref : ParallelFused.Schedules.Completion jobs)
    (unique : (jobs.flatten.map Prod.fst).Nodup)
    (reduce : (S → Option V) → F × A × R) {h : Heap F A R}
    (run : Run (reduce cells).1 (reduce cells).2.1 (reduce cells).2.2 h)
    {j} (read : h.workers j = .reading) :
    let result := reduce ref.state.cells
    h.cells = ⟨some result.1, some result.2.1, some result.2.2⟩ := by
  have same := ParallelFused.LastFinisher.reference_cells history last ref unique
  simpa [same] using read_cells run read

end slhdsa.WorkerBarrier
