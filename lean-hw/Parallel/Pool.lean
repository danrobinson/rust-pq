import Std

namespace ParallelPool

/-- Model one exclusively owned dispatch. A worker moves from pending to
live after acquiring its publication, and leaves live when it decrements
the completion counter. A live worker may have stopped reading the job
but has not yet announced that it has finished. -/
inductive Run : List Nat → List Nat → Nat → Bool → List Nat → Prop
  | dispatch (n : Nat) : Run (List.range n) [] n false []
  | start {p q live n flag failures i} : Run (p ++ i :: q) live n flag failures →
      Run (p ++ q) (i :: live) n flag failures
  | finish {p q pending n flag failures i} : Run pending (p ++ i :: q) (n+1) flag failures →
      Run pending (p ++ q) n flag failures
  | panic {p q pending n flag failures i} : Run pending (p ++ i :: q) (n+1) flag failures →
      Run pending (p ++ q) n true (i :: failures)

theorem ledger {pending live n flag failures} (run : Run pending live n flag failures) :
    pending.length + live.length = n ∧ (flag = false ↔ failures = []) := by
  induction run with
  | dispatch => simp
  | start _ ih => simp_all [List.length_append]; omega
  | finish _ ih => simp_all [List.length_append]; omega
  | panic _ ih => simp_all [List.length_append]; omega

/-- The caller may clear its borrowed job after acquiring zero. At that
point every worker has finished, including any worker whose closure
unwound. A normally returning dispatch with the failure bit clear certifies
that none of the joined workers panicked. -/
theorem join {pending live flag failures} (run : Run pending live 0 flag failures) :
    pending = [] ∧ live = [] ∧ (flag = false ↔ failures = []) := by
  have h := ledger run
  exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega), h.2⟩

/-- Encoding used by Pool.remaining. The low bit is sticky during dispatch. -/
def encode (n : Nat) (failed : Bool) := 2*n + failed.toNat

theorem packed_join (n : Nat) (failed : Bool) :
    (encode n failed < 2 ↔ n = 0) ∧ (encode 0 failed = 1 ↔ failed = true) ∧
    encode (n+1) failed - 2 = encode n failed ∧
    (encode (n+1) failed < 4 ↔ n = 0) := by
  cases failed <;> simp [encode, Bool.toNat] <;> omega

/-- A trace between job publication and retirement. A call has three stages:
waiting for publication, borrowing the closure, and released but still
counted. Different workers can interleave the relaxed OR, slot release and
SeqCst decrement. The flag records whether a worker has reported a panic. -/
inductive CounterTrace : List Nat → List Nat → List Nat → Nat → Bool → Prop
  | init (n) : CounterTrace (List.range n) [] [] (2*n) false
  | acquire {p q live idle word failed i} :
      CounterTrace (p ++ i :: q) live idle word failed →
      CounterTrace (p ++ q) (i :: live) idle word failed
  | report {pending p q idle word failed i} :
      CounterTrace pending (p ++ i :: q) idle word failed →
      CounterTrace pending (p ++ i :: q) idle (word ||| 1) true
  | release {pending p q idle word failed i} :
      CounterTrace pending (p ++ i :: q) idle word failed →
      CounterTrace pending (p ++ q) (i :: idle) word failed
  | decrement {pending live p q word failed i} :
      CounterTrace pending live (p ++ i :: q) word failed →
      CounterTrace pending live (p ++ q) (word - 2) failed

private theorem mark_failed (n : Nat) (failed : Bool) :
    encode n failed ||| 1 = encode n true := by
  have odd : (encode n failed ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (.inr rfl)
  have half : (encode n failed ||| 1) / 2 = n := by
    rw [Nat.or_div_two]
    cases failed <;> simp [encode, Bool.toNat] <;> omega
  change (encode n failed ||| 1) = 2*n + 1
  omega

theorem counter_word {pending live idle word failed}
    (h : CounterTrace pending live idle word failed) :
    word = encode (pending.length + live.length + idle.length) failed := by
  induction h with
  | init => simp [encode, Bool.toNat]
  | acquire _ ih => simpa [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using ih
  | report _ ih => rw [ih, mark_failed]
  | release _ ih => simpa [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using ih
  | decrement _ ih =>
    rw [ih]
    simp only [List.length_append, List.length_cons, encode]
    omega

/-- The Acquire load that licenses clearing UnsafeCell has accounted for
every release, even when another worker set the failure bit between decrements. -/
theorem safe_to_clear {pending live idle word failed} (h : CounterTrace pending live idle word failed)
    (joined : word < 2) :
    pending = [] ∧ live = [] ∧ idle = [] ∧ (word = 1 ↔ failed = true) := by
  have wh := counter_word h
  have hz := ((packed_join _ failed).1).mp (wh ▸ joined)
  exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega),
    List.length_eq_zero_iff.mp (by omega), by rw [wh, hz]; exact (packed_join 0 failed).2.1⟩

/-- In the total order of the four SeqCst operations in one join attempt,
the dispatcher sees the final decrement, or the last worker observes the
wait flag (unless the dispatcher has since withdrawn it). This is the
store-buffering cycle excluded by the chosen memory order. -/
theorem join_wakeup_order {announce check decrement poll : Nat}
    (caller : announce < check) (worker : decrement < poll) :
    decrement < check ∨ announce < poll := by omega

/-- Both condition variables use the same mutex discipline. If notification
has already released the mutex when the waiter takes it, the predicate write
happens before the recheck. Otherwise the atomic unlock-and-wait precedes
notification. Coordinates describe lock ownership in the serialized mutex
trace, with program order extending either side of the critical sections. -/
theorem condvar_wakeup_order {publish notifyLock notify notifyUnlock waitLock check releaseWait : Nat}
    (sender : publish < notifyLock ∧ notifyLock < notify ∧ notify < notifyUnlock)
    (waiter : waitLock < check ∧ check < releaseWait)
    (exclusive : notifyUnlock < waitLock ∨ releaseWait < notifyLock) :
    (publish < notifyUnlock ∧ notifyUnlock < check) ∨ releaseWait < notify := by omega

namespace Publication

/-- Single worker up to its first job read. A parked worker can own the
mutex for the predicate check, or be atomically queued on the condvar.
The notifier holds that same mutex during notify_all. Spurious wakes
return the worker to the mutex acquisition path. -/
inductive Worker where
  | spinning | waitingForLock | checking | sleeping | reading
  deriving DecidableEq
inductive Sender where
  | beforeSwap | needsLock | notifying | done
  deriving DecidableEq
open Worker Sender

inductive Step : Worker × Sender → Worker × Sender → Prop
  | park : Step (spinning, beforeSwap) (waitingForLock, beforeSwap)
  | publishSpin : Step (spinning, beforeSwap) (spinning, done)
  | publishPark {w} : w ≠ spinning → w ≠ reading →
      Step (w, beforeSwap) (w, needsLock)
  | observe : Step (spinning, done) (reading, done)
  | workerLock {s} : s ≠ notifying → Step (waitingForLock, s) (checking, s)
  | wait : Step (checking, beforeSwap) (sleeping, beforeSwap)
  /-- Before the notifier hands off the mutex, an acquire load can still
  read the old parked state even though the swap has taken place. -/
  | waitAfterSwap : Step (checking, needsLock) (sleeping, needsLock)
  | recheck {s} : s ≠ beforeSwap → Step (checking, s) (reading, s)
  | spurious {s} : Step (sleeping, s) (waitingForLock, s)
  | senderLock {w} : w ≠ checking → Step (w, needsLock) (w, notifying)
  | wake : Step (sleeping, notifying) (waitingForLock, done)
  | finish {w} : w ≠ sleeping → Step (w, notifying) (w, done)

inductive Reach : Worker × Sender → Prop
  | init : Reach (spinning, beforeSwap)
  | step {a b} : Reach a → Step a b → Reach b

/-- Once publication and any required notification are complete, a sleeping
worker cannot have missed that notification. A worker in its read section
must have passed an acquire observation after publication. -/
theorem published {w s} (h : Reach (w, s)) :
    (s = done → w ≠ sleeping) ∧ (w = reading → s ≠ beforeSwap) := by
  generalize he : (w, s) = ws at h
  revert w s
  induction h with
  | init => rintro _ _ eq; cases eq; decide
  | step _ step ih =>
    rintro _ _ eq
    cases step <;> cases eq <;> simp_all

end Publication

end ParallelPool
