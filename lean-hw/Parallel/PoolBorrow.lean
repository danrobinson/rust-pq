import Parallel.Pool

/-! C++20 release-sequence and scoped borrow argument for the Rust worker pool.
The modification-order prefix starts at this dispatch's relaxed counter reset
and ends at the write read by the dispatcher's final acquire load. In particular
this is a per-location order, not a sequentially consistent machine execution. -/
namespace ParallelPool.Borrow

inductive Modification where
  | decrement (worker : Nat)
  | flagPanic (worker : Nat)
  deriving DecidableEq

/-- Newest first. Only RMWs can extend a release sequence on `remaining`
between the store that resets it and the load that observes completion. -/
inductive Trace (workers : Nat) : List Nat → Nat → List Modification → Prop
  | reset : Trace workers (List.range workers) (2*workers) []
  | flag {p q w count history} : Trace workers (p ++ w :: q) count history →
      Trace workers (p ++ w :: q) (count ||| 1) (.flagPanic w :: history)
  | retire {p q w count history} : Trace workers (p ++ w :: q) count history →
      Trace workers (p ++ q) (count - 2) (.decrement w :: history)

private theorem word {n left count history} (h : Trace n left count history) :
    count / 2 = left.length := by
  induction h with
  | reset => simp
  | flag _ ih => simpa [Nat.or_div_two] using ih
  | retire _ ih => simp_all; omega

private theorem issued {n left count history} (h : Trace n left count history) (w : Nat) (hw : w < n) :
    w ∈ left ∨ .decrement w ∈ history := by
  induction h with
  | reset => exact .inl (List.mem_range.mpr hw)
  | flag _ ih => exact ih.imp_right (List.mem_cons_of_mem _)
  | retire prior ih =>
    rcases ih with hl | hr
    · simp only [List.mem_append, List.mem_cons] at hl ⊢
      rcases hl with h | rfl | h
      · exact .inl (.inl h)
      · exact .inr (.inl rfl)
      · exact .inl (.inr h)
    · exact .inr (List.mem_cons_of_mem _ hr)

/-- A release decrement of `w` heads a release sequence whose tail is the
last modification observed. Relaxed panic RMWs extend this sequence too. -/
inductive ReleaseSequence (w : Nat) : List Modification → Prop
  | head (older) : ReleaseSequence w (.decrement w :: older)
  | rmw (next) {older} : ReleaseSequence w older → ReleaseSequence w (next :: older)

private theorem sequence_of_mem {w history} (hm : .decrement w ∈ history) :
    ReleaseSequence w history := by
  induction history with
  | nil => simp at hm
  | cons m ms ih =>
    rcases List.mem_cons.mp hm with rfl | h
    · exact .head _
    · exact .rmw _ (ih h)

/-- Every issued worker contributes a release head, including when the acquire
observes a later worker's decrement and the panic bit is set. -/
theorem joined {n left count history} (h : Trace n left count history) (low : count < 2)
    (w : Nat) (hw : w < n) : ReleaseSequence w history := by
  have hz : left.length = 0 := by have := word h; omega
  rcases issued h w hw with hl | hm
  · simp [List.length_eq_zero_iff.mp hz] at hl
  · exact sequence_of_mem hm

inductive Event where
  | claim (epoch : Nat)
  | initialize (epoch : Nat)
  | publish (epoch worker : Nat)
  | park (epoch worker : Nat)
  | idleBefore (epoch worker : Nat)
  | idleAfter (epoch worker : Nat)
  | reset (epoch : Nat)
  | acquire (epoch worker : Nat)
  | copyJob (epoch worker : Nat)
  | useClosure (epoch worker : Nat)
  | decrement (epoch worker : Nat)
  | join (epoch : Nat)
  | clear (epoch : Nat)
  | release (epoch : Nat)
  | endBorrow (epoch : Nat)
  deriving DecidableEq

/-- A reads-from choice in a per-location modification order. The bounds
represent write-read coherence from the preceding write and read-write
coherence to the following write. Older and newer writes may store identical
machine words. -/
structure ReadWindow {α : Type} (during : List α) where
  older : List α
  later : List α
  source : Nat
  seen : α
  rf : (older ++ during ++ later)[source]? = some seen

theorem ReadWindow.origin {α} {during : List α} (r : ReadWindow during)
    (lower : r.older.length ≤ r.source) (upper : r.source < r.older.length + during.length) :
    r.seen ∈ during := by
  have h := r.rf
  rw [List.getElem?_append_left (by simpa using upper), List.getElem?_append_right lower] at h
  exact List.mem_iff_getElem?.mpr ⟨_, h⟩

/-- The successful CAS is an RMW on busy. It reads the immediately preceding
modification. Failed CAS operations and loads make no modifications. -/
inductive BusyWrite where
  | init | claim (e : Nat) | release (e : Nat)
  deriving DecidableEq

inductive BusyMO : Nat → Bool → List BusyWrite → Prop
  | init : BusyMO 0 false [.init]
  | claim {e hist} : BusyMO e false hist → BusyMO e true (.claim e :: hist)
  | release {e hist} : BusyMO e true hist → BusyMO (e+1) false (.release e :: hist)

theorem busy_predecessor {e hist} (h : BusyMO (e+1) false hist) :
    hist.head? = some (.release e) := by cases h; rfl

inductive SlotWrite where
  | idle | parked | pending (e : Nat)
  deriving DecidableEq

def SlotWrite.word : SlotWrite → Nat
  | .idle => 0
  | .parked => 1
  | .pending _ => 2

/-- Between two consecutive worker-owned idle stores, a single assignment
writes pending. The optional parked CAS may occur first. Bounds for the
observation come from sequencing with these worker-owned writes. -/
def slotWindow (e : Nat) (park : Bool) : List SlotWrite :=
  [.idle] ++ (if park then [.parked] else []) ++ [.pending e]

theorem slot_publication (e : Nat) (park : Bool) (r : ReadWindow (slotWindow e park))
    (lower : r.older.length ≤ r.source) (upper : r.source < r.older.length + (slotWindow e park).length)
    (pending : r.seen.word = 2) : r.seen = .pending e := by
  have mem := r.origin lower upper
  cases park <;> cases hw : r.seen <;> simp_all [slotWindow, SlotWrite.word]

/-- After a successful CAS from idle to parked, the worker's own write
excludes the older idle value. The wait-loop's actual exit predicate is
"not parked"; that suffices to identify this dispatch's pending write. -/
theorem park_recheck (e : Nat) (r : ReadWindow (slotWindow e true))
    (afterCAS : r.older.length + 1 ≤ r.source)
    (upper : r.source < r.older.length + (slotWindow e true).length)
    (wake : r.seen.word ≠ 1) : r.seen = .pending e := by
  have h := r.rf
  rw [List.getElem?_append_left (by simpa using upper),
    List.getElem?_append_right (by omega : r.older.length ≤ r.source)] at h
  change r.source < r.older.length + 3 at upper
  have two : r.source - r.older.length = 1 ∨ r.source - r.older.length = 2 := by omega
  rcases two with one | two
  · simp [one, slotWindow] at h
    simp [← h, SlotWrite.word] at wake
  · simpa [two, slotWindow] using h.symm

private theorem parked_source (e : Nat) (park : Bool) (r : ReadWindow (slotWindow e park))
    (parked : park = true) (afterCAS : r.older.length + 1 ≤ r.source)
    (upper : r.source < r.older.length + (slotWindow e park).length)
    (wake : r.seen.word ≠ 1) : r.seen = .pending e := by
  subst park
  exact park_recheck e r afterCAS upper wake

/-- With no publisher between the worker's own park CAS and the recheck,
a spurious condition-variable wake still reads parked. -/
theorem spurious_recheck (r : ReadWindow [SlotWrite.parked])
    (lower : r.older.length ≤ r.source) (upper : r.source < r.older.length + 1) :
    r.seen = .parked := by
  have mem := r.origin lower upper
  simpa using mem

structure Sample where
  count : Nat
  mods : List Modification

private def counterValue (n : Nat) : List Modification → Nat
  | [] => 2*n
  | .decrement _ :: older => counterValue n older - 2
  | .flagPanic _ :: older => (counterValue n older) ||| 1

private theorem trace_value {n left count mods} (h : Trace n left count mods) :
    counterValue n mods = count := by induction h <;> simp_all [counterValue]

/-- All legal choices of reads-from inside a generation, in modification
order starting with the relaxed reset. The acquire need not see the most
recent write. -/
def counterWindow (n : Nat) : List Modification → List Sample
  | [] => [⟨2*n, []⟩]
  | m :: older => counterWindow n older ++ [⟨counterValue n (m::older), m::older⟩]

private theorem prefix_legal {n left count history} (h : Trace n left count history)
    (sample : Sample) (hm : sample ∈ counterWindow n history) :
    ∃ remaining, Trace n remaining sample.count sample.mods := by
  induction h with
  | reset => simp only [counterWindow, List.mem_singleton] at hm; subst sample; exact ⟨_, .reset⟩
  | flag old ih =>
    simp only [counterWindow, List.mem_append, List.mem_singleton] at hm
    rcases hm with earlier | rfl
    · exact ih earlier
    · simp only [counterValue, trace_value old]; exact ⟨_, .flag old⟩
  | retire old ih =>
    simp only [counterWindow, List.mem_append, List.mem_singleton] at hm
    rcases hm with earlier | rfl
    · exact ih earlier
    · simp only [counterValue, trace_value old]; exact ⟨_, .retire old⟩

/-- The caller's reset precedes its join load, and that join precedes the next
owner's reset via busy. Coherence excludes stale zero from an earlier dispatch
and values from future resets. The observed low count then supplies *every*
worker release head, including when panic RMWs intervene. -/
theorem counter_source {n left count mods} (h : Trace n left count mods)
    (r : ReadWindow (counterWindow n mods)) (lower : r.older.length ≤ r.source)
    (upper : r.source < r.older.length + (counterWindow n mods).length) (low : r.seen.count < 2)
    (w : Nat) (assigned : w < n) : ReleaseSequence w r.seen.mods := by
  obtain ⟨_, legal⟩ := prefix_legal h r.seen (r.origin lower upper)
  exact joined legal low w assigned

/-- In a terminal dispatch there may be no later owner. The end of this
location's finite history supplies the upper bound without a next reset. -/
theorem terminal_counter_source {n left count mods} (h : Trace n left count mods)
    (r : ReadWindow (counterWindow n mods)) (last : r.later = [])
    (lower : r.older.length ≤ r.source) (low : r.seen.count < 2)
    (w : Nat) (assigned : w < n) : ReleaseSequence w r.seen.mods := by
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp r.rf
  exact counter_source h r lower (by simpa [last] using inside) low w assigned

structure Epoch (e : Nat) where
  workers : Nat
  left : List Nat
  count : Nat
  modifications : List Modification
  legal : Trace workers left count modifications
  counter : ReadWindow (counterWindow workers modifications)
  low : counter.seen.count < 2
  parks : Nat → Bool
  slot : ∀ w, w < workers → ReadWindow (slotWindow e (parks w))
  ready : ∀ w (h : w < workers), if parks w then (slot w h).seen.word ≠ 1
    else (slot w h).seen.word = 2
  busy : List BusyWrite
  unlocked : BusyMO e false busy

/-- Program-order and synchronizes-with generators for successful dispatches.
The release/acquire edges require identified reads-from sources. The
coherence and modification-order proofs below establish those premises. -/
inductive Edge (epochs : (e : Nat) → Epoch e) : Event → Event → Prop
  | parkRecheck e w : (epochs e).parks w = true → Edge epochs (.park e w) (.acquire e w)
  | workerOrder e w : Edge epochs (.idleBefore e w) (.acquire e w)
  | useIdle e w : Edge epochs (.useClosure e w) (.idleAfter e w)
  | writeReset e : Edge epochs (.initialize e) (.reset e)
  | resetJoin e : Edge epochs (.reset e) (.join e)
  | claimWrite e : Edge epochs (.claim e) (.initialize e)
  | writePublish e w : Edge epochs (.initialize e) (.publish e w)
  | publishAcquire e w (h : w < (epochs e).workers) :
      ((epochs e).slot w h).seen = .pending e → Edge epochs (.publish e w) (.acquire e w)
  | acquireCopy e w : Edge epochs (.acquire e w) (.copyJob e w)
  | copyUse e w : Edge epochs (.copyJob e w) (.useClosure e w)
  | useDecrement e w : Edge epochs (.useClosure e w) (.decrement e w)
  | sequenceAcquire e w : ReleaseSequence w (epochs e).counter.seen.mods →
      Edge epochs (.decrement e w) (.join e)
  | joinClear e : Edge epochs (.join e) (.clear e)
  | clearRelease e : Edge epochs (.clear e) (.release e)
  | releaseScope e : Edge epochs (.release e) (.endBorrow e)
  | handoff e : (epochs (e+1)).busy.head? = some (.release e) →
      Edge epochs (.release e) (.claim (e+1))

inductive HB (epochs : (e : Nat) → Epoch e) : Event → Event → Prop
  | single {a b} : Edge epochs a b → HB epochs a b
  | trans {a b c} : HB epochs a b → HB epochs b c → HB epochs a c

inductive Location where
  | remaining | slot (w : Nat)

def writes : Event → Option Location
  | .reset _ => some .remaining
  | .park _ w | .idleBefore _ w | .idleAfter _ w => some (.slot w)
  | _ => none

def reads : Event → Option Location
  | .join _ => some .remaining
  | .acquire _ w => some (.slot w)
  | _ => none

/-- Coordinate writes by their position in each atomic's modification order,
and reads by the position of their chosen source. C++20 write-read and
read-write coherence apply only at a common location. The remaining fields
identify the boundaries and read coordinates in the supplied histories;
they do not constrain which write an acquire may observe. -/
structure Coherent (epochs : (e : Nat) → Epoch e) where
  stamp : Event → Nat
  write_read : ∀ {a b loc}, writes a = some loc → reads b = some loc →
    HB epochs a b → stamp a ≤ stamp b
  read_write : ∀ {a b loc}, reads a = some loc → writes b = some loc →
    HB epochs a b → stamp a < stamp b
  count_start : ∀ e, stamp (.reset e) = (epochs e).counter.older.length
  count_end : ∀ e, stamp (.reset (e+1)) =
    (epochs e).counter.older.length + (counterWindow (epochs e).workers (epochs e).modifications).length
  count_read : ∀ e, stamp (.join e) = (epochs e).counter.source
  slot_start : ∀ e w (h : w < (epochs e).workers),
    stamp (.idleBefore e w) = ((epochs e).slot w h).older.length
  slot_park : ∀ e w (h : w < (epochs e).workers), (epochs e).parks w = true →
    stamp (.park e w) = ((epochs e).slot w h).older.length + 1
  slot_end : ∀ e w (h : w < (epochs e).workers),
    stamp (.idleAfter e w) = ((epochs e).slot w h).older.length + (slotWindow e ((epochs e).parks w)).length
  slot_read : ∀ e w (h : w < (epochs e).workers),
    stamp (.acquire e w) = ((epochs e).slot w h).source

private theorem clear_next (epochs : (e : Nat) → Epoch e) (e : Nat) :
    HB epochs (.clear e) (.initialize (e+1)) :=
  (HB.single (.clearRelease e)).trans
    ((HB.single (.handoff e (busy_predecessor (epochs _).unlocked))).trans (.single (.claimWrite _)))

theorem coherent_slot_source (epochs : (e : Nat) → Epoch e) (co : Coherent epochs)
    (e w : Nat) (h : w < (epochs e).workers) : ((epochs e).slot w h).seen = .pending e := by
  have lo : ((epochs e).slot w h).older.length ≤ ((epochs e).slot w h).source := by
    rw [← co.slot_start e w h, ← co.slot_read e w h]
    exact co.write_read (loc := .slot w) rfl rfl (.single (.workerOrder e w))
  have hi : ((epochs e).slot w h).source < ((epochs e).slot w h).older.length +
      (slotWindow e ((epochs e).parks w)).length := by
    rw [← co.slot_read e w h, ← co.slot_end e w h]
    exact co.read_write (loc := .slot w) rfl rfl
      ((HB.single (.acquireCopy e w)).trans ((HB.single (.copyUse e w)).trans (.single (.useIdle e w))))
  have ready := (epochs e).ready w h
  by_cases park : (epochs e).parks w = true
  · have afterCAS : ((epochs e).slot w h).older.length + 1 ≤ ((epochs e).slot w h).source := by
      rw [← co.slot_park e w h park, ← co.slot_read e w h]
      exact co.write_read (loc := .slot w) rfl rfl (.single (.parkRecheck e w park))
    exact parked_source _ _ _ park afterCAS hi (by simpa [park] using ready)
  · exact slot_publication _ _ _ lo hi (by simpa [park] using ready)

theorem coherent_counter_source (epochs : (e : Nat) → Epoch e) (co : Coherent epochs)
    (e w : Nat) (h : w < (epochs e).workers) : ReleaseSequence w (epochs e).counter.seen.mods := by
  apply counter_source (epochs e).legal (epochs e).counter _ _ (epochs e).low w h
  · rw [← co.count_start e, ← co.count_read e]
    exact co.write_read (loc := .remaining) rfl rfl (.single (.resetJoin e))
  · rw [← co.count_read e, ← co.count_end e]
    exact co.read_write (loc := .remaining) rfl rfl
      ((HB.single (.joinClear e)).trans ((clear_next epochs e).trans (.single (.writeReset _))))

theorem borrow_lifetime (epochs : (e : Nat) → Epoch e) (co : Coherent epochs) (e w : Nat) (assigned : w < (epochs e).workers) :
    HB epochs (.initialize e) (.copyJob e w) ∧
    HB epochs (.useClosure e w) (.clear e) ∧
    HB epochs (.useClosure e w) (.endBorrow e) := by
  have pub := coherent_slot_source epochs co e w assigned
  have seq := coherent_counter_source epochs co e w assigned
  have done : HB epochs (.useClosure e w) (.clear e) :=
    (HB.single (.useDecrement e w)).trans ((HB.single (.sequenceAcquire e w seq)).trans (.single (.joinClear e)))
  exact ⟨(HB.single (.writePublish e w)).trans ((HB.single (.publishAcquire e w assigned pub)).trans (.single (.acquireCopy e w))),
    done, done.trans ((HB.single (.clearRelease e)).trans (.single (.releaseScope e)))⟩

private theorem write_clear (epochs : (e : Nat) → Epoch e) (e : Nat) :
    HB epochs (.initialize e) (.clear e) :=
  (HB.single (.writeReset e)).trans ((HB.single (.resetJoin e)).trans (.single (.joinClear e)))

/-- A borrow in any retired epoch finishes before the shared job cell is
overwritten by any later successful dispatcher, including another thread.
Epochs count only successful nonempty dispatches, excluding serial fallbacks. -/
theorem reuse (epochs : (e : Nat) → Epoch e) (co : Coherent epochs)
    (e w : Nat) (assigned : w < (epochs e).workers) (k : Nat) :
    HB epochs (.useClosure e w) (.initialize (e+k+1)) := by
  induction k with
  | zero => exact (borrow_lifetime epochs co e w assigned).2.1.trans (clear_next epochs e)
  | succ k ih =>
    exact ih.trans ((write_clear epochs _).trans (clear_next epochs _))

/-- The shared job cell has two exclusive accesses per owning dispatch and
one shared copy per dispatched worker. Closure invocations are shared through
the Rust bound `F: Fn() + Sync`. -/
inductive CellAccess where
  | initialize | copy (worker : Nat) | clear
  deriving DecidableEq

def CellAccess.event (e : Nat) : CellAccess → Event
  | .initialize => .initialize e
  | .copy w => .copyJob e w
  | .clear => .clear e

def CellAccess.allowed (n : Nat) : CellAccess → Prop
  | .copy w => w < n
  | _ => True

def CellAccess.exclusive : CellAccess → Bool
  | .copy _ => false
  | _ => true

private theorem clear_later (epochs : (e : Nat) → Epoch e) {i j : Nat} (lt : i < j) :
    HB epochs (.clear i) (.initialize j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt lt)
  induction k with
  | zero => exact clear_next epochs i
  | succ k ih => exact (ih (by omega)).trans ((write_clear epochs _).trans (clear_next epochs _))

private theorem distinct_owners (epochs : (e : Nat) → Epoch e) (co : Coherent epochs)
    {i j : Nat} (lt : i < j) (a b : CellAccess) (ha : a.allowed (epochs i).workers)
    (hb : b.allowed (epochs j).workers) : HB epochs (a.event i) (b.event j) := by
  have mid := clear_later epochs lt
  have before : HB epochs (a.event i) (.initialize j) := by
    cases a with
    | «initialize» => exact (write_clear epochs i).trans mid
    | clear => exact mid
    | copy w =>
      exact (HB.single (.copyUse i w)).trans ((borrow_lifetime epochs co i w ha).2.1.trans mid)
  cases b with
  | «initialize» => exact before
  | clear => exact before.trans (write_clear epochs j)
  | copy w => exact before.trans (borrow_lifetime epochs co j w hb).1

/-- All distinct accesses to the raw job cell with at least one writer are
ordered by happens-before. Shared worker reads in one dispatch may overlap. -/
theorem job_cell_race_free (epochs : (e : Nat) → Epoch e) (co : Coherent epochs)
    (i j : Nat) (a b : CellAccess) (ha : a.allowed (epochs i).workers)
    (hb : b.allowed (epochs j).workers) (distinct : (i, a) ≠ (j, b))
    (writer : a.exclusive = true ∨ b.exclusive = true) :
    HB epochs (a.event i) (b.event j) ∨ HB epochs (b.event j) (a.event i) := by
  rcases Nat.lt_trichotomy i j with lt | rfl | gt
  · exact .inl (distinct_owners epochs co lt a b ha hb)
  · cases a <;> cases b <;> simp_all [CellAccess.exclusive, CellAccess.allowed, CellAccess.event]
    all_goals first
      | exact .inl (write_clear epochs i)
      | exact .inr (write_clear epochs i)
      | exact .inl (borrow_lifetime epochs co i _ hb).1
      | exact .inr (borrow_lifetime epochs co i _ ha).1
      | exact .inl ((HB.single (.copyUse i _)).trans (borrow_lifetime epochs co i _ ha).2.1)
      | exact .inr ((HB.single (.copyUse i _)).trans (borrow_lifetime epochs co i _ hb).2.1)
  · exact .inr (distinct_owners epochs co gt b a hb ha)

/-! A witness exercises the hypotheses with an unbounded sequence of owners.
Each dispatch parks, borrows, reports a panic, retires, and hands off. -/
private def panicMods : List Modification := [.decrement 0, .flagPanic 0]

private theorem panicTrace : Trace 1 [] 1 panicMods := by
  exact Trace.retire (p := []) (q := []) (w := 0)
    (Trace.flag (p := []) (q := []) (w := 0) (.reset (workers := 1)))

private def busyHistory : (e : Nat) → { h : List BusyWrite // BusyMO e false h }
  | 0 => ⟨_, .init⟩
  | e+1 => ⟨_, .release (.claim (busyHistory e).2)⟩

private def before {α} (f : Nat → List α) : Nat → List α
  | 0 => []
  | n+1 => before f n ++ f n

private theorem before_length {α} (f : Nat → List α) (size : ∀ e, (f e).length = 3)
    (n : Nat) : (before f n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [before, ih, size, Nat.mul_succ]

private def third {α} (f : Nat → List α) (e : Nat) (x : α) (hx : (f e)[2]? = some x) :
    ReadWindow (f e) where
  older := before f e
  later := []
  source := (before f e).length + 2
  seen := x
  rf := by simp [List.getElem?_append_right, hx]

private def witness (e : Nat) : Epoch e where
  workers := 1
  left := []
  count := 1
  modifications := panicMods
  legal := panicTrace
  counter := third (fun _ => counterWindow 1 panicMods) e ⟨1, panicMods⟩ rfl
  low := by change 1 < 2; decide
  parks := fun _ => true
  slot := fun _ _ => third (fun k => slotWindow k true) e (.pending e) rfl
  ready := fun _ _ => by change (2 : Nat) ≠ 1; decide
  busy := (busyHistory e).1
  unlocked := (busyHistory e).2

private def clock : Event → Nat
  | .claim e | .idleBefore e _ => 12*e
  | .initialize e => 12*e+1
  | .reset e | .park e _ => 12*e+2
  | .publish e _ => 12*e+3
  | .acquire e _ => 12*e+4
  | .copyJob e _ => 12*e+5
  | .useClosure e _ => 12*e+6
  | .idleAfter e _ => 12*e+7
  | .decrement e _ => 12*e+8
  | .join e => 12*e+9
  | .clear e => 12*e+10
  | .release e => 12*e+11
  | .endBorrow e => 12*e+12

private theorem clock_mono {a b} (h : HB witness a b) : clock a < clock b := by
  induction h with
  | single edge => cases edge <;> simp [clock] <;> omega
  | trans _ _ ab bc => omega

private def stamp : Event → Nat
  | .reset e | .idleBefore e _ => 3*e
  | .park e _ => 3*e+1
  | .join e | .acquire e _ => 3*e+2
  | .idleAfter e _ => 3*e+3
  | _ => 0

private def witnessCoherent : Coherent witness where
  stamp := stamp
  write_read := by
    intro a b loc aw br hab
    have h := clock_mono hab
    cases loc <;> cases a <;> simp [writes] at aw <;> cases b <;> simp_all [reads, clock, stamp] <;> omega
  read_write := by
    intro a b loc ar bw hab
    have h := clock_mono hab
    cases loc <;> cases a <;> simp [reads] at ar <;> cases b <;> simp_all [writes, clock, stamp] <;> omega
  count_start e := (before_length _ (fun _ => rfl) e).symm
  count_end e := by
    change 3*(e+1) = (before (fun _ => counterWindow 1 panicMods) e).length + 3
    rw [before_length _ (fun _ => rfl), Nat.mul_succ]
  count_read e := by
    change 3*e+2 = (before (fun _ => counterWindow 1 panicMods) e).length + 2
    rw [before_length _ (fun _ => rfl)]
  slot_start e w h := (before_length _ (fun _ => rfl) e).symm
  slot_park e w h _ := by
    change 3*e+1 = (before (fun k => slotWindow k true) e).length + 1
    rw [before_length _ (fun _ => rfl)]
  slot_end e w h := by
    change 3*e+3 = (before (fun k => slotWindow k true) e).length + 3
    rw [before_length _ (fun _ => rfl)]
  slot_read e w h := by
    change 3*e+2 = (before (fun k => slotWindow k true) e).length + 2
    rw [before_length _ (fun _ => rfl)]

theorem nonempty_reuse : ∃ (epochs : (e : Nat) → Epoch e), Nonempty (Coherent epochs) ∧
    ∀ e, (epochs e).workers = 1 ∧ (epochs e).counter.seen.count = 1 ∧
      (epochs e).parks 0 = true := ⟨witness, ⟨witnessCoherent⟩, fun _ => ⟨rfl, rfl, rfl⟩⟩

end ParallelPool.Borrow
