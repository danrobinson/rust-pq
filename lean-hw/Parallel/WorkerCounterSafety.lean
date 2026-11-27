import Parallel.WorkerRuntime
import Aeneas.Data.Coinductive.ITreeWP.DWLP

namespace ParallelWorkerCounterSafety
open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerHeap ParallelWorkerRuntime ParallelWorkerInterleave

/-- Any value of this type denotes one typed allocation site. Even an
opaque polymorphic iterator cannot manufacture an arbitrary heap updater. -/
structure Physical (N : Usize) (T : Type) where
  key : Key
  payloadType : Payload N key = T

def physicalSlot (N : Usize) (k : Key) : Physical N (Payload N k) := ⟨k,rfl⟩

def physicalTable (N : Usize) (key : Nat → Key) (T : Type) (ty : ∀ i, Payload N (key i) = T)
    (len : Usize) : alloc.vec.Vec (Physical N T) :=
  alloc.vec.Vec.from ((List.range len.val).map fun i => ⟨key i, ty i⟩) (by simp; scalar_tac)

def Physical.ref (p : Physical N T) : ParallelWorkerCells.Ref (Shared N) T := p.payloadType ▸ slot N p.key

theorem physical_lookup (N : Usize) (len j : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice _)
      (physicalTable N Key.wotsSigs _ (fun _ => rfl) len).deref j =
    ok (if j.val < len.val then some (physicalSlot N (.wotsSigs j.val)) else none) := by
  simp only [core.slice.Slice.get,core.slice.index.Usize.get,Slice.getElem?_Usize_eq,alloc.vec.Vec.deref,
    Slice.from_val,physicalTable,alloc.vec.Vec.from_val,List.getElem?_map]
  split
  · simp [List.getElem?_range ‹_›,physicalSlot] <;> rfl
  · simp [List.getElem?_eq_none (by simp; omega : (List.range len.val).length ≤ j.val)] <;> rfl

def put (k : Key) (v : Payload N k) (h : Shared N) : Shared N :=
  match (slot N k).read h with | some _ => h | none => (slot N k).write v h

/-- Every raw scheduler action is a load, a single occupied-or-empty OnceLock
store, the release of READY, or the unit increment of one named counter. -/
inductive Allowed (N : Usize) : (Shared N → Shared N) → Prop where
  | observe : Allowed N id
  | store (k : Key) (v : Payload N k) : Allowed N (put k v)
  | publish : Allowed N (fun h => {h with ready:=true})
  | issue (c : Counter) : Allowed N (fun h => increment h c 1#usize)

def semantics (N : Usize) : EffectWP (effects (Shared N)) where
  State := Unit
  wp op post _ := match op with
    | .atomic f => Allowed N f ∧ ∀ h, post h ()
    | .fail _ => True

instance : (semantics N).Monotonic where
  wp_monotonic := by
    intro op q r implies _ pre
    cases op with
    | fail => exact trivial
    | atomic f => exact ⟨pre.1, fun h => implies h () (pre.2 h)⟩

instance : (semantics N).Conjunctive where
  wp_conj := by
    intro op _ requires nonempty all
    obtain ⟨q,inhabited⟩ := nonempty
    cases op with
    | fail => exact trivial
    | atomic f => exact ⟨(all q inhabited).1,fun h p wanted => (all p wanted).2 h⟩

def Safe (p : Program (Shared N) A) := DWLP (semantics N) p (fun _ _ => True) ()

private theorem safe_iter {A B} (body : A → Program (Shared N) (A ⊕ B))
    (steps : ∀ a, Safe (body a)) (x : A) : Safe (ITree.iter body x) := by
  suffices all : ∀ a, Safe (ITree.iter body a) from all x
  apply ITree.iter.fixpoint_induct body (fun f => ∀ a, Safe (f a))
  · exact Lean.Order.admissible_pi_apply _ (fun _ => DWLP.admissible (semantics N) (fun _ _ => True) ())
  · intro iter ih a
    apply DWLP.bind (steps a)
    intro v _ _
    cases v with
    | inl a => exact ih a
    | inr => exact DWLP.ret_iff.mpr trivial

private theorem safe_loop {A B} (body : A → Program (Shared N) (ControlFlow A B))
    (steps : ∀ a, Safe (body a)) (x : A) : Safe (runLoop body x) := by
  apply safe_iter
  intro a
  apply DWLP.bind (steps a)
  intro v _ _
  cases v <;> exact DWLP.ret_iff.mpr trivial

/-- The raw field is an ordinary interaction tree accepted by the existing
scheduler. The attached certificate covers all its finite interleavings. -/
structure Certified (N : Usize) (A : Type) where
  raw : Program (Shared N) A
  safe : Safe raw

instance : Monad (Certified N) where
  pure a := ⟨.ret a,DWLP.ret_iff.mpr trivial⟩
  bind x k := ⟨x.raw >>= fun a => (k a).raw, DWLP.bind x.safe (fun a _ _ => (k a).safe)⟩

instance : MonadLift Result (Certified N) where
  monadLift r := ⟨liftResult r,by
    unfold liftResult
    cases r.match with
    | ok => exact DWLP.ret_iff.mpr trivial
    | div => exact DWLP.div
    | vis e => cases e; exact DWLP.vis trivial⟩

theorem raw_bind (p : Certified N A) (k : A → Certified N B) :
    (p >>= k).raw = p.raw >>= fun a => (k a).raw := rfl

theorem raw_pure (x : A) : (pure x : Certified N A).raw = pure x := rfl

theorem raw_lift (r : Result A) :
    (liftM r : Certified N A).raw = (liftM r : Program (Shared N) A) := rfl

def atomic (f : Shared N → Shared N) (allowed : Allowed N f) (answer : Shared N → T) :
    Certified N T :=
  ⟨.vis (.atomic f) (fun s => .ret (answer s)),
    DWLP.vis ⟨allowed,fun _ => DWLP.ret_iff.mpr trivial⟩⟩

def get (target : Physical N T) : Certified N (Option T) :=
  atomic id .observe target.ref.read

def set (target : Physical N T) (v : T) : Certified N (core.result.Result Unit T) :=
  by
    obtain ⟨key,equal⟩ := target
    subst T
    refine ⟨ParallelWorkerInterleave.set (slot N key) v,DWLP.vis ⟨?_,fun _ => DWLP.ret_iff.mpr trivial⟩⟩
    convert (Allowed.store key v) using 1
    funext h
    unfold put
    cases (slot N key).read h <;> rfl

theorem set_slot (key : Key) (v : Payload N key) :
    (set (physicalSlot N key) v).raw = ParallelWorkerInterleave.set (slot N key) v := rfl

def unitFetch (c : Counter) : Certified N Usize :=
  ⟨rmw c 1#usize,DWLP.vis ⟨.issue c,fun _ => DWLP.ret_iff.mpr trivial⟩⟩

def publish : Certified N Unit :=
  ⟨ParallelWorkerRuntime.publish, DWLP.vis ⟨.publish,fun _ => DWLP.ret_iff.mpr trivial⟩⟩

def loop (body : A → Certified N (ControlFlow A B)) (a : A) : Certified N B :=
  ⟨runLoop (fun x => (body x).raw) a,safe_loop _ (fun x => (body x).safe) a⟩

def wait : Certified N Bool :=
  ⟨waitReady,by
    apply safe_iter
    intro _
    apply DWLP.bind (Q₁:=fun _ _ => True) (m:=poll)
    · exact DWLP.vis ⟨.observe,fun _ => DWLP.ret_iff.mpr trivial⟩
    · intro ready _ _
      cases ready <;> exact DWLP.ret_iff.mpr trivial⟩

/-- A local safety certificate gives each scheduler step a faithful ticket
label using its actual primitive update and the heap at linearization. -/
inductive Label (c : Counter) (h : Shared N) (f : Shared N → Shared N) : List Nat → Prop where
  | skip : (f h).counts c = h.counts c → Label c h f []
  | issued : f = (fun s => increment s c 1#usize) → Label c h f [(oldTicket h c).val]

private theorem label_allowed {N c h f} (ok : Allowed N f) : ∃ log, Label c h f log := by
  cases ok with
  | observe | publish => exact ⟨[],.skip rfl⟩
  | store key v => exact ⟨[],.skip (by unfold put; cases (slot N key).read h <;> rfl)⟩
  | issue which =>
    by_cases same : c=which
    · subst which; exact ⟨_,.issued rfl⟩
    · exact ⟨[],.skip (by simp [increment,same])⟩


abbrev All (threads : List (Program (Shared N) A)) := ∀ p ∈ threads, Safe p
abbrev Pair (N : Usize) (A : Type) := Shared N × List (Program (Shared N) A)

inductive Recorded (c : Counter) (first : Pair N A) : Pair N A → List Nat → Prop where
  | begin : Recorded c first first []
  | step {h l r f k prior extra}
      (before : Recorded c first (h,l ++ ITree.vis (E := effects (Shared N)) (.atomic f) k :: r) prior)
      (allowed : Allowed N f) (written : Label c h f extra) : Recorded c first (f h,l ++ k h :: r) (prior ++ extra)

private theorem note_step (c : Counter) {first : Pair N A} {h hs h' hs' prior}
    (before : Recorded c first (h,hs) prior) (certs : All hs)
    (physical : Step h hs h' hs') :
    ∃ log, Recorded c first (h',hs') log ∧ All hs' := by
  cases physical with
  | atomic l r f k =>
    have active := certs (ITree.vis (E := effects (Shared N)) (.atomic f) k) (by simp)
    have exposed := DWLP.vis_view active
    change Allowed N f ∧ ∀ h, Safe (k h) at exposed
    obtain ⟨log,label⟩ := label_allowed (c:=c) (h:=h) exposed.1
    refine ⟨_,.step before exposed.1 label,?_⟩
    intro p member
    simp only [List.mem_append,List.mem_cons] at member
    rcases member with lhs | rfl | rhs
    · exact certs p (by simp [lhs])
    · exact exposed.2 h
    · exact certs p (by simp [rhs])

private theorem annotate {x y : Pair N A} (c : Counter)
    (run : Relation.ReflTransGen (fun (a b : Pair N A) => Step a.1 a.2 b.1 b.2) x y)
    (initial : All x.2) : ∃ log, Recorded c x y log ∧ All y.2 := by
  induction run with
  | refl => exact ⟨[],.begin,initial⟩
  | tail before step ih =>
    obtain ⟨log,prior,valid⟩ := ih
    exact note_step c prior valid step

theorem current_ticket (h : Shared N) (c : Counter)
    (capacity : h.counts c < 2 ^ System.Platform.numBits) :
    (oldTicket h c).val = h.counts c := by
  change (BitVec.ofNat System.Platform.numBits (h.counts c)).toNat = h.counts c
  exact (BitVec.toNat_ofNat ..).trans (Nat.mod_eq_of_lt capacity)

private theorem advanced_issue (h : Shared N) (c : Counter)
    (capacity : h.counts c + 1 < 2^System.Platform.numBits) :
    (increment h c 1#usize).counts c = h.counts c + 1 := by
  simp only [increment, UScalar.wrapping_add_val_eq]
  rw [current_ticket h c (by omega)]
  change (h.counts c+1) % (UScalar.size .Usize) = _
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size_def] using capacity

theorem recorded_values {N A c} {first final : Pair N A} {log}
    (history : Recorded c first final log)
    (capacity : first.1.counts c + log.length < 2 ^ System.Platform.numBits) :
    final.1.counts c = first.1.counts c + log.length ∧
    log = List.range' (first.1.counts c) log.length := by
  induction history with
  | begin => exact ⟨rfl,rfl⟩
  | @step h l r f k prior extra _ _ label ih =>
    rw [List.length_append] at capacity
    obtain ⟨count,order⟩ := ih (by omega)
    change h.counts c = _ at count
    cases label with
    | skip same => simpa [same] using And.intro count order
    | issued same =>
      subst f
      have cap : h.counts c+1 < 2^System.Platform.numBits := by simpa [count,Nat.add_assoc] using capacity
      have next := advanced_issue h c cap
      refine ⟨by simp [next,count,Nat.add_assoc],?_⟩
      rw [List.length_append, ← List.range'_append]
      simp only [Nat.one_mul]
      rw [← order, ← count, current_ticket h c (by omega)]
      rfl

/-- Arbitrarily many raw scheduler steps, taken by arbitrary workers in any
order. The returned trace records actual RMW values. The number of tickets
issued in the whole execution determines the only capacity hypothesis. -/
theorem all_interleavings {N A} (c : Counter) {start final : Shared N} {workers out : List (Program (Shared N) A)}
    (safe : All workers) (run : Steps start workers final out) :
    ∃ log, Recorded c (start,workers) (final,out) log ∧ All out ∧
      (start.counts c + log.length < 2^System.Platform.numBits →
        final.counts c = start.counts c+log.length ∧ log = List.range' (start.counts c) log.length ∧ log.Nodup) := by
  obtain ⟨log,history,outSafe⟩ := annotate c run safe
  refine ⟨log,history,outSafe,?_⟩
  intro capacity
  obtain ⟨count,range⟩ := recorded_values history capacity
  exact ⟨count,range,range ▸ List.nodup_range' 1 (by decide)⟩

/-- The completion counter selects exactly one last finisher once the queue's
positive total has been reached. The index counts actual RMWs on this counter,
so arbitrarily many operations by other workers may intervene. -/
theorem last_finisher {N A} {first final : Pair N A} {log : List Nat}
    (history : Recorded .phase1Done first final log) (fresh : first.1.counts .phase1Done = 0)
    (capacity : log.length < 2 ^ System.Platform.numBits) (total : Usize)
    (positive : 0 < total.val) (reached : total.val ≤ final.1.counts .phase1Done) :
    ∃! i : Fin log.length, log[i.val] + 1 = total.val := by
  obtain ⟨count,range⟩ := recorded_values history (by simpa [fresh] using capacity)
  have values (i : Fin log.length) : log[i.val] = i.val := by
    have h := congrArg (fun l : List Nat => l[i.val]?) range
    simpa [fresh,List.getElem?_eq_getElem,i.isLt] using h
  rw [count,fresh,Nat.zero_add] at reached
  let winner : Fin log.length := ⟨total.val-1,by omega⟩
  refine ⟨winner,?_,?_⟩
  · change log[winner.val] + 1 = total.val
    rw [values winner]; dsimp [winner]; omega
  · intro j other
    rw [values] at other
    apply Fin.ext
    dsimp [winner]; omega

private theorem allowed_persists {f : Shared N → Shared N} (ok : Allowed N f) (h : Shared N) :
    (h.ready = true → (f h).ready = true) ∧
    ∀ (k : Key) (v : Payload N k), h.cells k = some v → (f h).cells k = some v := by
  cases ok with
  | observe | issue => exact ⟨id,fun _ _ same => same⟩
  | publish => exact ⟨fun _ => rfl,fun _ _ same => same⟩
  | store key value =>
    unfold put
    simp only [slot] at *
    cases prior : h.cells key with
    | some => exact ⟨id,fun _ _ same => same⟩
    | none =>
      refine ⟨id,?_⟩
      intro k v full
      by_cases same : key = k
      · subst k; rw [prior] at full; contradiction
      · exact (ParallelWorkerHeap.frame h.toHeap k key same value).trans full

/-- Every previously published cell retains its exact payload, and READY is
monotone, under arbitrary raw scheduling of certified callbacks. -/
theorem published_persists {N A} {start final : Shared N} {workers out : List (Program (Shared N) A)}
    (safe : All workers) (run : Steps start workers final out) :
    (start.ready = true → final.ready = true) ∧
    ∀ (k : Key) (v : Payload N k), start.cells k = some v → final.cells k = some v := by
  obtain ⟨_,path,_⟩ := annotate .phase1Next run safe
  generalize firstEq : (start,workers) = first at path
  generalize lastEq : (final,out) = last at path
  have keep (x y : Pair N A) (log) (s : Recorded .phase1Next x y log) :
      (x.1.ready = true → y.1.ready = true) ∧
      ∀ k v, x.1.cells k = some v → y.1.cells k = some v := by
    induction s with
    | begin => exact ⟨id,fun _ _ => id⟩
    | @step h l r f k prior extra _ allowed _ ih =>
      have now := allowed_persists allowed h
      exact ⟨fun ready => now.1 (ih.1 ready),fun k v full => now.2 k v (ih.2 k v full)⟩
  subst first; subst last
  exact keep _ _ _ path

end ParallelWorkerCounterSafety
