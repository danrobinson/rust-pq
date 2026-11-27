import Parallel.WorkerMir
import Parallel.WorkerBarrier

namespace slhdsa.WorkerBarrierMir
open ParallelWorkerMir

inductive Phase where | running | ready | aborted deriving DecidableEq, Repr
inductive Op where
  | acquire (dst : Nat)
  | compare (src : Nat) (phase : Phase) (eq : Bool)
  | accept | reject | other
  deriving DecidableEq

/-- Register and value of the most recent acquire of the phase atomic. -/
abbrev Seen := Option (Nat × Phase)

/-- Other branches are overapproximated. A compare on a register different from
the last acquire can likewise take either edge. MIR orders a false branch first. -/
def successors (op : Op) (old : Seen) (choice : Nat) : List Seen :=
  match op with
  | .acquire reg => [some (reg,.running),some (reg,.ready),some (reg,.aborted)]
  | .compare reg phase eq =>
    match old with
    | some (src, st) =>
      if src ≠ reg ∨ choice = ((decide (st = phase) == eq).toNat) then [old] else []
    | none => [old]
  | _ => [old]

def isReady : Seen → Bool
  | some (_, .ready) => true
  | _ => false

abbrev Facts := List (List Seen)
def factsAt (facts : Facts) (pc : Nat) : List Seen := facts[pc]?.getD []

def Certified (g : Graph) (decode : Nat → Op) (facts : Facts) : Prop :=
  none ∈ factsAt facts 0 ∧
    ∀ pc : Fin g.length, ∀ old ∈ factsAt facts pc,
      (decode g[pc].ops = .accept → isReady old = true) ∧
      ∀ i : Fin g[pc].successors.length, ∀ obs ∈ successors (decode g[pc].ops) old i,
        obs ∈ factsAt facts g[pc].successors[i]

instance (g : Graph) (decode : Nat → Op) (facts : Facts) :
    Decidable (Certified g decode facts) := by unfold Certified; infer_instance

/-- Execution of the actual normalized wait graph from its initial block,
logging individual primitive acquire results. The register is deliberately
unknown until the first load. -/
inductive Trace (g : Graph) (decode : Nat → Op) : Nat → Seen → Prop where
  | start : Trace g decode 0 none
  | step {pc old} (prior : Trace g decode pc old)
      (valid : pc < g.length) (edge : Fin g[pc].successors.length) {next}
      (result : next ∈ successors (decode g[pc].ops) old edge) :
      Trace g decode (g[pc].successors[edge]) next

theorem trace_certified {g decode facts} (cert : Certified g decode facts) {pc seen}
    (run : Trace g decode pc seen) : seen ∈ factsAt facts pc := by
  induction run with
  | start => exact cert.1
  | @step pc old _ bound edge next member prior =>
    exact (cert.2 ⟨pc,bound⟩ old prior).2 edge next member

theorem accepts_after_ready {g decode facts} (cert : Certified g decode facts) {pc seen}
    (run : Trace g decode pc seen) (valid : pc < g.length) (accept : decode g[pc].ops = .accept) :
    isReady seen = true :=
  (cert.2 ⟨pc,valid⟩ seen (trace_certified cert run)).1 accept

open WorkerBarrier

/-- Between two MIR blocks of the observing worker other callbacks may advance
the shared barrier heap. A ready acquire must read the sender's release. The
certificate, computed over every normal graph branch, determines when the
observing worker can return successfully. -/
inductive Interleaved (f : F) (a : A) (r : R) (g : Graph) (decode : Nat → Op) :
    Heap F A R → Nat → Seen → Prop where
  | start : Interleaved f a r g decode initial 0 none
  | heap {h pc seen h'} (prior : Interleaved f a r g decode h pc seen)
      (action : Step f a r h h') : Interleaved f a r g decode h' pc seen
  | block {h pc old} (prior : Interleaved f a r g decode h pc old)
      (valid : pc < g.length) (edge : Fin g[pc].successors.length) {next}
      (result : next ∈ successors (decode g[pc].ops) old edge)
      (load : ∀ dst, decode g[pc].ops = .acquire dst → isReady next = true → h.writer.released = true) :
      Interleaved f a r g decode h (g[pc].successors[edge]) next

theorem Interleaved.on_published_heap {f : F} {a : A} {r : R} {h}
    (g : Graph) (decode : Nat → Op) (heap : WorkerBarrier.Run f a r h) :
    Interleaved f a r g decode h 0 none := by
  induction heap with
  | refl => exact .start
  | tail _ step ih => exact .heap ih step

private theorem release_persists {f : F} {a : A} {r : R} {h h' : Heap F A R}
    (action : Step f a r h h') (published : h.writer.released = true) : h'.writer.released = true := by
  cases action <;> simp_all [Heap.move, Writer.released]

private theorem preserves_seen {P : Prop} {op old choice next} (member : next ∈ successors op old choice)
    (previous : isReady old = true → P) (observed : ∀ dst, op = .acquire dst → isReady next = true → P)
    (now : isReady next = true) : P := by
  cases op with
  | acquire dst => exact observed dst rfl now
  | compare src phase eq =>
    cases old <;> simp only [successors,List.mem_singleton] at member
    · exact previous (member ▸ now)
    · split at member <;> simp_all
  | accept | reject | other => simp [successors] at member; exact previous (member ▸ now)

theorem Interleaved.projects {f : F} {a : A} {r : R} {g decode h pc seen}
    (exec : Interleaved f a r g decode h pc seen) :
    WorkerBarrier.Run f a r h ∧ Trace g decode pc seen ∧ (isReady seen = true → h.writer.released = true) := by
  induction exec with
  | start => exact ⟨.refl,.start,by simp [isReady]⟩
  | heap _ action ih =>
    exact ⟨ih.1.tail action,ih.2.1,fun seen => release_persists action (ih.2.2 seen)⟩
  | block _ valid edge result load ih =>
    exact ⟨ih.1,.step ih.2.1 valid edge result,preserves_seen result ih.2.2 load⟩

theorem accepts_installed {f : F} {a : A} {r : R} {g decode facts h pc seen}
    (cert : Certified g decode facts) (exec : Interleaved f a r g decode h pc seen)
    (valid : pc < g.length) (ok : decode g[pc].ops = .accept) :
    h.cells = ⟨some f,some a,some r⟩ := by
  obtain ⟨heap,trace,observed⟩ := exec.projects
  have published := observed (accepts_after_ready cert trace valid ok)
  rw [(invariant heap).cells]
  cases hw : h.writer <;> simp_all [Writer.released,installed]

/-- The normalized sender CFG records the physical OnceLock destination or the
mutex/atomic/notification operation at each block. A returning execution may
have arbitrary branches and may revisit loop blocks. -/
inductive SenderOp where | effect (tag : Nat) | finish | other deriving DecidableEq

def SenderOp.record : SenderOp → List Nat → List Nat
  | .effect k, prior => k :: prior
  | _, prior => prior

abbrev SenderFacts := List (List (List Nat))
def senderAt (facts : SenderFacts) (pc : Nat) : List (List Nat) := facts[pc]?.getD []

def SenderCertified (g : Graph) (decode : Nat → SenderOp) (facts : SenderFacts)
    (order : List Nat) : Prop :=
  [] ∈ senderAt facts 0 ∧
    ∀ pc : Fin g.length, ∀ soFar ∈ senderAt facts pc,
      (decode g[pc].ops = .finish → soFar.reverse = order) ∧
      ∀ next ∈ g[pc].successors, (decode g[pc].ops).record soFar ∈ senderAt facts next

instance (g : Graph) (decode : Nat → SenderOp) (facts : SenderFacts) (order : List Nat) :
    Decidable (SenderCertified g decode facts order) := by unfold SenderCertified; infer_instance

inductive SenderTrace (g : Graph) (decode : Nat → SenderOp) : Nat → List Nat → Prop where
  | start : SenderTrace g decode 0 []
  | step {pc soFar} (prior : SenderTrace g decode pc soFar)
      (valid : pc < g.length) {next} (edge : next ∈ g[pc].successors) :
      SenderTrace g decode next ((decode g[pc].ops).record soFar)

theorem sender_returns {g decode facts order} (cert : SenderCertified g decode facts order)
    {pc soFar} (trace : SenderTrace g decode pc soFar) (valid : pc < g.length)
    (finish : decode g[pc].ops = .finish) : soFar.reverse = order := by
  suffices tracked : soFar ∈ senderAt facts pc from (cert.2 ⟨pc,valid⟩ soFar tracked).1 finish
  clear finish valid
  induction trace with
  | start => exact cert.1
  | @step pc old _ bound next edge ih => exact (cert.2 ⟨pc,bound⟩ old ih).2 next edge

end slhdsa.WorkerBarrierMir
