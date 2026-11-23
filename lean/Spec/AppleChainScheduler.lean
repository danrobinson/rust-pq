import Std
import Spec.Sha256

/-! The native scheduler checks prove a refill admits one pending chain, and a
dispatch advances each live chain by its smallest positive remaining interval.
The physical slots can move, so this induction indexes logical jobs by their
original order. Its value type can be the entire SHA block, including the round
address, and the transition can be the seeded, truncated SHA-256 compression. -/

namespace Spec.AppleChainScheduler

structure Job (α : Type) where
  id : Nat
  atRound : Nat
  remaining : Nat
  value : α
  pending : Bool

def advance (f : Nat → α → α) (start : Nat) (val : α) : Nat → α
  | 0 => val
  | r+1 => advance f (start+1) (f start val) r

private theorem advance_append (f : Nat → α → α) (start : Nat) (val : α) (a b : Nat) :
    advance f (start+a) (advance f start val a) b = advance f start val (a+b) := by
  induction a generalizing start val with
  | zero => simp [advance]
  | succ a ih =>
    rw [Nat.succ_add, advance, advance, ← ih]
    congr 1 <;> omega

def finish (round : Nat → Nat → α → α) (j : Job α) :=
  advance (round j.id) j.atRound j.value j.remaining

def work (j : Job α) := j.remaining + (if j.pending then 1 else 0)

inductive Change (round : Nat → Nat → α → α) : Job α → Job α → Prop
  | enqueue (j : Job α) (unread : j.pending = true) : Change round j { j with pending := false }
  | run (j : Job α) (live : j.pending = false) (r : Nat) (pos : 0 < r) (bound : r ≤ j.remaining) :
      Change round j { j with atRound := j.atRound + r, remaining := j.remaining - r,
                               value := advance (round j.id) j.atRound j.value r }

private theorem changed {r : Nat → Nat → α → α} {a b} (h : Change r a b) :
    finish r b = finish r a ∧ work b < work a := by
  cases h with
  | enqueue p => simp [finish,work,p]
  | run p count pos bound =>
    constructor
    · simp only [finish,advance_append]; congr 1; omega
    · simp [work,p]; omega

/-- Sweep visits logical indices in order. Finished and unselected jobs stay unchanged. -/
inductive Sweep (r : Nat → Nat → α → α) : Bool → List (Job α) → List (Job α) → Prop
  | nil : Sweep r false [] []
  | keep {flag a b} (j) : Sweep r flag a b → Sweep r flag (j::a) (j::b)
  | change {flag a b x y} : Change r x y → Sweep r flag a b → Sweep r true (x::a) (y::b)

def budget (jobs : List (Job α)) := (jobs.map work).sum

private theorem sweep_spec {r : Nat → Nat → α → α} {flag a b} (h : Sweep r flag a b) :
    b.map (finish r) = a.map (finish r) ∧
    budget b ≤ budget a ∧ (flag = true → budget b < budget a) := by
  induction h with
  | nil => simp [budget]
  | keep j hs ih =>
    obtain ⟨out,weak,strong⟩ := ih
    simp only [List.map_cons, List.sum_cons, budget] at *
    exact ⟨by rw [out],by omega,fun f => by have := strong f; omega⟩
  | change hc hs ih =>
    obtain ⟨out,weak,_⟩ := ih
    obtain ⟨keep,less⟩ := changed hc
    simp only [List.map_cons,List.sum_cons,budget] at *
    exact ⟨by rw [out,keep],by omega,fun _ => by omega⟩

private theorem empty_work {r : Nat → Nat → α → α} (a : List (Job α)) (h : budget a = 0) :
    a.map Job.value = a.map (finish r) := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    simp only [budget,List.map_cons,List.sum_cons] at h
    have zero : x.remaining = 0 := by dsimp [work] at h; omega
    have tail : budget xs = 0 := by dsimp [budget]; omega
    simp [finish,zero,advance,ih tail]

inductive Execution (r : Nat → Nat → α → α) : List (Job α) → List (Job α) → Prop
  | done (a) : Execution r a a
  | more {a b c} : Sweep r true a b → Execution r b c → Execution r a c

/-- Every admissible choice of active slots makes progress. -/
theorem all_steps_terminate (r : Nat → Nat → α → α) :
    WellFounded (fun b a => Sweep r true a b) :=
  Subrelation.wf (fun h => (sweep_spec h).2.2 rfl) (measure budget).wf

theorem every_completed_result {r : Nat → Nat → α → α} {a b}
    (exec : Execution r a b) (doneWork : budget b = 0) :
    b.map Job.value = a.map (finish r) := by
  have h : b.map (finish r) = a.map (finish r) := by
    induction exec with
    | done => rfl
    | more hs _ ih => exact (ih doneWork).trans (sweep_spec hs).1
  exact (empty_work _ doneWork).trans h

/-- Progress of each positive-work scheduler iteration gives finite termination
and precisely the original reference result at every original chain index. -/
theorem termination_and_outputs (r : Nat → Nat → α → α)
    (progress : ∀ a, 0 < budget a → ∃ b, Sweep r true a b) (input : List (Job α)) :
    ∃ final, Execution r input final ∧ budget final = 0 ∧
      final.map Job.value = input.map (finish r) := by
  generalize hx : budget input = n
  induction n using Nat.strongRecOn generalizing input with
  | ind n ih =>
    by_cases z : budget input = 0
    · exact ⟨input,.done _,z,empty_work _ z⟩
    · obtain ⟨b,sweep⟩ := progress input (by omega)
      obtain ⟨eqv,_,lt⟩ := sweep_spec sweep
      obtain ⟨f,exec,endWork,out⟩ := ih (budget b) (by have := lt rfl; omega) b rfl
      exact ⟨f,.more sweep exec,endWork,out.trans eqv⟩

/-- The concrete 64-byte block recurrence used in the executable's chain checks.
The original block supplies its compressed address, padding, and any second child.
Its four-byte hash address is replaced before each seeded compression. -/
def sha256Round (n : Nat) (seedState : List SHA256.Word) (_id counter : Nat)
    (block : Bytes) : Bytes :=
  let msg := block.take 18 ++ toByte counter 4 ++ block.drop 22
  let digest := (SHA256.compress seedState msg).flatMap fun w => toByte w.toNat 4
  msg.take 22 ++ digest.take n ++ msg.drop (22+n)

theorem every_sha256_result {n : Nat} {seedState : List SHA256.Word} {input final}
    (exec : Execution (sha256Round n seedState) input final) (doneWork : budget final = 0) :
    final.map Job.value = input.map (finish (sha256Round n seedState)) :=
  every_completed_result exec doneWork

#print axioms every_sha256_result
#print axioms termination_and_outputs
#print axioms all_steps_terminate
#print axioms every_completed_result
end Spec.AppleChainScheduler
