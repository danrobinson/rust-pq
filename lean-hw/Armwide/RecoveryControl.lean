import Armwide.RecoverySchedule
import Armwide.RecoveryControlProgram
namespace slhdsa.Armwide.Recovery
open WotsRefill

/-- Ordered provenance of surviving registers, available queue suffix and store operands. -/
def plan {I J : Type} : List (Bool × I) → List J → List (Sum I J) × List J × List I
  | [], q => ([],q,[])
  | (live,i)::rest,q =>
    if live then
      let (ls,more,writes) := plan rest q
      (Sum.inl i :: ls, more, writes)
    else match q with
      | [] =>
        let (ls,more,writes) := plan rest []
        (ls,more,i::writes)
      | j::tail =>
        let (ls,more,writes) := plan rest tail
        (Sum.inr j :: ls, more, i::writes)

/-- Applying the source-projected lane origins to arbitrary registers rebuilds
the exact retire operation used in the WOTS recovery simulation. -/
theorem plan_retire {I J O : Type} (old : I → RecoverLane) (queued : J → Nat)
    (sig : Nat → Spec.Bytes) (d : Nat → Nat) (write : O → Nat → Spec.Bytes → O)
    (ls : List (Bool × I)) (q : List J) (out : O)
    (live : ∀ e∈ls, e.1=decide ((old e.2).left≠0)) :
    retire write sig d (ls.map (fun e => old e.2)) (q.map queued) out =
      let (active,more,stored) := plan ls q
      (active.map (Sum.elim old (fun j => fresh sig d (queued j))), more.map queued,
       stored.foldl (fun o i => write o (old i).chain (old i).x) out) := by
  induction ls generalizing q out with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨keep,i⟩ := e
    have tag := live (keep,i) (by simp)
    have all (x) (hx : x∈es) := live x (List.mem_cons_of_mem _ hx)
    cases keep
    · have h : (old i).left=0 := by simpa using tag.symm
      cases q <;> simp [plan,retire,h,ih _ _ all]
      exact ih [] _ all
    · have h : (old i).left≠0 := by simpa using tag.symm
      simp [plan,retire,h,ih _ _ all]

/-- One pass examines at most one queued item per old lane. Arbitrarily long
queues use precisely the same physical routes as their first four entries. -/
theorem plan_queue_suffix {I J : Type} (ls : List (Bool × I)) (q more : List J)
    (enough : ls.length≤q.length) :
    plan ls (q++more) =
      let (active,rest,written) := plan ls q
      (active,rest++more,written) := by
  induction ls generalizing q with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨keep,i⟩ := e
    cases keep
    · cases q with
      | nil => simp at enough
      | cons j tail =>
        simp only [List.length_cons,Nat.add_le_add_iff_right] at enough
        simp [plan,ih tail enough]
    · have h : es.length≤q.length := by simp only [List.length_cons] at enough;omega
      simp [plan,ih q h]

def summarize (a mask q : Nat) :=
  let ls := (List.range a).map (fun i => (mask.testBit i,i))
  let queue := List.range q
  let (alive,more,stored) := plan ls queue
  (a,mask,q,alive.map (Sum.elim id (4+·)),q-more.length,stored)

/-- All two-way retire decisions, legal active widths, and all queue prefixes
observable by a single round occur exactly once in the compiled source trace. -/
theorem control_complete : controlRows =
    (List.range 4).flatMap fun n =>
      (List.range (2^(n+1))).flatMap fun mask =>
        (List.range (if n+1=4 then 5 else 1)).map fun q => summarize (n+1) mask q := by decide

end slhdsa.Armwide.Recovery
