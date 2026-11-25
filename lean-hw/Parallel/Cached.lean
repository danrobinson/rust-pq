import Std

namespace ParallelCached

/-- Successful fetch-add tickets introduce every write performed by that job.
Workers may interleave individual publications, even inside a grouped job.
Reading the slots waits for the pool join. -/
inductive Run {S V : Type} [DecidableEq S] (n : Nat) (writes : Nat → List (S × V)) :
    Nat → List (S × V) → (S → Option V) → Prop where
  | start : Run n writes 0 [] (fun _ => none)
  | claim {ticket pending cells} : Run n writes ticket pending cells → ticket < n →
      Run n writes (ticket+1) (writes ticket ++ pending) cells
  | publish {ticket before after cells slot value} :
      Run n writes ticket (before ++ (slot,value) :: after) cells →
      cells slot = none →
      Run n writes ticket (before ++ after) (fun s => if s = slot then some value else cells s)

private theorem ledger {S V : Type} [DecidableEq S] {n ticket : Nat} {writes : Nat → List (S × V)} {pending cells}
    (run : Run n writes ticket pending cells) (s : S) (v : V) :
    (∃ j < ticket, (s,v) ∈ writes j) ↔ (s,v) ∈ pending ∨ cells s = some v := by
  induction run with
  | start => simp
  | @claim t pending cells _ _ ih =>
    simp only [List.mem_append]
    constructor
    · rintro ⟨j,hj,hw⟩
      by_cases e : j = t
      · exact Or.inl (Or.inl (e ▸ hw))
      · rcases ih.mp ⟨j, by omega, hw⟩ with h|h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rintro ((hw | hp) | hc)
      · exact ⟨t,by omega,hw⟩
      · obtain ⟨j,hj,hw⟩ := ih.mpr (Or.inl hp)
        exact ⟨j,by omega,hw⟩
      · obtain ⟨j,hj,hw⟩ := ih.mpr (Or.inr hc)
        exact ⟨j,by omega,hw⟩
  | @publish t before after cells slot value _ empty ih =>
    rw [ih]
    by_cases h : s = slot
    · subst s
      simp [empty, List.mem_cons]
      grind
    · simp [h, List.mem_cons]

/-- At a normal join every reported cell has exactly its claimed job value.
Thus comparing one completed ledger to a reference suffices for any other
normally completed execution, irrespective of publication order. -/
theorem joined {S V : Type} [DecidableEq S] {n : Nat} {writes : Nat → List (S × V)} {cells}
    (run : Run n writes n [] cells) (s : S) (v : V) :
    cells s = some v ↔ ∃ j < n, (s,v) ∈ writes j := by
  simpa only [List.not_mem_nil,false_or] using (ledger run s v).symm

theorem interleavings {S V : Type} [DecidableEq S] {n : Nat} {writes : Nat → List (S × V)} {a b}
    (left : Run n writes n [] a) (right : Run n writes n [] b) : a = b := by
  funext s
  cases ha : a s with
  | some v => exact ((joined right s v).mpr ((joined left s v).mp ha)).symm
  | none =>
    cases hb : b s with
    | none => rfl
    | some v =>
      have e := (joined left s v).mpr ((joined right s v).mp hb)
      simp [ha] at e

end ParallelCached
