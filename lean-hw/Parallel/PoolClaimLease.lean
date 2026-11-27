import Parallel.PoolCallerLease
namespace ParallelPool.Lease.Claim

abbrev Edge := Nat × Nat

/-- All MIR paths, including loops and unwind successors. -/
inductive Path (g : List Edge) (start : Nat) : Nat → List Edge → Prop where
  | empty : Path g start start []
  | step {pc trail dst} : Path g start pc trail → (pc,dst)∈g → Path g start dst ((pc,dst)::trail)

/-- A reachable-set overapproximation after removing specific edges. -/
def separated (g : List Edge) (start target : Nat) (cut : List Edge) (seen : List Nat) : Bool :=
  seen.contains start && !seen.contains target &&
    g.all (fun e => !seen.contains e.1 || cut.contains e || seen.contains e.2)

theorem passes {g start target cut seen} (certificate : separated g start target cut seen=true)
    {trail} (run : Path g start target trail) : ∃ edge, edge∈trail ∧ edge∈cut := by
  simp only [separated,Bool.and_eq_true,Bool.not_eq_true',List.contains_iff_mem,List.all_eq_true,
    Bool.or_eq_true] at certificate
  have step {pc} {actions} (path : Path g start pc actions) :
      pc∈seen ∨ ∃ e, e∈actions ∧ e∈cut := by
    induction path with
    | empty => exact .inl certificate.1.1
    | @step pc history dst prior edge ih =>
      rcases ih with present | ⟨e,mem,cutMem⟩
      · have h := certificate.2 _ edge
        simp [present] at h
        rcases h with cutMem | visited
        · exact .inr ⟨_,List.mem_cons_self,cutMem⟩
        · exact .inl visited
      · exact .inr ⟨e,List.mem_cons_of_mem _ mem,cutMem⟩
  exact (step run).resolve_left (by simpa using certificate.1.2)

end ParallelPool.Lease.Claim
