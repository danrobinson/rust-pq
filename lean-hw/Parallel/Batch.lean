import Parallel.Signing

namespace ParallelBatch

/-- A ticket is removed from the outstanding set only after its verifier has
returned. A false verdict can stop further claims while other tickets finish. -/
inductive Run (n : Nat) (verify : Nat → Bool) :
    Nat → (Nat → Prop) → Bool → Prop where
  | start : Run n verify 0 (fun _ => False) true
  | claim {k pending flag} : Run n verify k pending flag → k < n →
      Run n verify (k+1) (fun j => j=k ∨ pending j) flag
  | finish {k pending flag i} : Run n verify k pending flag → pending i →
      Run n verify k (fun j => j≠i ∧ pending j) (flag && verify i)

private theorem invariant {n f k pending flag} (r : Run n f k pending flag) :
    (∀ i, pending i → i < k ∧ i < n) ∧
    (flag = false → ∃ i < n, f i = false) ∧
    (flag = true → ∀ i < k, ¬pending i → f i = true) := by
  induction r with
  | start => simp
  | claim prior bound ih =>
    obtain ⟨bounds, rejected, accepted⟩ := ih
    refine ⟨?_,rejected,?_⟩
    · intro i hi
      rcases hi with rfl | old
      · exact ⟨by omega,bound⟩
      · obtain ⟨_,_⟩ := bounds i old
        exact ⟨by omega,by omega⟩
    · intro ok i hi done
      apply accepted ok i (by by_contra h; exact done (Or.inl (by omega)))
      exact fun old => done (Or.inr old)
  | @finish k pend flag i prior active ih =>
    obtain ⟨bounds, rejected, accepted⟩ := ih
    refine ⟨fun j hj => bounds j hj.2,?_,?_⟩
    · cases h : _ && _ <;> simp_all
      cases flag <;> simp_all
      exact ⟨i,(bounds i active).2,by assumption⟩
    · intro both j hj absent
      obtain ⟨ok, valid⟩ := Bool.and_eq_true_iff.mp both
      by_cases same : j = i
      · subst j; exact valid
      · exact accepted ok j hj (fun old => absent ⟨same,old⟩)

/-- A normally joined dispatch has no outstanding work. A still-true
accumulator permits worker exit only after the queue has been exhausted. -/
theorem verify_all {n f k flag} (run : Run n f k (fun _ => False) flag)
    (stopped : flag = true → n ≤ k) :
    flag = true ↔ ∀ i < n, f i = true := by
  obtain ⟨_, rejected, accepted⟩ := invariant run
  constructor
  · intro ok i hi
    exact accepted ok i (Nat.lt_of_lt_of_le hi (stopped ok)) id
  · intro all
    cases flag with
    | true => rfl
    | false =>
      obtain ⟨i,hi,bad⟩ := rejected rfl
      simp [all i hi] at bad

/-- The per-item API publishes to the ticket index, irrespective of the
relative completion times of other items. -/
def results (verify : Nat → Bool) (done : List Nat) : Nat → Bool :=
  done.foldl (fun old i j => if j = i then verify i else old j) (fun _ => false)

private theorem lookup (verify : Nat → Bool) (done : List Nat) (j : Nat) :
    results verify done j = (decide (j ∈ done) && verify j) := by
  induction done using List.reverseRecOn with
  | nil => simp [results]
  | append_singleton xs i ih =>
    simp only [results, List.foldl_append,List.foldl_cons,List.foldl_nil] at *
    by_cases same : j = i <;> simp [same, ih]

theorem verify_each {n k done} (trace : ParallelSigning.Trace n k [] done) (drained : n < k)
    (verify : Nat → Bool) (j : Nat) (hj : j < n) :
    results verify done j = verify j := by
  simp [lookup, ((trace.joined drained).exactly_once.2 j).mpr hj]

end ParallelBatch
