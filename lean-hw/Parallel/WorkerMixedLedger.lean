import Parallel.WorkerPhaseOne

open Aeneas Aeneas.Std ParallelWorkerHeap ParallelWorkerRuntime
namespace ParallelPhaseOne

/-- Ticket numbers are positions in the sorted physical queue. One worker owns
each active ticket until its completion RMW. -/
structure Ledger (jobs : Nat) where
  next : Nat
  finished : Finset (Fin jobs)
  owners : List (Option (Fin jobs))

def Ledger.active (s : Ledger jobs) := s.owners.filterMap id

structure Ledger.Valid (s : Ledger jobs) : Prop where
  unique : s.active.Nodup
  separate : ∀ i ∈ s.active, i ∉ s.finished
  issued : ∀ i : Fin jobs, (i.val < s.next ↔ i ∈ s.active ∨ i ∈ s.finished)

theorem Ledger.initial (jobs workers : Nat) :
    Valid (jobs:=jobs) ⟨0,∅,List.replicate workers none⟩ := by
  constructor <;> simp [active]

theorem Ledger.claim {jobs n completed left right} (i : Fin jobs) (ticket : i.val=n)
    (before : Valid (jobs:=jobs) ⟨n,completed,left ++ none :: right⟩) :
    Valid ⟨n+1,completed,left ++ some i :: right⟩ := by
  obtain ⟨unique,apart,issued⟩ := before
  simp [active] at unique apart issued ⊢
  have fresh := (issued i).not.mp (by omega)
  simp only [not_or] at fresh
  constructor
  · simp [active,List.nodup_append,List.nodup_cons] at unique ⊢
    exact ⟨unique.1,fresh.1.2,unique.2.1,fun a ha =>
      ⟨fun e => fresh.1.1 (e ▸ ha),unique.2.2 a ha⟩⟩
  · intro j mem
    simp [active] at mem
    rcases mem with h|rfl|h
    · exact apart j (Or.inl h)
    · tauto
    · exact apart j (Or.inr h)
  · intro j
    simp [active]
    by_cases same : j=i
    · subst j; simp [ticket]
    · have ne : j.val ≠ n := fun e => same (Fin.ext (e.trans ticket.symm))
      specialize issued j
      have bound : j.val≤n ↔ j.val<n := by omega
      tauto

theorem Ledger.complete {jobs n completed left right} (i : Fin jobs)
    (before : Valid (jobs:=jobs) ⟨n,completed,left ++ some i :: right⟩) :
    i ∉ completed ∧ Valid ⟨n,insert i completed,left ++ none :: right⟩ := by
  obtain ⟨unique,apart,issued⟩ := before
  simp [active] at unique apart issued
  refine ⟨apart i (by simp),?_⟩
  constructor
  · simp [active,List.nodup_append,List.nodup_cons] at unique ⊢
    exact ⟨unique.1,unique.2.2.1,fun a ha => (unique.2.2.2 a ha).2⟩
  · intro j mem
    simp [active] at mem
    have prev := apart j (by tauto)
    have ne : j ≠ i := by
      intro e; subst j
      simp [List.nodup_append,List.nodup_cons] at unique
      exact mem.elim (fun hi => (unique.2.2.2 i hi).1 rfl) unique.2.1
    simp [ne,prev]
  · intro j
    simpa [active,or_assoc,or_left_comm,or_comm] using issued j

theorem Ledger.exhausted {jobs n completed left right} (limit : jobs ≤ n)
    (before : Valid (jobs:=jobs) ⟨n,completed,left ++ none :: right⟩) :
    Valid ⟨n+1,completed,left ++ none :: right⟩ := by
  refine ⟨before.unique,before.separate,fun i => ?_⟩
  have prior := before.issued i
  change i.val<n ↔ _ at prior
  have bound := i.isLt
  change i.val<n+1 ↔ _
  exact (iff_of_true (by omega) (by omega)).trans prior

/-- At the last completion RMW every physical queue index has contributed its
job's entire write list, including jobs with several distinct scatter lanes. -/
theorem Ledger.at_reduction {jobs} {s : Ledger jobs} (total : s.finished.card=jobs)
    (published : Fin jobs → Prop) (kept : ∀ i ∈ s.finished, published i) :
    ∀ i, published i := by
  have full : s.finished = Finset.univ := Finset.eq_univ_of_card _ (by simpa using total)
  intro i
  exact kept i (by simp [full])

end ParallelPhaseOne
