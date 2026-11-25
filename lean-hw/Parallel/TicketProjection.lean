import Parallel.Signing
namespace ParallelSigning

private theorem claim_all (jobs k : Nat) (h : k≤jobs) :
    Trace jobs k (List.range k).reverse [] := by
  induction k with
  | zero => exact .start
  | succ k ih => simpa [List.range_succ] using (Trace.claim (ih (by omega)) (by omega))

private theorem publish_order {jobs k : Nat} {pending done : List Nat} (order : List Nat)
    (t : Trace jobs k pending done) (perm : pending.Perm order) :
    Trace jobs k [] (order.reverse ++ done) := by
  induction order generalizing pending done with
  | nil =>
    have eq : pending=[] := List.Perm.eq_nil perm
    simpa [eq] using t
  | cons j tail ih =>
    simpa [List.reverse_cons,List.append_assoc] using ih (Trace.publish t perm) (List.Perm.refl tail)

/-- Any exactly-once completion order is a realizable projection of the counter
semantics. The final out-of-range fetch witnesses queue exhaustion. -/
theorem trace_of_perm {n : Nat} {done : List Nat} (perm : done.Perm (List.range n)) :
    Trace n (n+1) [] done := by
  have p := publish_order done.reverse (claim_all n n (by omega)) ((List.range n).reverse_perm.trans (perm.symm.trans done.reverse_perm.symm))
  exact Trace.stop (by simpa using p) (by omega)

/-- Restrict an arbitrary normally joined schedule to the physical writes for
one table. A replayed slot certificate suffices for all completion orders. -/
theorem projected_trace {jobs n issued : Nat} {done : List Nat}
    (trace : Trace jobs issued [] done) (exhausted : jobs < issued) (fields : Nat → List Nat)
    (cover : ((List.range jobs).flatMap fields).Perm (List.range n)) :
    Trace n (n+1) [] (done.flatMap fields) := by
  obtain ⟨unique,inside⟩ := (trace.joined exhausted).exactly_once
  have full : done.Perm (List.range jobs) :=
    (List.perm_ext_iff_of_nodup unique List.nodup_range).mpr
      (fun j => (inside j).trans List.mem_range.symm)
  exact trace_of_perm ((full.flatMap_right fields).trans cover)

end ParallelSigning
