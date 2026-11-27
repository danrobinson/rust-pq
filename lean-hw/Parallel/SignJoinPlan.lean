import Parallel.SignJoinTable
namespace slhdsa.ParallelSignJoin
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def expand (runs : List (Nat × Nat)) : List Nat := runs.flatMap fun (first,count) => List.range' first count

def PhysicalRows.matches (r : PhysicalRows) (p : Spec.Params) : Bool :=
  r.n == p.n && r.d == p.d && (expand r.forest).length == p.k*(1+p.a) &&
    (expand r.auth).length == p.d*p.hp && (expand r.wots).length == p.d

def lookup (p : Spec.Params) := observed.find? (·.matches p)

/-- Six source-derived successful paths. The proof checks the physical row ID
of every published cell, including the final cell of the largest set. -/
theorem standard_lookup :
    [Spec.shake_128s,Spec.shake_128f,Spec.shake_192s,Spec.shake_192f,Spec.shake_256s,Spec.shake_256f].all
      (fun p => (lookup p).isSome) = true := by decide

private theorem physical_order : observed.all (fun r =>
    [r.forest,r.auth,r.wots].all fun v => expand v == List.range (expand v).length) = true := by decide

theorem read_order {p : Spec.Params} {r : PhysicalRows} (found : lookup p=some r) :
    expand r.forest = List.range (p.k*(1+p.a)) ∧ expand r.auth = List.range (p.d*p.hp) ∧
      expand r.wots = List.range p.d := by
  have mem := List.mem_of_find?_eq_some found
  have matchRow := List.find?_some found
  simp only [PhysicalRows.matches,Bool.and_eq_true,beq_iff_eq] at matchRow
  have checked := List.all_eq_true.mp physical_order r mem
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,beq_iff_eq] at checked
  exact ⟨checked.1.trans (congrArg List.range matchRow.1.1.2),
    checked.2.1.trans (congrArg List.range matchRow.1.2),checked.2.2.trans (congrArg List.range matchRow.2)⟩

end slhdsa.ParallelSignJoin
