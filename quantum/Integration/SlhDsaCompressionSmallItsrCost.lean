import Integration.SlhDsaCompressionSmallItsrEvidence

namespace Reduction.Compression.SmallItsr
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA OracleComp OracleSpec PQ.Interactive
variable (S : Sha2Set) (hs : S.vp.params.n = 16) {K : Type} [DecidableEq K] (key : St → K)

private theorem read (u : Cell) :
    EvalCost (fun H => (pure ((tablesOf H).1 u) : ProbComp St)) 1 :=
  EvalCost.eval (X := Input) (Y := Output) (.inl u) Prod.fst

private theorem walk (c : St) (bs : List Blk) :
    EvalCost (fun H => (pure (mdFold (tablesOf H).1 c bs, mdCells (tablesOf H).1 c bs) : ProbComp _)) bs.length := by
  induction bs generalizing c with
  | nil => exact EvalCost.const (pure (c,[]))
  | cons b bs ih =>
    have h := EvalCost.bind (read (c,b)) fun t => (ih t).map (fun z => (z.1,(c,b)::z.2))
    simp only [pure_bind,map_pure,Nat.add_comm 1] at h
    kexact h

private theorem path (x : Fast128.Input) :
    EvalCost (fun H => (pure (Fast128.cells (tablesOf H).1 x) : ProbComp _)) ((Fast128.innerBlocks x).length+3) := by
  have h := EvalCost.bind (walk IV128 (Fast128.innerBlocks x)) fun z =>
    (read (IV128,counterPrefix x.1 x.2.1 z.1)).map (fun t => z.2 ++
      [(IV128,counterPrefix x.1 x.2.1 z.1),(t,counterFinal 0),(t,counterFinal 1)])
  apply h.mono (by omega)

def charge (x : Query S) := (Fast128.innerBlocks (raw S hs x)).length+3
def traceBudget (xs : List (Query S)) := (xs.map (charge S hs)).sum

private theorem visits_cost (xs : List (Query S)) :
    EvalCost (fun H => (pure (visits S hs (tablesOf H) xs) : ProbComp _)) (traceBudget S hs xs) := by
  have paths : EvalCost (fun H => (pure (xs.map fun x => Fast128.cells (tablesOf H).1 (raw S hs x)) : ProbComp _))
      (traceBudget S hs xs) := by
    induction xs with
    | nil => exact EvalCost.const (pure [])
    | cons x xs ih =>
      have h := EvalCost.bind (path (raw S hs x)) fun y => ih.map (List.cons y)
      simpa only [traceBudget,charge,pure_bind,map_pure,List.map_cons,List.sum_cons] using h
  simpa only [visits,map_pure,List.flatMap_def] using paths.map (fun vs => vs.flatten.dedup)

private theorem md_length (g : CF St Blk) (c : St) (bs : List Blk) : (mdCells g c bs).length = bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [mdCells,ih]

private theorem visits_len (g : CompressionTables) (xs : List (Query S)) :
    (visits S hs g xs).length ≤ traceBudget S hs xs := by
  apply List.Sublist.length_le (List.dedup_sublist _ ) |>.trans
  simp only [List.length_flatMap,Fast128.cells,List.length_append,md_length,List.length_cons,List.length_nil,
    traceBudget,charge]
  exact le_rfl

private theorem read_list (xs : List Cell) :
    EvalCost (fun H => (pure (xs.map fun u => (u,(tablesOf H).1 u)) : ProbComp _)) xs.length := by
  induction xs with
  | nil => exact EvalCost.const (pure [])
  | cons u us ih =>
    have h := EvalCost.bind (read u) fun v => ih.map (List.cons (u,v))
    simpa only [pure_bind,map_pure,List.map_cons,List.length_cons,Nat.add_comm 1] using h

theorem select_cost (xs : List (Query S)) :
    EvalCost (fun H => (pure (select key (trace S hs (tablesOf H) xs)) : ProbComp _))
      (traceBudget S hs xs + traceBudget S hs xs) := by
  let B := traceBudget S hs xs
  have rd (us : List Cell) := ((read_list (us.take B)).map (select key)).mono (List.length_take_le B us)
  have h := EvalCost.bind (visits_cost S hs xs) rd
  have take (H : Input → Output) : (visits S hs (tablesOf H) xs).take B = visits S hs (tablesOf H) xs :=
    List.take_of_length_le (visits_len S hs _ xs)
  simp only [pure_bind,map_pure,take] at h
  exact h

def extractionBudget (L qs : ℕ) := (qs+1)*((L+56)/64+4)
theorem budget_le (L qs : ℕ) (cand : Query S) (ts : List (Query S)) (hc : cand.2.2.2.length ≤ L)
    (hlen : ts.length ≤ qs) (ht : ∀ x ∈ ts, x.2.2.2.length ≤ L) :
    traceBudget S hs (cand::ts) ≤ extractionBudget L qs := by
  let B := (L+56)/64+4
  have one (x : Query S) (le : x.2.2.2.length ≤ L) : charge S hs x ≤ B := by
    have len : (raw S hs x).2.2.2.length = x.2.2.2.length := by cases S <;> first | rfl | contradiction
    unfold charge Fast128.innerBlocks
    rw [iblocksH_length,len]
    dsimp [B]
    omega
  have sum : ∀ vs : List (Query S), (∀ x ∈ vs, x.2.2.2.length ≤ L) → traceBudget S hs vs ≤ B*vs.length := by
    intro vs
    induction vs with
    | nil => simp [traceBudget]
    | cons x xs ih =>
      intro ok
      simpa only [traceBudget,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ,Nat.add_comm B] using
        Nat.add_le_add (one x (ok x (List.mem_cons_self ..))) (ih (fun y hy => ok y (List.mem_cons_of_mem _ hy)))
  have h := sum (cand::ts) (by intro x hx; rcases List.mem_cons.mp hx with rfl|hx; exact hc; exact ht x hx)
  unfold extractionBudget
  rw [Nat.mul_comm (qs+1)]
  exact h.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hlen))
end Reduction.Compression.SmallItsr
#print axioms Reduction.Compression.SmallItsr.select_cost
#print axioms Reduction.Compression.SmallItsr.budget_le
