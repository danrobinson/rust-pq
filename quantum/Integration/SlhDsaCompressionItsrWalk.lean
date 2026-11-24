import Integration.SlhDsaCompressionItsrEvidence

namespace Reduction.Compression.MessageHash
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA OracleComp OracleSpec PQ.Interactive
variable (S : Sha2Set)

private theorem list_cost {A B : Type} (f : (Input → Output) → A → B) (cost : A → ℕ)
    (hf : ∀ x, EvalCost (fun H => (pure (f H x) : ProbComp B)) (cost x)) (xs : List A) :
    EvalCost (fun H => (pure (xs.map (f H)) : ProbComp (List B))) (xs.map cost).sum := by
  induction xs with
  | nil => exact EvalCost.const (pure [])
  | cons x xs ih =>
    have h := EvalCost.bind (hf x) fun y => ih.map (List.cons y)
    simpa only [pure_bind,map_pure,List.map_cons,List.sum_cons] using h

private theorem walk_cost (c : Chain512) (bs : List Block512) :
    EvalCost (fun H => (pure (mdFold (tablesOf H).2 c bs, mdCells (tablesOf H).2 c bs) : ProbComp _)) bs.length := by
  induction bs generalizing c with
  | nil => exact EvalCost.const (pure (c,[]))
  | cons b bs ih =>
    have one := EvalCost.eval (X := Input) (Y := Output) (.inr (c,b))
      (fun y => (arrayVectorEquivFin UInt64 8).symm y.2)
    have h := EvalCost.bind one fun t => (ih t).map (fun z => (z.1,(c,b)::z.2))
    simp only [pure_bind,map_pure,Nat.add_comm 1] at h
    kexact h

private theorem path_cost (hw : S.vp.params.n ≠ 16) (x : Query S) :
    EvalCost (fun H => (pure (cellsH MIdeal.Sha512.initial (ib S) (ob S) (tablesOf H).2 x) : ProbComp _))
      ((ib S x).length+2) := by
  have h := EvalCost.bind (walk_cost MIdeal.Sha512.initial (ib S x)) fun z =>
    ((walk_cost MIdeal.Sha512.initial (ob S x z.1)).map (fun w => z.2 ++ w.2)).mono
      (show (ob S x z.1).length ≤ 2 from (outer_length S hw x.1 x.2.1 z.1).le)
  simpa only [pure_bind,map_pure,cellsH] using h

/-- Reading all compression addresses in the actual candidate and target paths.
Duplicates are removed after evaluation. The count charges each inner and outer block once. -/
theorem cells_cost (hw : S.vp.params.n ≠ 16) (cand : Query S) (ts : List (Query S)) :
    EvalCost (fun H => (pure (cells S (tablesOf H) cand ts) : ProbComp _))
      (((cand::ts).map (fun x => (ib S x).length+2)).sum) := by
  have h := (list_cost (fun H => cellsH MIdeal.Sha512.initial (ib S) (ob S) (tablesOf H).2)
    _ (path_cost S hw) (cand::ts)).map (fun xs => xs.flatten.dedup)
  simpa only [map_pure,cells,List.flatMap_def] using h

theorem finalCells_cost (hw : S.vp.params.n ≠ 16) (cand : Query S) (ts : List (Query S)) :
    EvalCost (fun H => (pure (finalCells S (tablesOf H) cand ts) : ProbComp _))
      (((cand::ts).map (fun x => (ib S x).length+1)).sum) := by
  have h := (list_cost (fun H => lastCell S (tablesOf H)) _ (lastCell_cost S hw) (cand::ts)).map List.dedup
  simpa only [map_pure,finalCells] using h

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.cells_cost
#print axioms Reduction.Compression.MessageHash.finalCells_cost
