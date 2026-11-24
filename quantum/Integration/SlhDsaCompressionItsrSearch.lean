import Integration.SlhDsaCompressionItsrCover

namespace Reduction.Compression.MessageHash
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA KeyedHash OracleComp OracleSpec PQ.Interactive

variable (S : Sha2Set)
abbrev Cell := HmacKey.InputCell
abbrev Entry := Cell × Chain512

private theorem final_subset (hw : S.vp.params.n ≠ 16) (g : CompressionTables)
    (cand : Query S) (ts : List (Query S)) (u : Cell) (hu : u ∈ finalCells S g cand ts) :
    u ∈ cells S g cand ts := by
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hu)
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨x,hx,List.mem_append_right _ ?_⟩
  let st := mdFold g.2 MIdeal.Sha512.initial (ib S x)
  have len : (ob S x st).length = 2 := outer_length S hw x.1 x.2.1 st
  rcases List.eq_nil_or_concat (ob S x st) with h | ⟨bs,b,h⟩
  · simp [h] at len
  · change lastCell S g x ∈ mdCells g.2 MIdeal.Sha512.initial (ob S x st)
    change (mdFold g.2 MIdeal.Sha512.initial (ob S x st).dropLast,(ob S x st).getLast!) ∈ _
    simp [h,List.concat_eq_append,mdCells_append]

def trace (g : CompressionTables) (cand : Query S) (ts : List (Query S)) : List Entry :=
  (cells S g cand ts).map fun u => (u,g.2 u)

def select (i : Fin S.vp.params.k) (xs : List Entry) : Option HmacKey.Evidence :=
  match xs.find? (fun z => decide (z.2 = MIdeal.Sha512.initial)) with
  | some z => some (.inl z.1)
  | none => ((xs.product xs).find? (fun p => decide
      (p.1.1 ≠ p.2.1 ∧ coordinate S i p.1.2 = coordinate S i p.2.2))).map (fun p => .inr (p.1.1,p.2.1))

def accepts (i : Fin S.vp.params.k) (g : CompressionTables) : Option HmacKey.Evidence → Prop
  | none => False
  | some (.inl u) => g.2 u = MIdeal.Sha512.initial
  | some (.inr (u,v)) => u ≠ v ∧ coordinate S i (g.2 u) = coordinate S i (g.2 v)

noncomputable local instance (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)

open Classical in
/-- Reading the candidate and target paths extracts a fixed-IV preimage or two
distinct compression addresses matching both the FIPS leaf and FORS index i. -/
theorem selects_hit (hw : S.vp.params.n ≠ 16) (g : CompressionTables) (cand : Query S) (ts : List (Query S))
    (win : (itsrProblem S.vp (tablePrimitives g S.vp.params)).Wins ts cand) (i : Fin S.vp.params.k) :
    accepts S i g (select S i (trace S g cand ts)) := by
  let xs := trace S g cand ts
  have mem (e : Entry) (h : e ∈ xs) : g.2 e.1 = e.2 := by
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp h
    rfl
  have entry (u : Cell) (h : u ∈ cells S g cand ts) : (u,g.2 u) ∈ xs := List.mem_map.mpr ⟨_,h,rfl⟩
  change accepts S i g (select S i xs)
  unfold select
  cases he : xs.find? (fun z => decide (z.2 = MIdeal.Sha512.initial)) with
  | some z => exact (mem _ (List.mem_of_find?_eq_some he)).trans (of_decide_eq_true (List.find?_some (p := fun e : Entry => decide (e.2 = MIdeal.Sha512.initial)) he))
  | none =>
    let ok := fun p : Entry × Entry => decide (p.1.1 ≠ p.2.1 ∧ coordinate S i p.1.2 = coordinate S i p.2.2)
    change accepts S i g (((xs.product xs).find? ok).map _)
    cases hp : (xs.product xs).find? ok with
    | some p =>
      have m := List.mem_product.mp (List.mem_of_find?_eq_some hp)
      have h : p.1.1 ≠ p.2.1 ∧ coordinate S i p.1.2 = coordinate S i p.2.2 := of_decide_eq_true (List.find?_some (p := ok) hp)
      exact ⟨h.1,by rw [mem _ m.1,mem _ m.2]; exact h.2⟩
    | none =>
      exfalso
      have noPair (u v : Cell) (mu : u ∈ cells S g cand ts) (mv : v ∈ cells S g cand ts) (ne : u ≠ v)
          (eq : coordinate S i (g.2 u) = coordinate S i (g.2 v)) : False := by
        have hh := List.find?_eq_none.mp hp ((u,g.2 u),(v,g.2 v))
          (List.mem_product.mpr ⟨entry u mu,entry v mv⟩)
        simp [ok,ne,eq] at hh
      rcases win_witness S hw g cand ts win with cov | ⟨u,mu,hit⟩ | ⟨u,mu,v,mv,ne,eq⟩
      · obtain ⟨u,hu,h⟩ := cover_cells S g _ (List.nodup_dedup _) cov
        obtain ⟨v,hv,ne,eq⟩ := h i
        exact noPair _ _ (final_subset S hw g cand ts _ hu) (final_subset S hw g cand ts _ hv) ne eq
      · have hh := List.find?_eq_none.mp he (u,g.2 u) (entry _ mu)
        simp [hit] at hh
      · exact noPair _ _ mu mv ne (congrArg (coordinate S i) eq)

private theorem md_len (g : CF Chain512 Block512) (c : Chain512) (bs : List Block512) :
    (mdCells g c bs).length = bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [mdCells,ih]

def traceBudget (xs : List (Query S)) := (xs.map fun x => (ib S x).length+2).sum

private theorem cells_len (hw : S.vp.params.n ≠ 16) (g : CompressionTables) (cand : Query S) (ts : List (Query S)) :
    (cells S g cand ts).length ≤ traceBudget S (cand :: ts) := by
  apply (List.dedup_sublist _).length_le.trans
  have len (x : Query S) : (cellsH MIdeal.Sha512.initial (ib S) (ob S) g.2 x).length = (ib S x).length+2 := by
    simp only [cellsH,List.length_append,md_len,ob,outer_length S hw]
  simp only [List.length_flatMap,traceBudget,len]
  exact le_rfl

private theorem read_cost (xs : List Cell) :
    EvalCost (fun H => (pure (xs.map fun u => (u,(tablesOf H).2 u)) : ProbComp _)) xs.length := by
  induction xs with
  | nil => exact EvalCost.const (pure [])
  | cons u us ih =>
    have one := EvalCost.eval (X := Input) (Y := Output) (.inr u) (fun y => (arrayVectorEquivFin UInt64 8).symm y.2)
    have h := EvalCost.bind one fun c => ih.map (fun l => (u,c)::l)
    simp only [pure_bind,map_pure,Nat.add_comm 1] at h
    kexact h

/-- Public query budget to report a witness, including the SHA-512 reads used
to compare states and to check the FORS coordinate. -/
theorem select_cost (hw : S.vp.params.n ≠ 16) (cand : Query S) (ts : List (Query S)) (i : Fin S.vp.params.k) :
    EvalCost (fun H => (pure (select S i (trace S (tablesOf H) cand ts)) : ProbComp _))
      (traceBudget S (cand::ts) + traceBudget S (cand::ts)) := by
  let B := traceBudget S (cand::ts)
  have rd (xs : List Cell) := ((read_cost (xs.take B)).map (select S i)).mono (List.length_take_le B xs)
  have h := EvalCost.bind (cells_cost S hw cand ts) rd
  have take (H : Input → Output) : (cells S (tablesOf H) cand ts).take B = cells S (tablesOf H) cand ts :=
    List.take_of_length_le (cells_len S hw _ cand ts)
  simp only [pure_bind,map_pure,take] at h
  exact h

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.selects_hit
#print axioms Reduction.Compression.MessageHash.select_cost
