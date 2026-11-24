import Integration.SlhDsaCompressionSearchSplit
import MIdeal.Itsr512

namespace Reduction.Compression.MessageHash
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA KeyedHash
variable (S : Sha2Set)
noncomputable local instance (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)

abbrev Query := S.Node × MIdeal.Hmsg.Input S

/-- The last compression input of MGF1 after hashing R, PK.seed, PK.root and M. -/
def lastCell (g : CompressionTables) (x : Query S) : HmacKey.InputCell :=
  let bs := ob S x (mdFold g.2 MIdeal.Sha512.initial (ib S x))
  (mdFold g.2 MIdeal.Sha512.initial bs.dropLast, bs.getLast!)

/-- The complete SHA-512 paths for the candidate and target transcript, counting
each physical address once even when different messages share a prefix. -/
def cells (g : CompressionTables) (cand : Query S) (ts : List (Query S)) :=
  ((cand :: ts).flatMap (cellsH MIdeal.Sha512.initial (ib S) (ob S) g.2)).dedup

def finalCells (g : CompressionTables) (cand : Query S) (ts : List (Query S)) :=
  ((cand :: ts).map (lastCell S g)).dedup

open Classical in
/-- At every fixed table, an ITSR win covers a final digest on distinct
compression inputs, repeats a full SHA-512 state at distinct inputs, or hits the IV. -/
theorem win_witness (hw : S.vp.params.n ≠ 16) (g : CompressionTables) (cand : Query S)
    (ts : List (Query S))
    (win : (itsrProblem S.vp (tablePrimitives g S.vp.params)).Wins ts cand) :
    CovP (idxOf S.vp) ((finalCells S g cand ts).map fun u => digest S (g.2 u)) ∨
    (∃ u ∈ cells S g cand ts, g.2 u = MIdeal.Sha512.initial) ∨
    (∃ u ∈ cells S g cand ts, ∃ v ∈ cells S g cand ts, u ≠ v ∧ g.2 u = g.2 v) := by
  classical
  have w : (probI MIdeal.Sha512.initial (ib S) (ob S) (digest S) (idxOf S.vp) g.2).Wins ts cand :=
    (congrArg (fun p : ITSRProblem S.Node (MIdeal.Hmsg.Input S) (Bytes S.vp.params.m) (Adrs × ℕ) => p.Wins ts cand) (itsr_problem S g hw)).mp win
  let a := cells S g cand ts
  have subset (x : Query S) (hx : x ∈ cand :: ts) (c) (hc : c ∈ cellsH MIdeal.Sha512.initial (ib S) (ob S) g.2 x) :
      c ∈ a := by
    apply List.mem_dedup.mpr
    exact List.mem_flatMap.mpr ⟨x,hx,hc⟩
  have log (x : Query S) (hx : x = cand ∨ x ∈ ts) (bs b)
      (he : ob S x (mdFold g.2 MIdeal.Sha512.initial (ib S x)) = bs ++ [b]) :
      (mdFold g.2 MIdeal.Sha512.initial bs,b) ∈ finalCells S g cand ts := by
    apply List.mem_dedup.mpr
    refine List.mem_map.mpr ⟨x,List.mem_cons.mpr hx,?_⟩
    simp [lastCell,he]
  have h := win_imp MIdeal.Sha512.initial (ib S) (ob S) (digest S) (idxOf S.vp)
    (ib_injective S) (ob_injective_state S) (fun x st hn => by
      have len := outer_length S hw x.1 x.2.1 st
      change (ob S x st).length = 2 at len
      simp [hn] at len) g.2 a (finalCells S g cand ts) cand ts
    (subset _ (List.mem_cons_self ..)) (fun x hx => subset x (List.mem_cons_of_mem _ hx))
    (fun _ => log) w.1 (by
      intro i hi
      obtain ⟨x,hx,hit⟩ := List.mem_flatMap.mp (w.2 i hi)
      exact List.mem_flatMap.mpr ⟨_,List.mem_map.mpr ⟨x,hx,rfl⟩,hit⟩)
  rcases h with cov | bad
  · exact Or.inl cov
  · right
    by_contra! none
    have hi : Set.InjOn g.2 {u | u ∈ a} := by
      intro u hu v hv he
      by_contra hn
      exact none.2 u hu v hv hn he
    have nodup : (a.map g.2).Nodup := List.Nodup.map_on (fun _ hu _ hv he => hi hu hv he) (List.nodup_dedup _)
    have fresh : MIdeal.Sha512.initial ∉ a.map g.2 := fun h => by
      obtain ⟨u,hu,he⟩ := List.mem_map.mp h
      exact none.1 u hu he
    simp [badV,nodup,fresh] at bad

/-- Reading the inner hash and the first outer block determines the address
of the final MGF1 query. The final block itself has not been queried yet. -/
theorem lastCell_cost (hw : S.vp.params.n ≠ 16) (x : Query S) :
    PQ.Interactive.EvalCost (fun H => (pure (lastCell S (tablesOf H) x) : ProbComp _))
      ((ib S x).length + 1) := by
  have outer (st : Chain512) : PQ.Interactive.EvalCost (fun H =>
      (pure (mdFold (tablesOf H).2 MIdeal.Sha512.initial (ob S x st).dropLast,
        (ob S x st).getLast!) : ProbComp HmacKey.InputCell)) 1 := by
    have h := (fold512_cost MIdeal.Sha512.initial (ob S x st).dropLast).map (fun t => (t,(ob S x st).getLast!))
    have len : (ob S x st).length = 2 := outer_length S hw x.1 x.2.1 st
    simpa only [map_pure,List.length_dropLast,len] using h
  have h := PQ.Interactive.EvalCost.bind (fold512_cost MIdeal.Sha512.initial (ib S x)) outer
  simpa only [lastCell,pure_bind] using h

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.win_witness
#print axioms Reduction.Compression.MessageHash.lastCell_cost
