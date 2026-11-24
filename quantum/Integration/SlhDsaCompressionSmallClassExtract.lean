import Integration.SlhDsaCompressionChainScan
import MIdeal.Hash128f

namespace Reduction.Compression.SmallClass
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive
variable (S : Sha2Set) (hs : S.vp.params.n = 16)
private def node (v : S.Node) : Bytes 16 := cast (congrArg Bytes hs) v
private def nodes (vs : List S.Node) : List (Bytes 16) := cast (congrArg (fun n => List (Bytes n)) hs) vs

private theorem nodes_length (vs : List S.Node) : (nodes S hs vs).length = vs.length := by
  cases S <;> first | rfl | contradiction

private theorem nodes_injective : Function.Injective (nodes S hs) := by
  exact (Equiv.cast (congrArg (fun n => List (Bytes n)) hs)).injective

private theorem shape (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (vs : List S.Node) :
    node S hs ((tablePrimitives g S.vp.params).Thash pk a vs) =
      out16 (keyedChain IV128 sb128 g.1 (node S hs pk) (tblocks a (nodes S hs vs))) := by
  cases S <;> first | exact MIdeal.Hash128f.shape g pk a vs | contradiction

def blocks (a : Bytes 22) (vs : List S.Node) : List Blk :=
  let b := tblocks a (nodes S hs vs)
  b.1 :: b.2

theorem blocks_length (a : Bytes 22) (vs : List S.Node) :
    (blocks S hs a vs).length = (22+16*vs.length+8)/64+1 := by
  simp only [blocks,List.length_cons,tblocks_snd_length,nodes_length]

private theorem blocks_injective (a : Bytes 22) {xs ys : List S.Node}
    (he : blocks S hs a xs = blocks S hs a ys) : xs = ys := by
  obtain ⟨h₁,h₂⟩ := List.cons.inj he
  exact nodes_injective S hs (tblocks_injective (Prod.ext h₁ h₂)).2

abbrev Cell := St × Blk

def extract (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (xs ys : List S.Node) : Option (Cell × Cell) :=
  let st := g.1 (IV128,sb128 (node S hs pk))
  ChainScan.scan out16 g.1 st st (blocks S hs a xs) (blocks S hs a ys)

/-- Any successful fixed-arity SHA-256 Thash collision gives distinct inputs
whose compression outputs agree on the first 16 bytes. -/
theorem extract_collision (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (xs ys : List S.Node)
    (len : xs.length = ys.length) (diff : xs ≠ ys)
    (win : (tablePrimitives g S.vp.params).Thash pk a xs = (tablePrimitives g S.vp.params).Thash pk a ys) :
    ∃ u v, extract S hs g pk a xs ys = some (u,v) ∧ u ≠ v ∧ out16 (g.1 u) = out16 (g.1 v) := by
  unfold extract
  cases h : ChainScan.scan out16 g.1 _ _ (blocks S hs a xs) (blocks S hs a ys) with
  | some pair =>
    obtain ⟨u,v⟩ := pair
    exact ⟨u,v,rfl,ChainScan.scan_sound out16 _ _ _ _ _ _ _ h⟩
  | none =>
    have he := congrArg (node S hs) win
    rw [shape,shape] at he
    have eq : (blocks S hs a xs).length = (blocks S hs a ys).length := by simp only [blocks_length,len]
    have ne : blocks S hs a xs ≠ [] := List.cons_ne_nil _ _
    exact (diff (blocks_injective S hs a (ChainScan.scan_none out16 _ _ _ _ _ eq ne h he).2)).elim

private theorem read_cost (u : Cell) :
    EvalCost (fun H => (pure ((tablesOf H).1 u) : ProbComp St)) 1 :=
  EvalCost.eval (X := Input) (Y := Output) (.inl u) Prod.fst

theorem extract_cost (pk : S.Node) (a : Bytes 22) (xs ys : List S.Node) :
    EvalCost (fun H => (pure (extract S hs (tablesOf H) pk a xs ys) : ProbComp (Option (Cell × Cell))))
      (1+2*((22+16*xs.length+8)/64+1)) := by
  have h := EvalCost.bind (read_cost (IV128,sb128 (node S hs pk))) (fun st =>
    ChainScan.scan_cost out16 (fun H => (tablesOf H).1) read_cost st st (blocks S hs a xs) (blocks S hs a ys))
  simpa only [extract,pure_bind,blocks_length] using h
end Reduction.Compression.SmallClass
#print axioms Reduction.Compression.SmallClass.extract_collision
#print axioms Reduction.Compression.SmallClass.extract_cost
