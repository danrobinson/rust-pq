import Integration.SlhDsaCompressionPrf

set_option maxRecDepth 8192
namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
variable (S : Sha2Set)

abbrev SingletonRow := Bytes 22 × S.Node → S.Node

private def rowCell (cv : St) (x : Bytes 22 × S.Node) : St × Blk :=
  location S (x.2,cv,x.1)

private theorem rowCell_inj (cv : St) : Function.Injective (rowCell S cv) := by
  intro x y h
  obtain ⟨hk,hs⟩ := Prod.mk.inj (location_injective S h)
  exact Prod.ext (Prod.mk.inj hs).2 hk

def seedState (g : CompressionTables) (pk : S.Node) := g.1 (IV128,MIdeal.SkPrf.seedBlock S pk)

private noncomputable def indexAt (cv : St) (i : St × Blk) : Option (Bytes 22 × S.Node) := by
  classical
  exact if h : ∃ x, rowCell S cv x = i then some h.choose else none

private theorem index_cell (cv : St) (x : Bytes 22 × S.Node) :
    indexAt S cv (rowCell S cv x) = some x := by
  classical
  unfold indexAt
  rw [dite_eq_left (show ∃ y, rowCell S cv y = rowCell S cv x from ⟨x,rfl⟩)]
  congr 1
  exact rowCell_inj S cv (Exists.choose_spec (show ∃ y, rowCell S cv y = rowCell S cv x from ⟨x,rfl⟩))

private theorem index_spec (cv : St) (i : St × Blk) (x : Bytes 22 × S.Node)
    (h : indexAt S cv i = some x) : rowCell S cv x = i := by
  classical
  unfold indexAt at h
  split_ifs at h with he
  · exact Option.some.inj h ▸ he.choose_spec

def readSingleton (g : CompressionTables) (pk : S.Node) : SingletonRow S :=
  fun x => MIdeal.SkPrf.output S (g.1 (rowCell S (seedState S g pk) x))

noncomputable def replaceSingleton (pk : S.Node) (g : CompressionTables) (r : SingletonRow S) : CompressionTables :=
  (fun i => (indexAt S (seedState S g pk) i).elim (g.1 i) (fun x => setPrefix S (g.1 i) (r x)), g.2)

private theorem replace_fst (pk : S.Node) (g : CompressionTables) (r : SingletonRow S) (i : St × Blk) :
    (replaceSingleton S pk g r).1 i = (indexAt S (seedState S g pk) i).elim (g.1 i) (fun x => setPrefix S (g.1 i) (r x)) := rfl

private theorem seed_replace (pk : S.Node) (g : CompressionTables) (r : SingletonRow S) :
    seedState S (replaceSingleton S pk g r) pk = seedState S g pk := by
  have h : indexAt S (seedState S g pk) (IV128,MIdeal.SkPrf.seedBlock S pk) = none := by
    cases he : indexAt S _ _ with
    | none => rfl
    | some x =>
      have h := congrArg Prod.snd (index_spec S _ _ _ he)
      exact (MIdeal.SkPrf.seed_ne_singleton S pk x.1 x.2 h.symm).elim
  unfold seedState
  rw [replace_fst, h]; rfl

theorem read_replaced (pk : S.Node) (g : CompressionTables) (r : SingletonRow S) :
    readSingleton S (replaceSingleton S pk g r) pk = r := by
  funext x
  unfold readSingleton
  rw [seed_replace]
  rw [replace_fst, index_cell]
  apply read_prefix

theorem swap_singleton (pk : S.Node) : Function.Involutive (fun z : CompressionTables × SingletonRow S =>
    (replaceSingleton S pk z.1 z.2,readSingleton S z.1 pk)) := by
  rintro ⟨g,r⟩
  refine Prod.ext (Prod.ext ?_ rfl) (read_replaced S pk g r)
  funext i
  change (replaceSingleton S pk (replaceSingleton S pk g r) (readSingleton S g pk)).1 i = g.1 i
  rw [replace_fst, seed_replace]
  cases e : indexAt S (seedState S g pk) i with
  | none =>
    simp only [Option.elim_none, replace_fst, e]
  | some x =>
    obtain rfl := index_spec S _ _ x e
    simp only [Option.elim_some, replace_fst, e, readSingleton, undo_prefix]

/-- Resampling every truncated singleton output at a fixed public seed preserves
the joint uniform distribution of the two compression tables. -/
theorem average_singleton (pk : S.Node) (f : CompressionTables → ℝ≥0∞) :
    (∑ g, unifW _ g * f g) = ∑ g, unifW _ g * ∑ r : SingletonRow S, unifW _ r * f (replaceSingleton S pk g r) :=
  SetOracle.avg_resample (replaceSingleton S pk) (fun g => readSingleton S g pk) (swap_singleton S pk) f

def singletonEmbedding (g : CompressionTables) (pk : S.Node) : (Bytes 22 × S.Node) ↪ Input :=
  ⟨fun x => .inl (rowCell S (seedState S g pk) x), fun _ _ e => rowCell_inj S _ (Sum.inl.inj e)⟩

theorem singleton_local (g : CompressionTables) (pk : S.Node) (r t : SingletonRow S) (x : Input)
    (h : oracle (replaceSingleton S pk g r) x ≠ oracle (replaceSingleton S pk g t) x) :
    ∃ a, singletonEmbedding S g pk a = x ∧ r a ≠ t a := by
  cases x with
  | inr i =>
    have hs (v : SingletonRow S) : oracle (replaceSingleton S pk g v) (.inr i) = oracle g (.inr i) := rfl
    exact (h ((hs r).trans (hs t).symm)).elim
  | inl i =>
    cases e : indexAt S (seedState S g pk) i with
    | none => exact (h (by simp only [oracle,replace_fst,e,Option.elim_none,Option.elim_some])).elim
    | some a =>
      exact ⟨a, congrArg Sum.inl (index_spec S _ _ a e), fun eq => h (by simp only [oracle,replace_fst,e,Option.elim_none,Option.elim_some,eq])⟩

theorem singleton_eval (g : CompressionTables) (pk : S.Node) (t : Bytes 22) (m : S.Node) :
    (tablePrimitives g S.vp.params).Thash pk t [m] = readSingleton S g pk (t,m) := by
  apply Eq.trans _ (MIdeal.SkPrf.singleton_shape S g.1 pk t m)
  change sha2ThashMixed (liftC g.1) (lift512 g.2) S.vp.params pk t [m] = _
  simp only [sha2ThashMixed, sha2ThashG, List.length_cons, List.length_nil, ite_true]
end Reduction.Compression

#print axioms Reduction.Compression.average_singleton
#print axioms Reduction.Compression.singleton_local
