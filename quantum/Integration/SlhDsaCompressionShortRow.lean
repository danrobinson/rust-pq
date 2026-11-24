import Integration.SlhDsaCompressionShortBlocks

namespace Reduction.Compression.ShortBlocks
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open Wots256 (Table Node write16 full)
open scoped ComplexOrder
abbrev Idx (ar : ℕ) := Bytes 22 × Msg ar
abbrev Row (ar : ℕ) := Idx ar → Node

private noncomputable def locate {ar : ℕ} (b : Blk) : Option (Idx ar) := by
  classical
  exact if h : ∃ x : Idx ar, block x = b then some h.choose else none

private theorem locate_block {ar : ℕ} (ha : ar ≤ 2) (x : Idx ar) : locate (block x) = some x := by
  classical
  unfold locate
  rw [dite_eq_left (show ∃ y : Idx ar, block y = block x from ⟨x,rfl⟩)]
  congr 1
  exact injective ha (Exists.choose_spec (show ∃ y : Idx ar, block y = block x from ⟨x,rfl⟩))

private theorem locate_spec {ar : ℕ} (b : Blk) (x : Idx ar) (h : locate b = some x) : block x = b := by
  classical
  unfold locate at h
  split_ifs at h with he
  exact Option.some.inj h ▸ he.choose_spec

def read (ar : ℕ) (T : Table) : Row ar := fun x => out16 (T (block x))
noncomputable def put {ar : ℕ} (T : Table) (R : Row ar) (b : Blk) : St :=
  (locate b).elim (T b) (fun x => write16 (T b) (R x))

private theorem read_put {ar : ℕ} (ha : ar ≤ 2) (T : Table) (R : Row ar) : read ar (put T R) = R := by
  funext x
  simp only [read,put,locate_block ha,Option.elim_some]
  exact Wots256.wr _ _

private theorem swap {ar : ℕ} (ha : ar ≤ 2) (z : Table × Row ar) :
    (put (put z.1 z.2) (read ar z.1),read ar (put z.1 z.2)) = z := by
  rcases z with ⟨T,R⟩
  refine Prod.ext (funext fun b => ?_) (read_put ha ..)
  unfold put
  cases he : locate (ar := ar) b with
  | none => simp only [he,Option.elim_none]
  | some x =>
    simp only [he,Option.elim_some,read]
    rw [locate_spec b x he]
    exact Wots256.undo _ _

attribute [local irreducible] put tblocks out16
local instance (ar : ℕ) : Fintype (Msg ar) := inferInstanceAs (Fintype (List.Vector Node ar))
theorem resample {ar : ℕ} (ha : ar ≤ 2) (w : Table → ℝ≥0∞) :
    HiddenWeight.mean ($ᵗ Table) w = HiddenWeight.mean ($ᵗ Table) (fun T => HiddenWeight.mean ($ᵗ (Row ar)) (fun R => w (put T R))) :=
  @Wots256.swapMean Table (Row ar) _ _ _ _ _ w put (read ar) (swap ha)

theorem leaf {ar : ℕ} (ha : ar ≤ 2) (g : CF St Blk) (T : Table) (R : Row ar) (a : Bytes 22) (m : Msg ar) :
    Wots256.collection g (put T R) a m.val = R (a,m) :=
  (congrArg out16 (Wots256.single g (put T R) (tblocks a m.val) (noTail ha a m))).trans (congrFun (read_put ha T R) (a,m))

theorem publicLeaf {ar : ℕ} (ha : ar ≤ 2) (pk : Node) (cv : St) (g : CF St Blk) (T : Table) (R : Row ar)
    (a : Bytes 22) (m : Msg ar) :
    out16 (keyedChain IV128 sb128 (gstar IV128 (sb128 pk) cv g (put T R)) pk (tblocks a m.val)) = R (a,m) :=
  (congrArg out16 (Wots256.keyed_one IV128 sb128 pk cv g (put T R) (tblocks a m.val) (seed_ne ha pk a m) (noTail ha a m))).trans
    (congrFun (read_put ha T R) (a,m))

theorem localCollection {ar : ℕ} (g : CF St Blk) (T : Table) (R U : Row ar) (a : Bytes 22) (xs : List Node)
    (ha : ∀ m, R (a,m) = U (a,m)) : Wots256.collection g (put T R) a xs = Wots256.collection g (put T U) a xs := by
  have e : put T R (tblocks a xs).1 = put T U (tblocks a xs).1 := by
    unfold put
    cases hi : locate (ar := ar) (tblocks a xs).1 with
    | none => simp only [Option.elim_none]
    | some x =>
      have had : x.1 = a := (btw128_tblocks x.1 x.2.val).symm.trans
        ((congrArg btw128 (locate_spec _ _ hi)).trans (btw128_tblocks a xs))
      have he : R x = U x := by simpa only [← had] using ha x.2
      simp only [Option.elim_some,he]
  exact congrArg (fun s => out16 (mdFold g s (tblocks a xs).2)) e

private theorem diff {ar : ℕ} (T : Table) (R U : Row ar) (b : Blk) (h : put T R b ≠ put T U b) :
    ∃ j, block j = b ∧ R j ≠ U j := by
  unfold put at h
  cases he : locate (ar := ar) b with
  | none => simp only [he,Option.elim_none] at h; exact (h rfl).elim
  | some j =>
    refine ⟨j,locate_spec _ _ he,fun eq => h ?_⟩
    simp only [he,Option.elim_some,eq]

def emb {ar : ℕ} (ha : ar ≤ 2) (cv : St) : Idx ar ↪ Input :=
  ⟨fun x => .inl (cv,block x), fun _ _ e => injective ha (congrArg Prod.snd (Sum.inl.inj e))⟩

theorem localPort {ar : ℕ} (ha : ar ≤ 2) (pk : Node) (cv : St) (g : CF St Blk) (h : CF Chain512 Block512)
    (T : Table) (R U : Row ar) (x : Input)
    (hn : oracle (full pk cv g h (put T R)) x ≠ oracle (full pk cv g h (put T U)) x) :
    ∃ j, emb ha cv j = x ∧ R j ≠ U j := by
  rw [Wots256.port_eq,Wots256.port_eq] at hn
  apply Wots256.portLocal (fun j : Idx ar => (cv,block j)) (fun j => R j ≠ U j) _ _ _ _ _ x hn
  rintro ⟨c,b⟩ hd
  obtain ⟨hc,nh⟩ := Wots256.atRow IV128 cv (sb128 pk) g (put T R) (put T U) c b hd
  obtain ⟨j,hj,hh⟩ := diff T R U b nh
  exact ⟨j,Prod.ext hc.symm hj,hh⟩

theorem model {ar : ℕ} (ha : ar ≤ 2) {D E : Type} [Fintype E] [DecidableEq E] (pk : Node) (cv : St) (g : CF St Blk)
    (h : CF Chain512 Block512) (T : Table) (A : (Input → Output) → Closed (WS Input Output E) D)
    (ρ : Matrix (WS Input Output E) (WS Input Output E) ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    ∃ M : HybridModel (Idx ar) Node D q, ∀ R (Ev : D → Prop) [DecidablePred Ev],
      M.prob R Ev = qWeight Ev (A (oracle (full pk cv g h (put T R)))) ρ := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (Input × Output) × E) ρ hp ht
  obtain ⟨M,hM⟩ := hq.exists_model σ
  refine ⟨M.pullback (emb ha cv) (fun R => oracle (full pk cv g h (put T R))) (localPort ha pk cv g h T), ?_⟩
  intro R Ev _
  rw [HybridModel.pullback_prob,hM,hσ]

end Reduction.Compression.ShortBlocks
#print axioms Reduction.Compression.ShortBlocks.resample
#print axioms Reduction.Compression.ShortBlocks.model
#print axioms Reduction.Compression.ShortBlocks.publicLeaf
