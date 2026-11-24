import Integration.SlhDsaCompressionWotsSmallRow
import Integration.SlhDsaCompressionWotsPhase
import Integration.SlhDsaCompressionHiddenWeightReverse
import Ideal.Realize.Phase1

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
open HiddenWeight (mean)

def family (seeds : ProbComp Node) (n : ℕ) : THFam St Blk Node (Bytes 22) Node Node Unit :=
  { FWots128T seeds with numTargets := n }

def preP (seeds : ProbComp Node) (n : ℕ) (c : Blk × List Blk → St) :=
  WotsPhase.chainPre (family seeds n) id Function.injective_id c

def tcrP (seeds : ProbComp Node) (n : ℕ) (c : Blk × List Blk → St) :=
  WotsPhase.chainTcr (family seeds n) c

noncomputable def udP (seeds : ProbComp Node) (n : ℕ) (c : Blk × List Blk → St) :=
  WotsPhase.chainUd (family seeds n) id Function.injective_id c

variable {E : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E

theorem rowModel {D : Type} (pk : Node) (cv : St) (g : CF St Blk) (h : CF Chain512 Block512) (T : Table)
    (A : (Input → Output) → Closed W D) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    ∃ M : HybridModel Idx Node D q, ∀ R (Ev : D → Prop) [DecidablePred Ev],
      M.prob R Ev = qWeight Ev (A (oracle (full pk cv g h (put T R)))) ρ := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (Input × Output) × E) ρ hp ht
  obtain ⟨M,hM⟩ := hq.exists_model σ
  refine ⟨M.pullback (emb cv) (fun R => oracle (full pk cv g h (put T R))) (localPort pk cv g h T), ?_⟩
  intro R Ev _
  rw [HybridModel.pullback_prob,hM,hσ]

theorem rowTight (pk : Node) (cv : St) (g : CF St Blk) (h : CF Chain512 Block512) (T : Table)
    (A : (Input → Output) → Closed W Bool) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    ∃ f : Row → ℝ≥0∞, Tight.TightAvgBound (fun R => (f R).toReal) q ∧
      ∀ R, f R = qWeight (· = true) (A (oracle (full pk cv g h (put T R)))) ρ := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (Input × Output) × E) ρ hp ht
  obtain ⟨x,hx,he⟩ := hq.exists_prog_qprob
  let f := fun H => qprob LocalSig.Interp.instruments H x σ (fun p => p.2 = true)
  have hb := Tight.qprob_tightAvgBound LocalSig.Interp.instruments x σ q hx (fun p => p.2 = true)
  refine ⟨fun R => f (oracle (full pk cv g h (put T R))), wq_tightAvgBound_pullback
    (fun H => (f H).toReal) q hb (emb cv) _ (localPort pk cv g h T), ?_⟩
  intro R
  exact (he (· = true) _ σ).trans (by rw [hσ])

theorem explicitMean {X : Type} [Fintype X] [SampleableType X] (f : X → ℝ≥0∞) :
    mean ($ᵗ X) f = SetOracle.uniformMean f := by
  simp only [mean,tsum_fintype,prob_uniformSample_eq,unifW,SetOracle.uniformMean]

theorem swapMean {X V : Type} [Fintype X] [Fintype V] [Nonempty V]
    [SampleableType X] [SampleableType V] (w : X → ℝ≥0∞) (put : X → V → X) (read : X → V)
    (hs : ∀ z : X × V, (put (put z.1 z.2) (read z.1), read (put z.1 z.2)) = z) :
    mean ($ᵗ X) w = mean ($ᵗ X) (fun x => mean ($ᵗ V) (fun v => w (put x v))) := by
  simp only [explicitMean]
  exact SetOracle.avg_resample put read (fun z => hs z) w

attribute [local irreducible] Wots256.read Wots256.put

theorem resample (w : Table → ℝ≥0∞) :
    mean ($ᵗ Table) w = mean ($ᵗ Table) (fun T => mean ($ᵗ Row) (fun R => w (put T R))) :=
  @swapMean Table Row _ _ _ _ _ w Wots256.put Wots256.read Wots256.swap

end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.rowModel
#print axioms Reduction.Compression.Wots256.rowTight
#print axioms Reduction.Compression.Wots256.resample
