import Integration.SlhDsaCompressionSearch
import PQ.QROM.Preimage

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder Kronecker

private def rightCell : HmacKey.InputCell ↪ Input := ⟨Sum.inr, fun _ _ h => Sum.inr.inj h⟩

variable {E D : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

private theorem right_model (g : CF St Blk) (A : (Input → Output) → Closed Work D)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    ∃ M : HybridModel HmacKey.InputCell Chain512 D q, ∀ R (ev : D → Prop) [DecidablePred ev],
      M.prob R ev = qWeight ev (A (oracle (g,R))) ρ := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (Input × Output) × E) ρ hp ht
  obtain ⟨M,hM⟩ := hq.exists_model σ
  have localPort (R T : CF Chain512 Block512) (x : Input) (hne : oracle (g,R) x ≠ oracle (g,T) x) :
      ∃ u, rightCell u = x ∧ R u ≠ T u := by
    cases x with
    | inl x => exact (hne rfl).elim
    | inr u =>
      refine ⟨u,rfl,fun he => hne ?_⟩
      exact congrArg (fun v : Chain512 => ((0 : St), arrayVectorEquivFin UInt64 8 v)) he
  refine ⟨M.pullback rightCell (fun R => oracle (g,R)) localPort, ?_⟩
  intro R ev _
  rw [HybridModel.pullback_prob, hM, hσ]

/-- Preimage of a revealed independent uniform SHA-512 chaining state, with
superposition access to both shared tables and arbitrary fixed SHA-256 table. -/
theorem preimage_fixed_left (g : CF St Blk) (A : Chain512 → (Input → Output) → Closed Work D)
    (out : Chain512 → D → HmacKey.InputCell) (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : ∀ i, PUE (spec := unifSpec) cnt0 (A i) q) :
    (∑ R : CF Chain512 Block512, ∑ i : Chain512, (unifW _ R * unifW _ i) *
      qWeight (fun z => R (out i z) = i) (A i (oracle (g,R))) ρ) ≤
        (2*(q:ℝ≥0∞)+1)^2 / 2^512 := by
  classical
  choose M hM using fun i => right_model g (A i) ρ hp ht q (hq i)
  let _ : AddCommGroup Chain512 := (arrayVectorEquivFin UInt64 8).addCommGroup
  have h := preimage_uniform_le M out
  unfold unifW
  simpa only [hM, MIdeal.Sha512.card_chain512, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Averaging also over the independent SHA-256 table preserves the bound. -/
theorem preimage_shared (A : Chain512 → (Input → Output) → Closed Work D)
    (out : Chain512 → D → HmacKey.InputCell) (ρ : Matrix Work Work ℂ)
    (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (q : ℕ)
    (hq : ∀ i, PUE (spec := unifSpec) cnt0 (A i) q) :
    SetOracle.uniformMean (fun g : CompressionTables => SetOracle.uniformMean (fun i =>
      qWeight (fun z => g.2 (out i z) = i) (A i (oracle g)) ρ)) ≤
        (2*(q:ℝ≥0∞)+1)^2 / 2^512 := by
  classical
  unfold SetOracle.uniformMean
  rw [SetOracle.avg_resample (fun (g : CompressionTables) r => (g.1,r)) Prod.snd
    (fun _ => rfl)]
  calc
    _ ≤ ∑ g : CompressionTables, unifW _ g * ((2*(q:ℝ≥0∞)+1)^2 / 2^512) := by
      apply Finset.sum_le_sum
      intro g _
      apply mul_le_mul' le_rfl
      simpa only [Finset.mul_sum, mul_assoc] using preimage_fixed_left g.1 A out ρ hp ht q hq
    _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]

end Reduction.Compression
#print axioms Reduction.Compression.preimage_fixed_left
#print axioms Reduction.Compression.preimage_shared
