import Integration.SlhDsaCompressionPreimage

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder Kronecker

private def leftCell : (St × Blk) ↪ Input := ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩

variable {E D : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

private theorem left_model (g : CF Chain512 Block512) (A : (Input → Output) → Closed Work D)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    ∃ M : HybridModel (St × Blk) St D q, ∀ R (ev : D → Prop) [DecidablePred ev],
      M.prob R ev = qWeight ev (A (oracle (R,g))) ρ := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (Input × Output) × E) ρ hp ht
  obtain ⟨M,hM⟩ := hq.exists_model σ
  have localPort (R T : CF St Blk) (x : Input) (hne : oracle (R,g) x ≠ oracle (T,g) x) :
      ∃ u, leftCell u = x ∧ R u ≠ T u := by
    cases x with
    | inr _ => exact False.elim (hne rfl)
    | inl u =>
      refine ⟨u,rfl,fun he => hne ?_⟩
      exact congrArg (fun v : St => (v,(0 : Fin 8 → UInt64))) he
  refine ⟨M.pullback leftCell (fun R => oracle (R,g)) localPort, ?_⟩
  intro R ev _
  rw [HybridModel.pullback_prob, hM, hσ]

/-- Preimage of a revealed independent uniform SHA-256 chaining state, with
superposition access to both shared tables and arbitrary fixed SHA-512 table. -/
theorem preimage_fixed_right (g : CF Chain512 Block512) (A : St → (Input → Output) → Closed Work D)
    (out : St → D → (St × Blk)) (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : ∀ i, PUE (spec := unifSpec) cnt0 (A i) q) :
    (∑ R : CF St Blk, ∑ i : St, (unifW _ R * unifW _ i) *
      qWeight (fun z => R (out i z) = i) (A i (oracle (R,g))) ρ) ≤
        (2*(q:ℝ≥0∞)+1)^2 / 2^256 := by
  classical
  choose M hM using fun i => left_model g (A i) ρ hp ht q (hq i)
  have h := preimage_uniform_le M out
  unfold unifW
  simpa only [hM, card_St, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Averaging also over the independent SHA-512 table preserves the bound. -/
theorem preimage_shared (A : St → (Input → Output) → Closed Work D)
    (out : St → D → (St × Blk)) (ρ : Matrix Work Work ℂ)
    (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (q : ℕ)
    (hq : ∀ i, PUE (spec := unifSpec) cnt0 (A i) q) :
    SetOracle.uniformMean (fun g : CompressionTables => SetOracle.uniformMean (fun i =>
      qWeight (fun z => g.1 (out i z) = i) (A i (oracle g)) ρ)) ≤
        (2*(q:ℝ≥0∞)+1)^2 / 2^256 := by
  classical
  unfold SetOracle.uniformMean
  rw [SetOracle.avg_resample (fun (g : CompressionTables) r => (r,g.2)) Prod.fst
    (fun _ => rfl)]
  calc
    _ ≤ ∑ g : CompressionTables, unifW _ g * ((2*(q:ℝ≥0∞)+1)^2 / 2^256) := by
      apply Finset.sum_le_sum
      intro g _
      apply mul_le_mul' le_rfl
      simpa only [Finset.mul_sum, mul_assoc] using preimage_fixed_right g.2 A out ρ hp ht q hq
    _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]


/-- Finding a preimage of a fixed SHA-256 chaining state with access to both
compression tables, including the public initial state used by the message hash. -/
theorem fixed_state_shared (A : (Input → Output) → Closed Work D) (out : D → (St × Blk))
    (t : St) (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (q : ℕ)
    (hq : PUE (spec := unifSpec) cnt0 A q) :
    SetOracle.uniformMean (fun g : CompressionTables =>
      qWeight (fun z => g.1 (out z) = t) (A (oracle g)) ρ) ≤ (2*(q:ℝ≥0∞)+1)^2 / 2^256 := by
  classical
  unfold SetOracle.uniformMean
  rw [SetOracle.avg_resample (fun (g : CompressionTables) r => (r,g.2)) Prod.fst (fun _ => rfl)]
  calc
    _ ≤ ∑ g : CompressionTables, unifW _ g * ((2*(q:ℝ≥0∞)+1)^2 / 2^256) := by
      apply Finset.sum_le_sum
      intro g _
      apply mul_le_mul' le_rfl
      obtain ⟨M,hM⟩ := left_model g.2 A ρ hp ht q hq
      simpa only [hM, card_St, Nat.cast_pow, Nat.cast_ofNat] using preimage_constant M out t
    _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.preimage_fixed_right
#print axioms Reduction.Compression.Hmac256.preimage_shared
#print axioms Reduction.Compression.Hmac256.fixed_state_shared
