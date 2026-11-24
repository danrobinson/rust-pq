import Integration.SlhDsaShakeXofRows
import Integration.SlhDsaCompressionPrf

namespace Reduction.ShakeXof
open MLink SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped Kronecker ComplexOrder

/-- A hidden key selects one column of an injectively encoded prefix slice.
The distinguisher has quantum access to every full raw XOF answer. -/
theorem column_prf {K Dm X : Type} [Fintype K] [DecidableEq K] [SampleableType K] [Nonempty K]
    [Fintype Dm] [DecidableEq Dm] [Nonempty Dm] [Fintype X] [DecidableEq X] [Nonempty X]
    {n m : ℕ} (hn : n ≤ m) (emb : K × Dm ↪ X)
    {D : Type} [DecidableEq D] (address : D → Dm) (inj : Function.Injective address)
    {E : Type} [Fintype E] [DecidableEq E]
    (A : (X → Bytes m) → QOC (WS X (Bytes m) E) (PRFScheme.PRFOracleSpec D (Bytes n)) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((X × Bytes m) × E)) :
    (∑ g, unifW _ g * qPrfRealPr (keyedScheme address (read emb hn g)) (A g)
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g, unifW _ g * qPrfIdealPr (A g)
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / Fintype.card K) := by
  let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
  have hr (g : X → Bytes m) := prf_answer_real_le_ideal_add (K := K) (Dm := Dm)
    address inj A q hA (write emb g) (locate emb) (local_at emb g) ρ
  rw [SetOracle.avg_resample (write emb) (read emb hn) (row_swap emb hn)
    (fun g => qPrfRealPr (keyedScheme address (read emb hn g)) (A g) M)]
  rw [SetOracle.avg_resample (write emb) (read emb hn) (row_swap emb hn)
    (fun g => qPrfIdealPr (A g) M)]
  simp only [read_write]
  calc _ ≤ ∑ g : X → Bytes m, unifW _ g * (_ + ENNReal.ofReal (8*(q:ℝ)^2 / Fintype.card K)) :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (hr g)
       _ = _ := by
         simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul]
         rfl

/-- The cost of a closed coherent program is preserved when a slice of the
raw table is varied, including when other encodings read the same raw input. -/
theorem slice_model {X J D E : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    [Fintype E] [DecidableEq E] {m n : ℕ} (emb : J ↪ X) (g : X → Bytes m)
    (A : (X → Bytes m) → Closed (WS X (Bytes m) E) D)
    (ρ : Matrix (WS X (Bytes m) E) (WS X (Bytes m) E) ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    ∃ M : HybridModel J (Bytes n) D q, ∀ R (Ev : D → Prop) [DecidablePred Ev],
      M.prob R Ev = qWeight Ev (A (write emb g R)) ρ := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (X × Bytes m) × E) ρ hp ht
  obtain ⟨M,hM⟩ := hq.exists_model σ
  refine ⟨M.pullback emb (write emb g) (different_at emb g), ?_⟩
  intro R Ev _
  rw [HybridModel.pullback_prob,hM,hσ]

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.column_prf
#print axioms Reduction.ShakeXof.slice_model
