import Integration.SlhDsaShakeXofRepeated

namespace Reduction.ShakeXof
open PQ.QROM Quantum ENNReal Finset MeasureTheory
universe u v w
variable {K X Y : Type} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u,v}} {W : QReg → Type w} {A : QReg}

/-- In a run independent of the hidden key, the sum over keys of their
inclusion probabilities is bounded by the maximum output list size. -/
private theorem list_sum (I : L.Interp) (G : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (out : (Σ a, W a) → Finset K) (t : ℕ) (size : ∀ p, (out p).card ≤ t) :
    (∑ k, qprob I G x ρ (fun p => k ∈ out p)) ≤ t := by
  classical
  simp only [qprob_eq_tsum]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  let wt := fun p => ENNReal.ofReal ((additiveOracleRuntime G).jointPost I x ρ p).matrix.trace.re
  calc
    _ ≤ ∑' p, wt p * (t:ℝ≥0∞) := by
      apply tsum_le_tsum
      intro p
      dsimp only
      rw [← Finset.mul_sum]
      apply mul_le_mul' le_rfl
      calc
        _ = ((out p).card:ℝ≥0∞) := by
          simp [Set.indicator]
        _ ≤ _ := Nat.cast_le.mpr (size p)
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' (tsum_jointPost_trace_le_one I G x ρ) le_rfl).trans_eq (one_mul _)

/-- A q-query quantum program reports at most t candidate keys. With a
uniform hidden key k and an oracle changed only on its row, the probability
that the report contains k is at most (sqrt(t)+2q)^2 / |K|. In a mixed-query
hybrid the report can record the raw rows accessed by classical honest calls
answered from the fixed table G. This theorem concerns that hybrid's hit
event. -/
theorem hidden_row_list_bound (I : L.Interp) (G : X → Y) (row : X → K)
    (H : K → X → Y) (outside : ∀ k z, row z ≠ k → H k z = G z)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (q : ℕ) (cost : QueryBounded x q)
    (out : (Σ a, W a) → Finset K) (t : ℕ) (size : ∀ p, (out p).card ≤ t) :
    (∑ k, qprob I (H k) x ρ (fun p => k ∈ out p)) / Fintype.card K ≤
      ((t:ℝ≥0∞)^(2⁻¹:ℝ)+2*q)^2 / Fintype.card K := by
  classical
  let M := HybridModel.ofProgram I x ρ q cost out
  let fiber := fun k : K => Finset.univ.filter (fun z => row z = k)
  have same : ∀ k, Finset.univ.filter (fun z => H k z ≠ G z) ⊆ fiber k := by
    intro k z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,not_not.mp (fun ne => (Finset.mem_filter.mp hz).2 (outside k z ne))⟩
  have hb := sqrt_sum_le (fun _ : K => 1) _ _ _ (fun k =>
    (M.hybrid (H k) G (fun l => k ∈ l)).trans (add_le_add le_rfl
      (sqrt_le_sqrt (mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset (f := M.mass G) (same k))))))
  simp only [one_mul] at hb
  have mass : (∑ k, 4*(q:ℝ≥0∞)*∑ z ∈ fiber k, M.mass G z) ≤ 4*q*(q:ℝ≥0∞) := by
    rw [← Finset.mul_sum]
    unfold fiber
    rw [Finset.sum_fiberwise]
    exact mul_le_mul' le_rfl (M.mass_sum_le _)
  have root : (4*(q:ℝ≥0∞)*q)^(2⁻¹:ℝ) = 2*q := by
    rw [show 4*(q:ℝ≥0∞)*q = (2*q)^2 by ring,← ENNReal.rpow_natCast_mul]
    norm_num
  have h := hb.trans (add_le_add (sqrt_le_sqrt (list_sum I G x ρ out t size))
    ((sqrt_le_sqrt mass).trans_eq root))
  apply ENNReal.div_le_div_right
  simpa only [sq_sqrt, M, HybridModel.ofProgram_prob] using pow_le_pow_left' h 2


open MLink SLHDSA
set_option exponentiation.threshold 2048

/-- For either keyed SHAKE slice, a coherent program observes the base table
with one hidden PRF row overwritten. The reported candidate keys may depend
on the complete measured transcript. -/
theorem column_list_bound (S : Sha2Set) {Dm : Type} {N : ℕ}
    (emb : S.Node × Dm ↪ ShakeApi.Input N)
    (g : ShakeApi.RawTable S N) (r : S.Node × Dm → S.Node) (f : Dm → S.Node)
    (I : L.Interp) (x : QuantumComp L (qromSpec (ShakeApi.Input N) (Bytes S.vp.params.m)) W A)
    (ρ : SubState A) (q t : ℕ) (cost : QueryBounded x q)
    (out : (Σ a, W a) → Finset S.Node) (size : ∀ p, (out p).card ≤ t) :
    (∑ k, qprob I (write emb g (prfSwapRow k r f)) x ρ (fun p => k ∈ out p)) /
      Fintype.card S.Node ≤ ((t:ℝ≥0∞)^(2⁻¹:ℝ)+2*q)^2 / 2^(8*S.vp.params.n) := by
  classical
  let row := fun z => ((locate emb z).map Prod.fst).getD default
  have off (k : S.Node) (z : ShakeApi.Input N) (hz : row z ≠ k) :
      write emb g (prfSwapRow k r f) z = write emb g r z := by
    apply local_at
    intro j hj
    have ne : j.1 ≠ k := by simpa [row,hj] using hz
    simp [prfSwapRow,ne]
  have h := hidden_row_list_bound I (write emb g r) row _ off x ρ q cost out t size
  have card : Fintype.card S.Node = 2^(8*S.vp.params.n) := by
    rw [card_bytes', pow_mul]
    norm_num
  simpa only [card,Nat.cast_pow,Nat.cast_ofNat] using h

/-- At the full signing budget of either 128-bit set the numerical hidden-row
hit error is at most 2^-42 (128s) or 2^-44 (128f), even if every honest raw
evaluation places one candidate key in the report. -/
theorem column_list_lifetime_128 (S : Sha2Set) (width : S.vp.params.n = 16)
    {Dm : Type} {N : ℕ} (emb : S.Node × Dm ↪ ShakeApi.Input N)
    (g : ShakeApi.RawTable S N) (r : S.Node × Dm → S.Node) (f : Dm → S.Node)
    (I : L.Interp) (x : QuantumComp L (qromSpec (ShakeApi.Input N) (Bytes S.vp.params.m)) W A)
    (ρ : SubState A) (cost : QueryBounded x (2^40))
    (out : (Σ a, W a) → Finset S.Node) (size : ∀ p, (out p).card ≤
      max (ShakeApi.Sk.budget S 0 (2^64)) (ShakeApi.Msg.budget S 0 (2^64))) :
    (∑ k, qprob I (write emb g (prfSwapRow k r f)) x ρ (fun p => k ∈ out p)) /
      Fintype.card S.Node ≤ ((2:ℝ≥0∞)^(if S = .s128s then 42 else 44))⁻¹ := by
  let t := max (ShakeApi.Sk.budget S 0 (2^64)) (ShakeApi.Msg.budget S 0 (2^64))
  let u : ℕ := if S = .s128s then 2^43-2^41 else 2^42-2^41
  have htu : t ≤ u^2 := by cases S <;> revert width <;> decide +kernel
  have le : (t:ℝ≥0∞)^(2⁻¹:ℝ) ≤ (u:ℝ≥0∞) := by
    have h : (t:ℝ≥0∞) ≤ (u:ℝ≥0∞)^2 := by exact_mod_cast htu
    have z := sqrt_le_sqrt h
    rw [← ENNReal.rpow_natCast_mul] at z
    norm_num at z
    simpa only [one_div] using z
  have b := column_list_bound S emb g r f I x ρ (2^40) t cost out size
  refine b.trans ((ENNReal.div_le_div_right (pow_le_pow_left' (add_le_add le le_rfl) 2) _).trans ?_)
  rw [width]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  split_ifs <;> norm_num [u, *, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.hidden_row_list_bound
#print axioms Reduction.ShakeXof.column_list_lifetime_128
