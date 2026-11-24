import Integration.SlhDsaCompressionWotsSmallGame

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open HiddenWeight (mean)
variable {σ : Type}
theorem mean_cap {A : Type} (p : ProbComp A) (f : A → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ a, f a ≤ c) :
    mean p f ≤ c := by
  refine (HiddenWeight.mean_mono p h).trans ?_
  unfold mean
  rw [ENNReal.tsum_mul_right]
  exact (mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans_eq (one_mul c)

noncomputable def phaseLoss (C L : ℕ) : ℝ≥0∞ :=
  ((C*(1+2*L)+1 : ℕ) : ℝ≥0∞) / 2^256

theorem phase_hop (seeds : ProbComp Node) (P : OracleComp (gS St Blk) σ)
    (w : Node → CF St Blk → σ → ℝ≥0∞) (hw : ∀ pk g s, w pk g s ≤ 1)
    (C L : ℕ) (h0 : IsQueryBoundP P (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP P (fun i => isChain i = true) C) (hL : AllQueriesSatisfy P (chainLenLe L))
    (b : ℝ≥0∞) (hr : ∀ pk cv g T, mean ($ᵗ Row) (fun R =>
       mean (simulateQ (ans₁ g (chainI g (put T R))) P) (w pk (gstar IV128 (sb128 pk) cv g (put T R)))) ≤ b) :
    mean seeds (fun pk => mean ($ᵗ (CF St Blk)) (fun g =>
      mean (simulateQ (ans₁ g (keyedChain IV128 sb128 g pk)) P) (w pk g))) ≤ b + phaseLoss C L := by
  have hop := HiddenWeight.hiddenPrefix IV128 sb128 P seeds sb128_injective 1
    (fun _ => prEvent_le_one _) 0 C L h0 hC hL w hw
  apply hop.trans (add_le_add ?_ ?_)
  · apply mean_cap; intro pk
    apply mean_cap; intro cv
    apply mean_cap; intro g
    rw [resample]
    exact mean_cap _ _ b (hr pk cv g)
  · simp only [Nat.cast_zero,zero_mul,zero_add,phaseLoss,div_eq_mul_inv]
    rw [card_St]
    norm_num

end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.phase_hop
