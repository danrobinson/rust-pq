import Integration.SlhDsaComposedClosedNum

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum Reduction
open scoped ComplexOrder

namespace Audit

/-- Caps: Thash lists up to 35, messages with |M|+|ctx|+2 ≤ 2. -/
def c0 : Caps := ⟨35, 2⟩

abbrev X0 := EncX c0
abbrev Spec0 := portSpec + (unifSpec + ((List Byte × List Byte) →ₒ Option (List Byte)))

noncomputable def w0 : WS X0 EncY Unit :=
  (((Sum.inl (default, default, (⟨⟨0, by omega⟩, Fin.elim0⟩ : BList (Bytes 16) 35)), default), ()), ())

noncomputable def ρ0 : Matrix (WS X0 EncY Unit) (WS X0 EncY Unit) ℂ :=
  Matrix.diagonal fun w ↦ if w = w0 then 1 else 0

lemma ρ0_psd : ρ0.PosSemidef := by
  unfold ρ0
  refine Matrix.PosSemidef.diagonal ?_
  intro w
  show (0 : ℂ) ≤ if w = w0 then 1 else 0
  split_ifs <;> simp

lemma ρ0_tr : ρ0.trace = 1 := by
  unfold ρ0
  rw [Matrix.trace_diagonal]
  simp

/-- One port call, one signing query on `([], [])`, output `(([], []), σ)`. -/
noncomputable def F1 : PortForger X0 EncY Unit where
  main _ := do
    let _ ← (liftM ((instrSpec ((X0 × EncY) × Unit) + Spec0).query (Sum.inr (Sum.inl ()))) :
      QOC ((X0 × EncY) × Unit) Spec0 Unit)
    let σ ← (liftM ((instrSpec ((X0 × EncY) × Unit) + Spec0).query
      (Sum.inr (Sum.inr (Sum.inr ([], []))))) : QOC ((X0 × EncY) × Unit) Spec0 (Option (List Byte)))
    pure (([], []), σ)
  ρ₀ := ρ0
  posSemidef := ρ0_psd
  trace_eq_one := ρ0_tr

lemma F1_hq (pk : List Byte) : CountBound isPort (F1.main pk) 1 := by
  simp only [F1]
  rw [countBound_query_bind]
  simp only [isPort, ite_true]
  refine ⟨by norm_num, fun _ ↦ ?_⟩
  rw [countBound_query_bind]
  simp only [isPort]
  exact fun _ ↦ trivial

lemma F1_hqs (pk : List Byte) : CountBound isSign (F1.main pk) 1 := by
  simp only [F1]
  rw [countBound_query_bind]
  simp only [isSign]
  intro _
  rw [countBound_query_bind]
  simp only [isSign, ite_true]
  exact ⟨by norm_num, fun _ ↦ trivial⟩

lemma F1_hcap (pk : List Byte) : AllQueries (capIdx c0) (capOut c0) (F1.main pk) := by
  refine ⟨trivial, fun _ ↦ ⟨?_, fun _ ↦ ?_⟩⟩
  · show 0 + 0 + 2 ≤ 2; rfl
  · show 0 + 0 + 2 ≤ 2; rfl

variable (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

theorem F1_suf :
    avΩ c0 (fun ω ↦ qStrongUnforgeableAdvantage (F1.at (encΩ ω) (algΩ c0 optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal 1 1 (openCounts128s 1).noPrfMsg :=
  slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed c0 optRand₀ pkSeedDist₀ F1 1 1
    F1_hq F1_hqs F1_hcap (by decide)

theorem F1_euf :
    avΩ c0 (fun ω ↦ qUnforgeableAdvantage (F1.at (encΩ ω) (algΩ c0 optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal 1 1 (openCounts128s 1).noPrfMsg :=
  slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed c0 optRand₀ pkSeedDist₀ F1 1 1
    F1_hq F1_hqs F1_hcap (by decide)

/-- Monotonicity in the budgets: a forger with 1 call also satisfies the 2^40/2^20 hypotheses. -/
lemma countBound_mono {κ α : Type} {sp : OracleSpec κ} (p : κ → Prop) [DecidablePred p]
    (P : OracleComp sp α) {a b : ℕ} (hab : a ≤ b) (h : CountBound p P a) : CountBound p P b := by
  induction P using OracleComp.inductionOn generalizing a b with
  | pure x => trivial
  | query_bind t k ih =>
    rw [countBound_query_bind] at h ⊢
    split_ifs at h ⊢ with ht
    · exact ⟨by omega, fun r ↦ ih r (by omega) (h.2 r)⟩
    · exact fun r ↦ ih r hab (h r)

theorem F1_suf_num :
    avΩ c0 (fun ω ↦ qStrongUnforgeableAdvantage (F1.at (encΩ ω) (algΩ c0 optRand₀ pkSeedDist₀ ω))) ≤
      ((2 : ℝ≥0∞) ^ 22)⁻¹ :=
  slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed_num c0 optRand₀ pkSeedDist₀ F1
    (fun pk ↦ countBound_mono _ _ (by norm_num) (F1_hq pk))
    (fun pk ↦ countBound_mono _ _ (by norm_num) (F1_hqs pk)) F1_hcap (by decide)

end Audit

#print axioms Audit.F1_suf
#print axioms Audit.F1_euf
#print axioms Audit.F1_suf_num
