import Integration.SlhDsaCompressionHmacKey

namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

variable {W R α : Type} [Fintype W]

private def embed (Q : Closed W α) : QOC W (PRFScheme.PRFOracleSpec Bool R) α :=
  simulateQ (fun t => match t with
    | .inl j => liftM ((instrSpec W + PRFScheme.PRFOracleSpec Bool R).query (.inl j))
    | .inr n => liftM ((instrSpec W + PRFScheme.PRFOracleSpec Bool R).query (.inr (.inl n)))) Q

private theorem ans_embed (f : Bool → R) (Q : Closed W α) : ansRun f (embed Q) = Q := by
  induction Q using OracleComp.inductionOn with
  | pure a => simp [embed, ansRun_pure]
  | query_bind t k ih =>
    unfold embed
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with j|n
    · rw [ansRun_instr]; exact bind_congr ih
    · rw [ansRun_unif]; exact bind_congr ih

/-- Read both key states and then run a continuation with no further key-state access. -/
private def readBoth (B : (Bool → R) → Closed W α) : QOC W (PRFScheme.PRFOracleSpec Bool R) α := do
  let i ← liftM ((instrSpec W + PRFScheme.PRFOracleSpec Bool R).query (.inr (.inr false)))
  let o ← liftM ((instrSpec W + PRFScheme.PRFOracleSpec Bool R).query (.inr (.inr true)))
  embed (B (fun b => if b then o else i))

private theorem ans_both (f : Bool → R) (B : (Bool → R) → Closed W α) :
    ansRun f (readBoth B) = B f := by
  unfold readBoth
  rw [ansRun_oracle, ansRun_oracle, ans_embed]
  exact congrArg B (funext fun b => by cases b <;> rfl)

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

/-- Run an arbitrary message-PRF distinguisher against HMAC continued from a fixed
pair of chaining states. Its access to the underlying compression port is preserved. -/
noncomputable def messageRun
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (start : Bool → Chain512) (H : Input → Output) : Closed Work Bool :=
  ansRun (fun d => wideMessage S (tablesOf H) start d.1 d.2) (A H)

/-- A message-oracle query pays for the remaining inner blocks and one outer compression. -/
def messageCharge : (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node).Domain → ℕ
  | .inl _ => 0
  | .inr (_, m) => (m.length + S.vp.params.n + 16) / 128 + 2

theorem messageRun_cost
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (q : ℕ) (hA : PUE (messageCharge S) A q) (start : Bool → Chain512) :
    PUE (spec := unifSpec) cnt0 (messageRun S A start) q := by
  let impl := fun H => statelessImpl
    ((ansScheme (fun d : S.Node × List Byte => wideMessage S (tablesOf H) start d.1 d.2)).prfRealQueryImpl ())
  apply PUE.map Prod.fst (PUE.close impl _ hA ())
  rintro (n | ⟨r,m⟩) ⟨⟩
  · exact EvalCost.const _
  · have h := (wide_message_cost S start r m).map (fun x => (x, ()))
    simp only [impl, statelessImpl, StateT.run, PRFScheme.prfRealQueryImpl_apply_inr, ansScheme, messageCharge, map_pure] at h ⊢
    kexact h

theorem wide_message_hop (hw : S.vp.params.n ≠ 16)
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (q : ℕ) (hA : PUE (messageCharge S) A q)
    (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf S.vp (randPrims (functions S g)))
      (A (oracle g)) M) ≤
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card (Bool → Chain512) : ℝ≥0∞)⁻¹ * ∑ start : Bool → Chain512,
        qWeight (· = true) (messageRun S A start (oracle g)) M)) +
      ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  intro M
  let D := fun H => readBoth (fun start => messageRun S A start H)
  have cost : PrfAnswerCost D q := by
    intro f
    simpa only [D, ans_both] using messageRun_cost S A q hA f
  have hop := wide_key_hop S D q cost ρ
  have hr (g : CompressionTables) : qPrfRealPr (wideScheme S g) (D (oracle g)) M =
      qPrfRealPr (msgPrf S.vp (randPrims (functions S g))) (A (oracle g)) M := by
    unfold qPrfRealPr qPrfRealExperiment
    congr 1
    apply bind_congr
    intro k
    change ansRun ((wideScheme S g).eval k) (readBoth _) = _
    rw [ans_both]
    unfold messageRun
    rw [tablesOf_oracle]
    have he : (fun d : S.Node × List Byte => wideMessage S g ((wideScheme S g).eval k) d.1 d.2) =
        (msgPrf S.vp (randPrims (functions S g))).eval k :=
      funext fun d => (wide_message_real S g hw k d.1 d.2).symm
    rw [he]
    rfl
  have hi (g : CompressionTables) := lazy_eq_avg (Dm := Bool) id Function.injective_id
    (· = true) (D (oracle g)) M
  change (∑ g, _ * qPrfRealPr _ _ M) ≤ (∑ g, _ * qPrfIdealPr _ M) + _ at hop
  have eq (g : CompressionTables) : qPrfIdealPr (D (oracle g)) M =
      (Fintype.card (Bool → Chain512) : ℝ≥0∞)⁻¹ * ∑ start : Bool → Chain512,
        qWeight (· = true) (messageRun S A start (oracle g)) M := by
    have e := hi g
    simp only [D, ans_both, id_eq] at e
    kexact e
  simpa only [hr, eq] using hop

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.wide_message_hop
