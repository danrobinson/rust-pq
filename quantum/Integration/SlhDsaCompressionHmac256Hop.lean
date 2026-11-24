import Integration.SlhDsaCompressionHmac256Key

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

open HmacKey (readBoth ans_both)
variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

/-- Run an arbitrary message-PRF distinguisher against HMAC continued from a fixed
pair of chaining states. Its access to the underlying compression port is preserved. -/
noncomputable def messageRun
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (start : Bool → St) (H : Input → Output) : Closed Work Bool :=
  ansRun (fun d => message (tablesOf H) start d.1 d.2) (A H)

/-- A message-oracle query pays for the remaining inner blocks and one outer compression. -/
def messageCharge : (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)).Domain → ℕ
  | .inl _ => 0
  | .inr (_, m) => (m.length + 24) / 64 + 2

theorem messageRun_cost
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (q : ℕ) (hA : PUE (messageCharge) A q) (start : Bool → St) :
    PUE (spec := unifSpec) cnt0 (messageRun A start) q := by
  let impl := fun H => statelessImpl
    ((ansScheme (fun d : (Bytes 16) × List Byte => message (tablesOf H) start d.1 d.2)).prfRealQueryImpl ())
  apply PUE.map Prod.fst (PUE.close impl _ hA ())
  rintro (n | ⟨r,m⟩) ⟨⟩
  · exact EvalCost.const _
  · have h := (message_cost start r m).map (fun x => (x, ()))
    simp only [impl, statelessImpl, StateT.run, PRFScheme.prfRealQueryImpl_apply_inr, ansScheme, messageCharge, map_pure] at h ⊢
    kexact h

theorem message_hop
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (q : ℕ) (hA : PUE (messageCharge) A q)
    (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf Sha2Set.s128s.vp (randPrims (functions Sha2Set.s128s g)))
      (A (oracle g)) M) ≤
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card (Bool → St) : ℝ≥0∞)⁻¹ * ∑ start : Bool → St,
        qWeight (· = true) (messageRun A start (oracle g)) M)) +
      ENNReal.ofReal (8*(q:ℝ)^2 / 2^128) := by
  intro M
  let D := fun H => readBoth (fun start => messageRun A start H)
  have cost : PrfAnswerCost D q := by
    intro f
    simpa only [D, ans_both] using messageRun_cost A q hA f
  have hop := key_hop D q cost ρ
  have hr (g : CompressionTables) : qPrfRealPr (keyScheme g) (D (oracle g)) M =
      qPrfRealPr (msgPrf Sha2Set.s128s.vp (randPrims (functions Sha2Set.s128s g))) (A (oracle g)) M := by
    unfold qPrfRealPr qPrfRealExperiment
    apply congrArg (fun Q : Closed Work Bool => qWeight (· = true) Q M)
    apply bind_congr
    intro k
    change ansRun ((keyScheme g).eval k) (readBoth _) = _
    rw [ans_both]
    unfold messageRun
    rw [tablesOf_oracle]
    have he : (fun d : (Bytes 16) × List Byte => message g ((keyScheme g).eval k) d.1 d.2) =
        (msgPrf Sha2Set.s128s.vp (randPrims (functions Sha2Set.s128s g))).eval k :=
      funext fun d => (message_real g k d.1 d.2).symm
    rw [he]
    rfl
  have hi (g : CompressionTables) := lazy_eq_avg (Dm := Bool) id Function.injective_id
    (· = true) (D (oracle g)) M
  change (∑ g, _ * qPrfRealPr _ _ M) ≤ (∑ g, _ * qPrfIdealPr _ M) + _ at hop
  have eq (g : CompressionTables) : qPrfIdealPr (D (oracle g)) M =
      (Fintype.card (Bool → St) : ℝ≥0∞)⁻¹ * ∑ start : Bool → St,
        qWeight (· = true) (messageRun A start (oracle g)) M := by
    have e := hi g
    simp only [D, ans_both, id_eq] at e
    kexact e
  simpa only [hr, eq] using hop

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.message_hop
