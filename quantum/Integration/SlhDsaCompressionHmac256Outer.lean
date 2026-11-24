import Integration.SlhDsaCompressionHmac256Hop

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

/-- SHA-256 outer HMAC compression after replacing its keyed starting state. -/
def outerScheme (g : CompressionTables) : PRFScheme St St St :=
  ⟨$ᵗ St, fun st inner => g.1 (st, Ideal.oblock inner)⟩

/-- The real outer compression and its ideal random function are compared while
the distinguisher retains superposition access to the very same compression table. -/
theorem outer_hop {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec St St) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (outerScheme g) (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^256) := by
  let loc : Input → Option (St × Blk) := fun x => x.elim some (fun _ => none)
  let put := fun (g : CompressionTables) (r : CF St Blk) => (r,g.2)
  have h := column_prf loc put Prod.fst (fun _ => rfl) (fun _ _ => rfl)
    (fun g r t x same => by
      rcases x with i|i
      · exact congrArg (fun c : St => (c,(0 : Fin 8 → UInt64))) (same i rfl)
      · rfl)
    (fun _ => Ideal.oblock) (fun _ => Ideal.oblock_injective)
    (fun _ _ => rfl) A q hA ρ
  simp only [card_St, Nat.cast_pow, Nat.cast_ofNat] at h
  kexact h


def innerDigest (g : CompressionTables) (start : St) (d : (Bytes 16) × List Byte) :=
  mdFold g.1 start (Ideal.iblocks d.1 d.2)

abbrev truncate := Ideal.out16

private def handler (g : CompressionTables) (start : St) :
    QueryImpl (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16))
      (OracleComp (PRFScheme.PRFOracleSpec St St))
  | .inl n => liftM ((PRFScheme.PRFOracleSpec St St).query (.inl n))
  | .inr d => truncate <$> liftM ((PRFScheme.PRFOracleSpec St St).query (.inr (innerDigest g start d)))

def outerMachine {W : Type} [Fintype W] (g : CompressionTables) (start : St)
    (A : QOC W (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool) :=
  wrap0 (handler g start) A

theorem outer_answer {W : Type} [Fintype W] (g : CompressionTables) (start : St)
    (f : St → St) (A : QOC W (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool) :
    ansRun f (outerMachine g start A) = ansRun (fun d => truncate (f (innerDigest g start d))) A := by
  unfold outerMachine
  induction A using OracleComp.inductionOn with
  | pure a => simp [ansRun_pure]
  | query_bind t k ih =>
    rcases t with j|n|d
    · rw [wrap0_instr_bind, ansRun_instr, ansRun_instr]; exact bind_congr ih
    · rw [wrap0_query_bind]
      change ansRun f (liftM ((instrSpec W + PRFScheme.PRFOracleSpec St St).query (.inr (.inl n))) >>= _) = _
      rw [ansRun_unif, ansRun_unif]; exact bind_congr ih
    · rw [wrap0_query_bind]
      have he : (liftQ (handler g start (.inr d)) : QOC W _ _) =
          truncate <$> liftM ((instrSpec W + PRFScheme.PRFOracleSpec St St).query
            (.inr (.inr (innerDigest g start d)))) := by
        simp [handler, liftQ, simulateQ_map]
      rw [he, bind_map_left, ansRun_oracle, ansRun_oracle]
      exact ih _

/-- For fixed inner and outer chaining states, the actual HMAC continuation
is exactly the real outer compression oracle wrapped around the message machine. -/
theorem outer_real {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (g : CompressionTables) (i o : St) :
    ansRun ((outerScheme g).eval o) (outerMachine g i (A (oracle g))) =
      messageRun A (fun b => if b then o else i) (oracle g) := by
  rw [outer_answer]
  unfold messageRun
  rw [tablesOf_oracle]
  rfl

variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

theorem outer_cost (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (start : St) (q : ℕ) (hA : PUE (messageCharge) A q) :
    PrfAnswerCost (fun H => outerMachine (tablesOf H) start (A H)) q := by
  intro f
  simp only [outer_answer]
  let answer := fun H d => truncate (f (innerDigest (tablesOf H) start d))
  let impl := fun H => statelessImpl ((ansScheme (answer H)).prfRealQueryImpl ())
  apply PUE.map Prod.fst (PUE.close impl _ hA ())
  rintro (n | ⟨r,m⟩) ⟨⟩
  · exact EvalCost.const _
  · have h := (fold256_cost start (Ideal.iblocks r m)).map (fun x => (truncate (f x), ()))
    have hh := h.mono (n' := (m.length + 24) / 64 + 2)
      (by rw [Ideal.iblocks_length]; omega)
    simp only [impl, statelessImpl, StateT.run, PRFScheme.prfRealQueryImpl_apply_inr, ansScheme,
      messageCharge, map_pure] at hh ⊢
    kexact hh

set_option maxRecDepth 8192 in
/-- For every fixed inner state, replace the independently sampled outer starting
state by a random function of the inner digest. The adversary's port is unchanged. -/
theorem outer_message_hop
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (i : St) (q : ℕ) (hA : PUE (messageCharge) A q)
    (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card St : ℝ≥0∞)⁻¹ * ∑ o : St,
        qWeight (· = true) (messageRun A (fun b => if b then o else i) (oracle g)) M)) ≤
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card (St → St) : ℝ≥0∞)⁻¹ * ∑ f : St → St,
        qWeight (· = true) (ansRun (fun d => truncate (f (innerDigest g i d))) (A (oracle g))) M)) +
    ENNReal.ofReal (8*(q:ℝ)^2 / 2^256) := by
  intro M
  let D := fun H => outerMachine (tablesOf H) i (A H)
  have h := outer_hop D q (outer_cost A i q hA) ρ
  have hr (g : CompressionTables) : qPrfRealPr (outerScheme g) (D (oracle g)) M =
      (Fintype.card St : ℝ≥0∞)⁻¹ * ∑ o : St,
        qWeight (· = true) (messageRun A (fun b => if b then o else i) (oracle g)) M := by
    change qWeight _ (liftU ($ᵗ St) >>= fun o =>
      ansRun ((outerScheme g).eval o) (outerMachine (tablesOf (oracle g)) i (A (oracle g)))) M = _
    simp only [tablesOf_oracle, outer_real]
    exact qWeight_liftU_uniform_bind _ _ _
  have hi (g : CompressionTables) := lazy_eq_avg (Dm := St) id Function.injective_id
    (· = true) (D (oracle g)) M
  have eq (g : CompressionTables) : qPrfIdealPr (D (oracle g)) M =
      (Fintype.card (St → St) : ℝ≥0∞)⁻¹ * ∑ f : St → St,
        qWeight (· = true) (ansRun (fun d => truncate (f (innerDigest g i d))) (A (oracle g))) M := by
    change qWeight _ (idealRun (D (oracle g)) ∅) M = _
    rw [hi g]
    simp only [D, tablesOf_oracle, outer_answer, id_eq]
  change (∑ g, _ * qPrfRealPr _ _ M) ≤ (∑ g, _ * qPrfIdealPr _ M) + _ at h
  simpa only [hr, eq] using h

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.outer_hop
#print axioms Reduction.Compression.Hmac256.outer_real
#print axioms Reduction.Compression.Hmac256.outer_message_hop
