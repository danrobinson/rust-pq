import Integration.SlhDsaCompressionHmacHop

namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

/-- SHA-512 outer HMAC compression after replacing its keyed starting state. -/
def outerScheme (g : CompressionTables) : PRFScheme Chain512 Chain512 Chain512 :=
  ⟨$ᵗ Chain512, fun st inner => g.2 (st, MIdeal.Sha512.oblock inner)⟩

/-- The real outer compression and its ideal random function are compared while
the distinguisher retains superposition access to the very same compression table. -/
theorem wide_outer_hop {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec Chain512 Chain512) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (outerScheme g) (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^512) := by
  let loc : Input → Option (Chain512 × Block512) := fun x => x.elim (fun _ => none) some
  let put := fun (g : CompressionTables) (r : CF Chain512 Block512) => (g.1,r)
  have h := column_prf loc put Prod.snd (fun _ => rfl) (fun _ _ => rfl)
    (fun g r t x same => by
      rcases x with i|i
      · rfl
      · exact congrArg (fun c : Chain512 => ((0 : St), arrayVectorEquivFin UInt64 8 c)) (same i rfl))
    (fun _ => MIdeal.Sha512.oblock) (fun _ => MIdeal.Sha512.oblock_injective)
    (fun _ _ => rfl) A q hA ρ
  simp only [MIdeal.Sha512.card_chain512, Nat.cast_pow, Nat.cast_ofNat] at h
  kexact h

variable (S : Sha2Set)

def innerDigest (g : CompressionTables) (start : Chain512) (d : S.Node × List Byte) :=
  mdFold g.2 start (MIdeal.Sha512.iblocks S d.1 d.2)

def truncate (x : Chain512) : S.Node :=
  byteArrayPrefixOrZero (VCVio.Algorithms.Sha2.stateBytes64 x.toArray) S.vp.params.n

private def handler (g : CompressionTables) (start : Chain512) :
    QueryImpl (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node)
      (OracleComp (PRFScheme.PRFOracleSpec Chain512 Chain512))
  | .inl n => liftM ((PRFScheme.PRFOracleSpec Chain512 Chain512).query (.inl n))
  | .inr d => truncate S <$> liftM ((PRFScheme.PRFOracleSpec Chain512 Chain512).query (.inr (innerDigest S g start d)))

def outerMachine {W : Type} [Fintype W] (g : CompressionTables) (start : Chain512)
    (A : QOC W (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool) :=
  wrap0 (handler S g start) A

theorem outer_answer {W : Type} [Fintype W] (g : CompressionTables) (start : Chain512)
    (f : Chain512 → Chain512) (A : QOC W (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool) :
    ansRun f (outerMachine S g start A) = ansRun (fun d => truncate S (f (innerDigest S g start d))) A := by
  unfold outerMachine
  induction A using OracleComp.inductionOn with
  | pure a => simp [ansRun_pure]
  | query_bind t k ih =>
    rcases t with j|n|d
    · rw [wrap0_instr_bind, ansRun_instr, ansRun_instr]; exact bind_congr ih
    · rw [wrap0_query_bind]
      change ansRun f (liftM ((instrSpec W + PRFScheme.PRFOracleSpec Chain512 Chain512).query (.inr (.inl n))) >>= _) = _
      rw [ansRun_unif, ansRun_unif]; exact bind_congr ih
    · rw [wrap0_query_bind]
      have he : (liftQ (handler S g start (.inr d)) : QOC W _ _) =
          truncate S <$> liftM ((instrSpec W + PRFScheme.PRFOracleSpec Chain512 Chain512).query
            (.inr (.inr (innerDigest S g start d)))) := by
        simp [handler, liftQ, simulateQ_map]
      rw [he, bind_map_left, ansRun_oracle, ansRun_oracle]
      exact ih _

/-- For fixed inner and outer chaining states, the actual HMAC continuation
is exactly the real outer compression oracle wrapped around the message machine. -/
theorem outer_real {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (g : CompressionTables) (i o : Chain512) :
    ansRun ((outerScheme g).eval o) (outerMachine S g i (A (oracle g))) =
      messageRun S A (fun b => if b then o else i) (oracle g) := by
  rw [outer_answer]
  unfold messageRun
  rw [tablesOf_oracle]
  rfl

variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

theorem outer_cost (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (start : Chain512) (q : ℕ) (hA : PUE (messageCharge S) A q) :
    PrfAnswerCost (fun H => outerMachine S (tablesOf H) start (A H)) q := by
  intro f
  simp only [outer_answer]
  let answer := fun H d => truncate S (f (innerDigest S (tablesOf H) start d))
  let impl := fun H => statelessImpl ((ansScheme (answer H)).prfRealQueryImpl ())
  apply PUE.map Prod.fst (PUE.close impl _ hA ())
  rintro (n | ⟨r,m⟩) ⟨⟩
  · exact EvalCost.const _
  · have h := (fold512_cost start (MIdeal.Sha512.iblocks S r m)).map (fun x => (truncate S (f x), ()))
    have hh := h.mono (n' := (m.length + S.vp.params.n + 16) / 128 + 2)
      (by rw [MIdeal.Sha512.iblocks_length]; omega)
    simp only [impl, statelessImpl, StateT.run, PRFScheme.prfRealQueryImpl_apply_inr, ansScheme,
      messageCharge, map_pure] at hh ⊢
    kexact hh

set_option maxRecDepth 8192 in
/-- For every fixed inner state, replace the independently sampled outer starting
state by a random function of the inner digest. The adversary's port is unchanged. -/
theorem wide_outer_message_hop
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (i : Chain512) (q : ℕ) (hA : PUE (messageCharge S) A q)
    (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card Chain512 : ℝ≥0∞)⁻¹ * ∑ o : Chain512,
        qWeight (· = true) (messageRun S A (fun b => if b then o else i) (oracle g)) M)) ≤
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card (Chain512 → Chain512) : ℝ≥0∞)⁻¹ * ∑ f : Chain512 → Chain512,
        qWeight (· = true) (ansRun (fun d => truncate S (f (innerDigest S g i d))) (A (oracle g))) M)) +
    ENNReal.ofReal (8*(q:ℝ)^2 / 2^512) := by
  intro M
  let D := fun H => outerMachine S (tablesOf H) i (A H)
  have h := wide_outer_hop D q (outer_cost S A i q hA) ρ
  have hr (g : CompressionTables) : qPrfRealPr (outerScheme g) (D (oracle g)) M =
      (Fintype.card Chain512 : ℝ≥0∞)⁻¹ * ∑ o : Chain512,
        qWeight (· = true) (messageRun S A (fun b => if b then o else i) (oracle g)) M := by
    change qWeight _ (liftU ($ᵗ Chain512) >>= fun o =>
      ansRun ((outerScheme g).eval o) (outerMachine S (tablesOf (oracle g)) i (A (oracle g)))) M = _
    simp only [tablesOf_oracle, outer_real]
    exact qWeight_liftU_uniform_bind _ _ _
  have hi (g : CompressionTables) := lazy_eq_avg (Dm := Chain512) id Function.injective_id
    (· = true) (D (oracle g)) M
  have eq (g : CompressionTables) : qPrfIdealPr (D (oracle g)) M =
      (Fintype.card (Chain512 → Chain512) : ℝ≥0∞)⁻¹ * ∑ f : Chain512 → Chain512,
        qWeight (· = true) (ansRun (fun d => truncate S (f (innerDigest S g i d))) (A (oracle g))) M := by
    change qWeight _ (idealRun (D (oracle g)) ∅) M = _
    rw [hi g]
    simp only [D, tablesOf_oracle, outer_answer, id_eq]
  change (∑ g, _ * qPrfRealPr _ _ M) ≤ (∑ g, _ * qPrfIdealPr _ M) + _ at h
  simpa only [hr, eq] using h

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.wide_outer_hop
#print axioms Reduction.Compression.HmacKey.outer_real
#print axioms Reduction.Compression.HmacKey.wide_outer_message_hop
