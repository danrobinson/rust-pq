import Integration.SlhDsaCompressionHmacMonitor
import Integration.SlhDsaCompressionHmacSignature
import Integration.SlhDsaCompressionClassCandidates
import Integration.SlhDsaCompressionCompose

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

/-- Public SHA-512 prefix collision or a preimage of an independent, revealed
starting state. The target may influence the machine before its first query. -/
def searchWin (g : CompressionTables) (i : Chain512) : Option HmacKey.Evidence → Prop
  | none => False
  | some (.inl u) => g.2 u = i
  | some (.inr (u,v)) => u ≠ v ∧ MIdeal.Sha512.trunc S (g.2 u) = MIdeal.Sha512.trunc S (g.2 v)

noncomputable def searchRisk (ρ : Matrix Work Work ℂ) (q : ℕ) : ℝ≥0∞ :=
  ⨆ M : {m : Chain512 → (Input → Output) → Closed Work (Option HmacKey.Evidence) //
      ∀ i, PUE (spec := unifSpec) cnt0 (m i) q},
    uniformMean (fun g : CompressionTables => uniformMean (fun i : Chain512 =>
      @qWeight _ _ _ (searchWin S g i) (Classical.decPred _) (M.val i (oracle g)) ρ))

def classQueries (L q qs a : ℕ) := ClassOne.budget S L q qs + tcrTargets S.vp * ClassCollision.walkMax S +
  (1 + 2 * ((38 + S.vp.params.n * a) / 128 + 1))

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)

private theorem class_le_search (hw : S.vp.params.n ≠ 16) (a : ℕ) (hn : a ≠ 1) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM a (reduced S rand seeds F g))) ≤
      searchRisk S F.ρ₀ (classQueries S c.ml q qs a) := by
  classical
  obtain ⟨M,cost,win⟩ := ClassCollision.signature_class_collision S rand seeds F a hw hn c q qs hq hs hc
  let tag := Option.map (Sum.inr : ClassCollision.Cell × ClassCollision.Cell → HmacKey.Evidence)
  let B := fun (_ : Chain512) H => tag <$> M H
  have bc (i) : PUE (spec := unifSpec) cnt0 (B i) (classQueries S c.ml q qs a) := PUE.map _ cost
  apply win.trans
  refine le_trans ?_ (le_iSup_of_le ⟨B,bc⟩ le_rfl)
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul' le_rfl
  have eq (i : Chain512) : @qWeight _ _ _ (searchWin S g i) (Classical.decPred _) (B i (oracle g)) F.ρ₀ =
      @qWeight _ _ _ (ClassCollision.collision S g) (Classical.decPred _) (M (oracle g)) F.ρ₀ := by
    unfold B
    rw [qWeight_map]
    apply qWeight_congr_ev
    intro z
    cases z with
    | none => rfl
    | some p => rfl
  simp only [uniformMean, eq, ← Finset.sum_mul, sum_unifW, one_mul, le_refl]

private theorem evidence_search (g : CompressionTables) (i : Chain512) (z : Option HmacKey.Evidence)
    (hit : HmacKey.acceptsEvidence g i z = true) : searchWin S g i z := by
  rcases z with (_ | u | ⟨u,v⟩)
  · cases hit
  · change g.2 u = i
    exact of_decide_eq_true hit
  · obtain ⟨ne,eq⟩ : u ≠ v ∧ g.2 u = g.2 v := of_decide_eq_true hit
    exact ⟨ne,congrArg (MIdeal.Sha512.trunc S) eq⟩

private theorem reorder {a b : ℝ≥0∞} (hb : a ≤ b) (i l r : ℝ≥0∞) :
    i+a+l+r ≤ i+(b+l+r) := by
  rw [← add_assoc i (b+l), ← add_assoc i b]
  gcongr

theorem hmac_le_search (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let Q := fun g => reduced S rand seeds F g
    let B := HmacKey.budget S c.ml q qs
    uniformMean (fun g => qPrfRealPr (msgPrf S.vp (randPrims (functions S g))) (qbPrfMsgWL sufCheck (Q g)) F.ρ₀) -
      uniformMean (fun g => qPrfIdealPr (qbPrfMsgWL sufCheck (Q g)) F.ρ₀) ≤
    searchRisk S F.ρ₀ (B+(B+B)) + ENNReal.ofReal (8*(B:ℝ)^2 / 2^512) +
      ENNReal.ofReal (8*(B:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  classical
  intro Q B
  let A := HmacKey.machine S (carrier S) rand seeds F
  have cost := HmacKey.machine_cost S (carrier S) rand seeds F c q qs hq hs hc
  let M := fun i => HmacKey.evidenceMachine S A i B
  have bc (i) := HmacKey.evidence_budget S A i B cost
  have bound : (∑ g : CompressionTables, unifW _ g * ∑ i : Chain512, unifW _ i *
      HmacKey.digestCollisionPr S A F.ρ₀ g i) ≤ searchRisk S F.ρ₀ (B+(B+B)) := by
    refine le_trans ?_ (le_iSup_of_le ⟨M,bc⟩ le_rfl)
    apply Finset.sum_le_sum
    intro g _
    apply mul_le_mul' le_rfl
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul' le_rfl
    apply (HmacKey.evidence_success S A g i B cost F.ρ₀).trans
    exact qWeight_mono (evidence_search S g i) _ _
  apply tsub_le_iff_left.mpr
  have hh := HmacKey.signature_hmac_collision S rand seeds F hw c q qs hq hs hc
  exact hh.trans (reorder bound _ _ _)

/-- Shared-compression forgery bound on the four wider sets. Only the signature
ITSR experiment and a budgeted public SHA-512 search game remain. -/
noncomputable def wideSearchBound (L q qs : ℕ) : ℝ≥0∞ :=
  let b := HmacKey.budget S L q qs
  let risk := searchRisk S F.ρ₀
  wideProvedLoss S L q qs +
    ((risk (b+(b+b)) + ENNReal.ofReal (8*(b:ℝ)^2/2^512) + ENNReal.ofReal (8*(b:ℝ)^2/2^(8*S.vp.params.n))) +
    uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g)))
      (qbItsrL (reduced S rand seeds F g)) F.ρ₀) +
    risk (classQueries S L q qs 2) + risk (classQueries S L q qs S.vp.params.len) +
    risk (classQueries S L q qs S.vp.params.k))

theorem wide_suf_search (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      wideSearchBound S rand seeds F c.ml q qs := by
  apply (wide_suf_partial S rand seeds F hw c q qs hq hs hc).trans
  unfold wideSearchBound wideRemaining
  apply add_le_add le_rfl
  apply add_le_add _ (class_le_search S rand seeds F hw _ (by cases S <;> decide) c q qs hq hs hc)
  apply add_le_add _ (class_le_search S rand seeds F hw _ (by cases S <;> decide) c q qs hq hs hc)
  apply add_le_add _ (class_le_search S rand seeds F hw 2 (by decide) c q qs hq hs hc)
  exact add_le_add (hmac_le_search S rand seeds F hw c q qs hq hs hc) le_rfl

theorem wide_euf_search (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      wideSearchBound S rand seeds F c.ml q qs :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans
      (wide_suf_search S rand seeds F hw c q qs hq hs hc)

end Reduction.Compression
#print axioms Reduction.Compression.wide_suf_search
#print axioms Reduction.Compression.wide_euf_search
