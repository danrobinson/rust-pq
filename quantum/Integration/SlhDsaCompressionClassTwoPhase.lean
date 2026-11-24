import Integration.SlhDsaCompressionMixedCollision

namespace Reduction.Compression.ClassCollision
open MLink Ideal Ideal.HP Ideal.Prf Ideal.Itsr MIdeal.Sha512 SLHDSA SLHDSA.Security OracleComp OracleSpec
open PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash Resources2 HiddenWeight Classical
open Recording.Compile (Right wins)
variable (S : Sha2Set)
local notation "P₀" => randPrims (carrier S)
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E) (ar : ℕ)
local notation "Work" => WS Input Output E

private noncomputable def follow (pk : S.Node) (tbl : SecretTable S.vp P₀) (log : CallLog S) :
    (Input → Output) → Closed Work (Option (Cell × Cell)) :=
  machine S (fun H => attemptAt S ar pk log <$>
    ClassOne.machine S (carrier S) rand F ar (tbl,Realize.clampL S.vp.params.len log) pk H)

def continuationBudget (L q qs : ℕ) :=
  ClassOne.budget S L q qs + (1+2*((38+S.vp.params.n*ar)/128+1))

private theorem follow_cost (pk : S.Node) (tbl : SecretTable S.vp P₀) (log : CallLog S) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (spec := unifSpec) cnt0 (follow S rand F ar pk tbl log) (continuationBudget S ar c.ml q qs) :=
  machine_cost S _ _ (PUE.map _ (ClassOne.machine_pue S (carrier S) rand F c ar _ pk q qs
    (Realize.clampL_mem _ _) hq hs hc))

private theorem factor (H : Input → Output) :
    machine S (signatureCandidates S rand seeds F ar) H = (do
      let pk ← liftU seeds
      let tbl ← liftU (Lazy.sparseTable S.vp P₀)
      follow S rand F ar pk tbl (walk S tbl pk H) H) := by
  unfold signatureCandidates follow machine
  simp only [map_bind,liftU_pure,pure_bind,bind_pure_comp]

private theorem eager_log {α : Type} (P : SHAReader α) (f : α → (Right → Chain512) → ℝ≥0∞) :
    mean (Transcript.eager P) (fun z => f z.1 z.2.2) =
      ∑ b : Right → Chain512, unifW _ b * mean (simulateQ (ansImpl (spec := hS Chain512 Block512) b) P) (fun x => f x b) := by
  unfold Transcript.eager
  rw [mean_bind]
  simp only [mean,tsum_fintype,prob_uniformSample_eq,unifW]
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg ((Fintype.card (Right → Chain512) : ℝ≥0∞)⁻¹ * ·)
  change mean _ _ = mean _ _
  rw [mean_bind]
  simp only [mean_pure]
  rw [← fst_map_run_stImpl b (logU id) P []]
  simp only [map_eq_bind_pure_comp,mean_bind,Function.comp_def,mean_pure]

private theorem fixed_bound (hw : S.vp.params.n ≠ 16) (a : CF St Blk) (pk : S.Node) (tbl : SecretTable S.vp P₀)
    (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ b : Right → Chain512, unifW _ b * qWeight (fun z => wins (trunc S) (a,b) (id z))
        (follow S rand F ar pk tbl (walk S tbl pk (oracle (a,b))) (oracle (a,b))) F.ρ₀) ≤
      (((tcrTargets S.vp * walkMax S)^2 : ℕ):ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ +
        Transcript.remainingLoss S (tcrTargets S.vp * walkMax S) (continuationBudget S ar c.ml q qs) := by
  let P := readWalk S a pk (structureFree tbl) []
  let f := fun l : CallLog S => fun b : Right → Chain512 => qWeight (fun z => wins (trunc S) (a,b) (id z))
    (follow S rand F ar pk tbl l (oracle (a,b))) F.ρ₀
  have eq := eager_log P f
  have eval (b : Right → Chain512) : simulateQ (ansImpl (spec := hS Chain512 Block512) b) P =
      pure (walk S tbl pk (oracle (a,b))) := readWalk_eval S (a,b) hw pk _ []
  simp only [eval,mean_pure] at eq
  apply le_trans _ (Transcript.mixed_bound S a P _ (readWalk_bound S a hw pk _ [] _ (walk_count S tbl)) default
    (follow S rand F ar pk tbl) id _ (fun log => follow_cost S rand F ar pk tbl log c q qs hq hs hc)
    F.ρ₀ F.posSemidef F.trace_eq_one)
  exact le_of_eq eq.symm

noncomputable def twoPhaseLoss (L q qs : ℕ) : ℝ≥0∞ :=
  (((tcrTargets S.vp * walkMax S)^2 : ℕ):ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ +
    Transcript.remainingLoss S (tcrTargets S.vp * walkMax S) (continuationBudget S ar L q qs)

private theorem uniform_mean {D : Type} [Fintype D] [SampleableType D] (f : D → ℝ≥0∞) :
    mean ($ᵗ D) f = ∑ d, unifW _ d * f d := by
  simp only [mean,tsum_fintype,prob_uniformSample_eq,unifW]

private theorem avg_le {A : Type} (oa : ProbComp A) (f : A → ℝ≥0∞) (l : ℝ≥0∞)
    (hf : ∀ x, f x ≤ l) : mean oa f ≤ l :=
  (mean_mono oa hf).trans (by rw [mean, ENNReal.tsum_mul_right]; exact (mul_le_mul' (tsum_prob_eq_le_one oa) le_rfl).trans_eq (one_mul _))

private theorem draws {A B D : Type} [Fintype D] [SampleableType D] (p : ProbComp A) (t : ProbComp B)
    (w : D → A → B → ℝ≥0∞) (l : ℝ≥0∞) (h : ∀ a b, (∑ d, unifW _ d * w d a b) ≤ l) :
    (∑ d, unifW _ d * mean p (fun a => mean t (w d a))) ≤ l := by
  rw [← uniform_mean,mean_switch]
  apply avg_le
  intro a
  rw [mean_switch]
  apply avg_le
  intro b
  rw [uniform_mean]
  exact h a b

private theorem pointwise (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (ha : ar ≠ 1) :
    qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g)) ≤
      mean seeds (fun pk => mean (Lazy.sparseTable S.vp P₀) (fun tbl =>
        qWeight (fun z => wins (trunc S) g (id z))
          (follow S rand F ar pk tbl (walk S tbl pk (oracle g)) (oracle g)) F.ρ₀)) := by
  rw [candidates_success (arity := ar) (E := E) S seeds g (qbTcrArM ar (reduced S rand seeds F g)),
    ← signatureCandidates_oracle]
  apply (collision_reduction S (signatureCandidates S rand seeds F ar) g hw ha F.ρ₀).trans
  rw [factor,qWeight_liftU_bind_tsum]
  apply tsum_le_tsum
  intro pk
  dsimp only
  rw [qWeight_liftU_bind_tsum]
  apply mul_le_mul' le_rfl
  apply tsum_le_tsum
  intro tbl
  apply mul_le_mul' le_rfl
  apply qWeight_mono
  rintro (_ | ⟨u,v⟩) win
  · exact win.elim
  · exact win

private theorem product_mean {A B : Type} [Fintype A] [Fintype B] (f : A × B → ℝ≥0∞) :
    (∑ g : A × B, unifW _ g * f g) = ∑ a, unifW _ a * ∑ b, unifW _ b * f (a,b) := by
  simp only [Fintype.sum_prod_type,unifW,Finset.mul_sum,Fintype.card_prod,Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),mul_assoc]

/-- Charge adaptive classical SHA-512 reads from the honest signature tree to
the birthday bound and charge only the forgery and its extraction to the
subsequent quantum continuation. -/
theorem two_phase_class_tcr (hw : S.vp.params.n ≠ 16) (ha : ar ≠ 1) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g))) ≤
      twoPhaseLoss S ar c.ml q qs := by
  unfold SetOracle.uniformMean
  rw [product_mean (fun g : CompressionTables => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g)))]
  calc _ ≤ ∑ a : CF St Blk, unifW _ a * twoPhaseLoss S ar c.ml q qs := by
         apply Finset.sum_le_sum
         intro a _
         apply mul_le_mul' le_rfl
         apply le_trans _ (draws seeds (Lazy.sparseTable S.vp P₀)
           (fun b pk tbl => qWeight (fun z => wins (trunc S) (a,b) (id z))
               (follow S rand F ar pk tbl (walk S tbl pk (oracle (a,b))) (oracle (a,b))) F.ρ₀) _
           (fun pk tbl => fixed_bound S rand F ar hw a pk tbl c q qs hq hs hc))
         apply Finset.sum_le_sum
         exact fun b _ => mul_le_mul' le_rfl (pointwise S rand seeds F ar (a,b) hw ha)
       _ = _ := by rw [← Finset.sum_mul,sum_unifW,one_mul]

end Reduction.Compression.ClassCollision
#print axioms Reduction.Compression.ClassCollision.two_phase_class_tcr
