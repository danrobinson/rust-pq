import Integration.SlhDsaCompressionCompileShared
import Integration.SlhDsaCompressionSearchSplit

namespace Reduction.Compression
open MLink Ideal MIdeal.Sha512 SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open SetOracle (uniformMean)
open Recording Recording.Database Recording.Compile
open scoped ComplexOrder
set_option maxRecDepth 12000
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E
local notation "Pair" => Option (ClassCollision.Cell × ClassCollision.Cell)

theorem prefix_search (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (M : (Input → Output) → Closed Work Pair) (hq : PUE (spec := unifSpec) cnt0 M q) :
    uniformMean (fun g : CompressionTables => @qWeight _ _ _ (ClassCollision.collision S g) (Classical.decPred _)
      (M (oracle g)) ρ) ≤ 16*((q:ℝ≥0∞)+1)^3/2^(8*S.vp.params.n) := by
  classical
  have b := shared_collision (trunc S) (2^(8*S.vp.params.n)) (by positivity)
    (fun B => (prefixCells_fraction S B).le) M id q hq ρ hp ht
  have event (g : CompressionTables) (z : Pair) : ClassCollision.collision S g z ↔ wins (trunc S) g (id z) := by
    cases z with
    | none => rfl
    | some pair => rcases pair with ⟨i,j⟩; rfl
  calc _ = ∑ g : CompressionTables, unifW _ g * qWeight (fun z => wins (trunc S) g (id z)) (M (oracle g)) ρ := by
         exact Finset.sum_congr rfl fun g _ => congrArg (unifW _ g * ·) (qWeight_congr_ev (event g) _ _)
       _ ≤ _ := b.trans_eq (by
         rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_mul (by norm_num),
           ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_pow (by norm_num),
           ENNReal.ofReal_add (by positivity) (by norm_num)]
         norm_num)

theorem searchRisk_le (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (q : ℕ) :
    searchRisk S ρ q ≤ (2*(q:ℝ≥0∞)+1)^2 / 2^512 + 16*((q:ℝ≥0∞)+1)^3/2^(8*S.vp.params.n) :=
  search_le_of_prefix S ρ hp ht q _ (prefix_search S ρ hp ht q)

theorem class_tcr_le (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (F : PortForger Input Output E) (a : ℕ) (hw : S.vp.params.n ≠ 16) (hn : a ≠ 1)
    (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM a (reduced S rand seeds F g))) ≤
      16*((classQueries S c.ml q qs a : ℝ≥0∞)+1)^3/2^(8*S.vp.params.n) := by
  obtain ⟨M,cost,b⟩ := ClassCollision.signature_class_collision S rand seeds F a hw hn c q qs hq hs hc
  exact b.trans (prefix_search S F.ρ₀ F.posSemidef F.trace_eq_one _ M cost)

/-- Numeric losses from the shared compression tables for wide SHA2, excluding ITSR. -/
noncomputable def wideLossWithClasses (ml q qs : ℕ) (classLoss : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  let b := HmacKey.budget S ml q qs
  let prefixLoss := fun (m : ℕ) => 16*((m:ℝ≥0∞)+1)^3/2^(8*S.vp.params.n)
  let hmac := (2*((b+(b+b) : ℕ):ℝ≥0∞)+1)^2/2^512 + prefixLoss (b+(b+b)) +
    ENNReal.ofReal (8*(b:ℝ)^2/2^512) + ENNReal.ofReal (8*(b:ℝ)^2/2^(8*S.vp.params.n))
  wideProvedLoss S ml q qs + hmac + classLoss 2 + classLoss S.vp.params.len + classLoss S.vp.params.k

noncomputable def wideCompressionLoss (ml q qs : ℕ) : ℝ≥0∞ :=
  wideLossWithClasses S ml q qs (fun a => 16*((classQueries S ml q qs a : ℝ≥0∞)+1)^3/2^(8*S.vp.params.n))

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (F : PortForger Input Output E)

private theorem move_itsr (u h i a b c : ℝ≥0∞) : u + (h+i+a+b+c) = u+h+a+b+c+i := by ac_rfl

/-- Every component of the wide shared-compression SUF bound except ITSR
is now bounded solely as a function of the query and message budgets. -/
theorem wide_suf_with_classes (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (classLoss : ℕ → ℝ≥0∞)
    (hclass : ∀ a, a ≠ 1 → uniformMean (fun g => qSM_DT_TCR_Advantage
      (qbTcrArM a (reduced S rand seeds F g))) ≤ classLoss a) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      wideLossWithClasses S c.ml q qs classLoss + uniformMean (fun g =>
        qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S rand seeds F g)) F.ρ₀) := by
  let b := HmacKey.budget S c.ml q qs
  have hm := hmac_le_search S rand seeds F hw c q qs hq hs hc
  have hash := searchRisk_le S F.ρ₀ F.posSemidef F.trace_eq_one (b+(b+b))
  have hc2 := hclass 2 (by decide)
  have hcl := hclass S.vp.params.len (by cases S <;> decide)
  have hck := hclass S.vp.params.k (by cases S <;> decide)
  apply (wide_suf_partial S rand seeds F hw c q qs hq hs hc).trans
  unfold wideRemaining wideLossWithClasses
  refine (add_le_add le_rfl (add_le_add (add_le_add (add_le_add (add_le_add
    (hm.trans (add_le_add (add_le_add hash le_rfl) le_rfl)) le_rfl) hc2) hcl) hck)).trans_eq ?_
  exact move_itsr _ _ _ _ _ _

theorem wide_suf_itsr (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      wideCompressionLoss S c.ml q qs + uniformMean (fun g =>
        qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S rand seeds F g)) F.ρ₀) :=
  wide_suf_with_classes S rand seeds F hw c q qs hq hs hc _ (fun a hn =>
    class_tcr_le S rand seeds F a hw hn c q qs hq hs hc)

theorem wide_euf_itsr (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      wideCompressionLoss S c.ml q qs + uniformMean (fun g =>
        qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S rand seeds F g)) F.ρ₀) :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans
      (wide_suf_itsr S rand seeds F hw c q qs hq hs hc)

end Reduction.Compression
#print axioms Reduction.Compression.prefix_search
#print axioms Reduction.Compression.searchRisk_le
#print axioms Reduction.Compression.class_tcr_le
#print axioms Reduction.Compression.wide_suf_itsr
#print axioms Reduction.Compression.wide_euf_itsr
