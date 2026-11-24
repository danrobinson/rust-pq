import Integration.SlhDsaCompressionItsrReduction
import Integration.SlhDsaCompressionPrefixBound

namespace Reduction.Compression.MessageHash
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
open Recording.Compile
open scoped ComplexOrder
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E
local notation "Ev" => Option HmacKey.Evidence

private def readPre : Ev → Cell
  | some (.inl u) => u
  | _ => default

private def readPair : Ev → Option (Cell × Cell)
  | some (.inr p) => some p
  | _ => none

private def pre (g : CompressionTables) : Ev → Prop
  | some (.inl u) => g.2 u = MIdeal.Sha512.initial
  | _ => False

open Classical in
private theorem split (i : Fin S.vp.params.k) (g : CompressionTables) (X : Closed Work Ev) (ρ : Matrix Work Work ℂ) :
    qWeight (accepts S i g) X ρ ≤ qWeight (fun z => g.2 (readPre z) = MIdeal.Sha512.initial) X ρ +
      qWeight (fun z => wins (coordinate S i) g (readPair z)) X ρ := by
  classical
  let C := fun z => wins (coordinate S i) g (readPair z)
  have disj : ∀ z, pre g z → ¬ C z := by
    rintro (_ | u | p) <;> simp [C,pre,readPair,wins]
  have incl : ∀ z, pre g z → g.2 (readPre z) = MIdeal.Sha512.initial := by
    rintro (_ | u | p) <;> simp [pre,readPre]
  have eq : ∀ z, accepts S i g z ↔ pre g z ∨ C z := by
    rintro (_ | u | ⟨u,v⟩) <;> simp [accepts,pre,C,readPair,wins]
  calc _ = qWeight (fun z => pre g z ∨ C z) X ρ := qWeight_congr_ev eq _ _
       _ = _ := qWeight_or disj X ρ
       _ ≤ _ := add_le_add (qWeight_mono incl X ρ) le_rfl

noncomputable def coordinateLoss (q : ℕ) : ℝ≥0∞ :=
  (2*(q:ℝ≥0∞)+1)^2/2^512 + ENNReal.ofReal (16*((q:ℝ)+1)^3/2^(S.vp.params.h+S.vp.params.a))

open Classical in
theorem search_bound (i : Fin S.vp.params.k) (M : (Input → Output) → Closed Work Ev) (q : ℕ)
    (hq : PUE (spec := unifSpec) cnt0 M q) (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    uniformMean (fun g => qWeight (accepts S i g) (M (oracle g)) ρ) ≤ coordinateLoss S q := by
  classical
  have pre := fixed_state_shared M readPre MIdeal.Sha512.initial ρ hp ht q hq
  have col := shared_collision (coordinate S i) (2^(S.vp.params.h+S.vp.params.a)) (by positivity)
    (fun B => (coordinate_fraction S i B).le) M readPair q hq ρ hp ht
  apply le_trans _ (add_le_add pre col)
  simp only [uniformMean, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (split S i g _ ρ)

variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)
def queries (L q qs : ℕ) := machineBudget S L q qs + (extractionBudget S L qs + extractionBudget S L qs)

theorem signature_itsr_le (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g)))
      (qbItsrL (reduced S r seeds F g)) F.ρ₀) ≤ coordinateLoss S (queries S c.ml q qs) := by
  classical
  let i : Fin S.vp.params.k := ⟨0,by cases S <;> decide⟩
  have h := search_bound S i (witnessMachine S r seeds F i c.ml qs) _ (witness_cost S r seeds F hw i c q qs hq hs hc)
    F.ρ₀ F.posSemidef F.trace_eq_one
  exact (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl (witness_success S r seeds F hw i c qs hs hc g)).trans h

end Reduction.Compression.MessageHash

namespace Reduction.Compression
open MLink SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
    (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)

/-- Query-bounded shared-compression forgery estimate using one of the FORS
coordinates in the ITSR experiment. Its collision loss can exceed one. -/
noncomputable def wideCoordinateBound (L q qs : ℕ) :=
  wideCompressionLoss S L q qs + MessageHash.coordinateLoss S (MessageHash.queries S L q qs)

theorem wide_suf_closed (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S r seeds F g)) ≤ wideCoordinateBound S c.ml q qs :=
  (wide_suf_itsr S r seeds F hw c q qs hq hs hc).trans (add_le_add le_rfl
    (MessageHash.signature_itsr_le S r seeds F hw c q qs hq hs hc))

theorem wide_euf_closed (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S r seeds F g)) ≤ wideCoordinateBound S c.ml q qs :=
  (wide_euf_itsr S r seeds F hw c q qs hq hs hc).trans (add_le_add le_rfl
    (MessageHash.signature_itsr_le S r seeds F hw c q qs hq hs hc))
/-- The one-coordinate estimate is vacuous at the repository's benchmark
of 2^40 public queries, even before adding the other security losses. -/
theorem MessageHash.coordinate_benchmark (L qs : ℕ) :
    1 ≤ MessageHash.coordinateLoss S (MessageHash.queries S L (2^40) qs) := by
  let Q := MessageHash.queries S L (2^40) qs
  have hQ : 2^40 ≤ Q := by
    dsimp [Q,MessageHash.queries,MessageHash.machineBudget]
    omega
  have hx : (2:ℝ)^40 ≤ (Q:ℝ)+1 := by
    have z : (2:ℝ)^40 ≤ (Q:ℝ) := by exact_mod_cast hQ
    linarith
  have hex : S.vp.params.h + S.vp.params.a ≤ 120 := by cases S <;> decide
  have hd : (2:ℝ)^(S.vp.params.h + S.vp.params.a) ≤ ((2:ℝ)^40)^3 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hex
  have v : (1:ℝ) ≤ 16*((Q:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [one_mul]
    apply hd.trans
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2^40) hx 3
    linarith [show 0 ≤ ((Q:ℝ)+1)^3 by positivity]
  have ve := ENNReal.ofReal_le_ofReal v
  rw [ENNReal.ofReal_one] at ve
  exact ve.trans le_add_self

theorem wideCoordinateBound_benchmark (L qs : ℕ) : 1 ≤ wideCoordinateBound S L (2^40) qs :=
  (MessageHash.coordinate_benchmark S L qs).trans le_add_self

end Reduction.Compression
#print axioms Reduction.Compression.MessageHash.signature_itsr_le
#print axioms Reduction.Compression.wide_suf_closed
#print axioms Reduction.Compression.wide_euf_closed
#print axioms Reduction.Compression.wideCoordinateBound_benchmark
