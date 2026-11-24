import Integration.SlhDsaCompressionSmallItsrMachine

namespace Reduction.Compression.SmallItsr
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum KeyedHash QMsg QItsr ENNReal Classical
open SetOracle (uniformMean)
open scoped ComplexOrder

private def cell : Evidence → Cell
  | some (.inl u) => u
  | _ => default
private def pair : Evidence → Option (Cell × Cell)
  | some (.inr p) => some p
  | _ => none
private def pre (g : CompressionTables) : Evidence → Prop
  | some (.inl u) => g.1 u = IV128
  | _ => False

variable {K : Type} [DecidableEq K] (key : St → K)
variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E
omit [DecidableEq K] in
private theorem split (g : CompressionTables) (X : Closed Work Evidence) (ρ : Matrix Work Work ℂ) :
    qWeight (accepts key g) X ρ ≤ qWeight (fun z => g.1 (cell z) = IV128) X ρ +
      qWeight (fun z => Recording.Compile.LeftPort.wins key g (pair z)) X ρ := by
  let P := pre g
  let C := fun z => Recording.Compile.LeftPort.wins key g (pair z)
  have disj : ∀ z, P z → ¬ C z := by
    rintro (_ | u | p) <;> simp [P,C,pre,pair,Recording.Compile.LeftPort.wins]
  have incl : ∀ z, P z → g.1 (cell z) = IV128 := by
    rintro (_ | u | p) <;> simp [P,pre,cell]
  have eq : ∀ z, accepts key g z ↔ P z ∨ C z := by
    rintro (_ | u | ⟨u,v⟩) <;> simp [accepts,P,C,pre,pair,Recording.Compile.LeftPort.wins]
  calc _ = qWeight (fun z => P z ∨ C z) X ρ := qWeight_congr_ev eq _ _
       _ = _ := qWeight_or disj X ρ
       _ ≤ _ := add_le_add (qWeight_mono incl X ρ) le_rfl

def budget (S : Sha2Set) (L q qs : ℕ) := MessageHash.machineBudget S L q qs + (extractionBudget L qs + extractionBudget L qs)
noncomputable def loss (S : Sha2Set) (L q qs bits : ℕ) : ℝ≥0∞ :=
  (2*(budget S L q qs:ℝ≥0∞)+1)^2 / 2^256 + 16*((budget S L q qs:ℝ≥0∞)+1)^3/2^bits

theorem itsr_bound (S : Sha2Set) (hn : S.vp.params.n = 16) (i : Fin S.vp.params.k)
    (cover : Covers S hn key i) (bits : ℕ)
    (uniform : ∀ B : Finset K, ((Finset.univ.filter fun y => key y ∈ B).card : ℝ)/Fintype.card St ≤ (B.card:ℝ)/2^bits)
    (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)
    (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S r seeds F g)) F.ρ₀)
      ≤ loss S c.ml q qs bits := by
  let M := witnessMachine S hn key r seeds F c.ml qs
  have cost := witness_cost S hn key r seeds F c q qs hq hs hc
  have p := Hmac256.fixed_state_shared M cell IV128 F.ρ₀ F.posSemidef F.trace_eq_one _ cost
  have t := Recording.Compile.LeftPort.search key bits uniform M pair _ cost F.ρ₀ F.posSemidef F.trace_eq_one
  apply le_trans _ (add_le_add p t)
  unfold uniformMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  rw [← mul_add]
  apply mul_le_mul' le_rfl
  exact (witness_success S hn key r seeds F i cover c qs hs hc g).trans (split key g _ _)

end Reduction.Compression.SmallItsr
#print axioms Reduction.Compression.SmallItsr.itsr_bound
