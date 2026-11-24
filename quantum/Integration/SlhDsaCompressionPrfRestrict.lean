import Integration.SlhDsaCompressionPrfDomain
import Integration.SlhDsaCompressionForsReduction

namespace Reduction.Compression.SkGame
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg ENNReal
open scoped Kronecker

def project {W P A R α : Type} [Fintype W] [Inhabited R]
    (Q : QOC W (PRFScheme.PRFOracleSpec (P × A) R) α) :=
  wrap0 (Restrict.restrictImpl (V := R) (fun d : P × A => some d.2)) Q

theorem restore {W P A R α : Type} [Fintype W] [Inhabited R] (pk : P)
    (Q : QOC W (PRFScheme.PRFOracleSpec (P × A) R) α)
    (hq : AllQueries (QG W (seedIndex pk)) (fun _ => True) Q) :
    wrap0 (Restrict.restrictImpl (fun a : A => some (pk,a))) (project Q) = Q := by
  unfold project
  induction Q using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j|n|⟨k',a⟩
    · rw [wrap0_instr_bind,wrap0_instr_bind]
      exact bind_congr fun u => ih u (hq.2 u)
    · rw [wrap0_query_bind,liftQ_restrict_unif,wrap0_query_bind,liftQ_restrict_unif]
      exact bind_congr fun u => ih u (hq.2 u)
    · have h : k' = pk := hq.1
      subst k'
      rw [wrap0_query_bind,liftQ_restrict_some (fun d : P × A => some d.2) (pk,a) a rfl,wrap0_query_bind,
        liftQ_restrict_some (fun a : A => some (pk,a)) a (pk,a) rfl]
      exact bind_congr fun u => ih u (hq.2 u)

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

noncomputable def machine (pk : S.Node) (H : Input → Output) :
    QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (SkAdrs S.vp) S.Node) Bool :=
  let f := functions S (tablesOf H)
  let B := F.at H (pureBytesAlg S.vp (randPrims f) (SetOracle.codecFor S f)
    (fun key => rand key.pkSeed key.pkRoot) seeds)
  project (checkedBody sufCheck (qPureBytesToInternal B) pk)

theorem atOracle (g : CompressionTables) :
    drawThen seeds (fun pk => addressAt S pk (machine S rand seeds F pk (oracle g))) =
      qbPrfWC sufCheck (reduced S rand seeds F g) := by
  rw [qbPrfWC_draw]
  unfold machine
  rw [tablesOf_oracle]
  apply congrArg (drawThen seeds)
  funext pk
  have h := checkedBody_seed sufCheck (reduced S rand seeds F g) pk
  kexact restore pk (checkedBody sufCheck (reduced S rand seeds F g) pk) h

/-- Real-to-ideal signature-reduction PRF step for a compression-port implementation of the
public-seed branch. The query budget includes every port call made inside that branch. -/
theorem real_le_ideal (q : ℕ)
    (hq : ∀ pk, PrfAnswerCost (machine S rand seeds F pk) q) :
    let Q := fun g => reduced S rand seeds F g
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (skPrfC S.vp (randPrims (functions S g)))
      (qbPrfWC sufCheck (Q g)) F.ρ₀) ≤
      (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (qbPrfWC sufCheck (Q g)) F.ρ₀) +
        ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  classical
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input × Output) × E) F.ρ₀ F.posSemidef F.trace_eq_one
  have h := address_prf_sample_answer S seeds (machine S rand seeds F) q hq ρ
  dsimp only at h ⊢
  simp only [atOracle] at h
  rw [hρ]
  kexact h

end Reduction.Compression.SkGame
#print axioms Reduction.Compression.SkGame.real_le_ideal
