import Integration.SlhDsaCompressionBudget
import Integration.SlhDsaCompressionDspr
import Integration.SlhDsaCompressionForsTransport

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
variable (S : Sha2Set)
def carrier : RandFns S.vp.params :=
  ⟨fun _ _ _ => default, fun _ _ _ _ => default, fun _ _ _ => default, fun _ _ _ => default⟩
local notation "f₀" => carrier S
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)
noncomputable abbrev reduced (g : CompressionTables) := qPureBytesToInternal (experimentForger S rand seeds F g)

private theorem phase_oracle (g : CompressionTables) (st : PhaseState S f₀) (pk : S.Node) :
    phaseMachine S f₀ rand F st pk (oracle g) = qFindRun (reduced S rand seeds F g) st pk := by
  let real := functions S g
  let ref : RandFns S.vp.params := { f₀ with thash := real.thash, hmsg := real.hmsg }
  let r := fun (k : PublicKeyCore (randPrims ref).core) => rand k.pkSeed k.pkRoot
  let r' := fun (k : PublicKeyCore (randPrims real).core) => rand k.pkSeed k.pkRoot
  let B := F.at (oracle g) (pureBytesAlg S.vp (randPrims ref) (SetOracle.codecFor S ref) r seeds)
  have tr := QInd.qFindRun_tr (prims := randPrims ref) real.prf real.prfMsg (SetOracle.codecFor S ref)
    r r' (fun _ => rfl) seeds B st pk
  refine Eq.trans ?_ tr.symm
  rw [qFindRun_eq_fRun]
  have hh : phaseMachine S f₀ rand F st pk (oracle g) = phaseMachine S ref rand F st pk (oracle g) := by qm_kernel_rfl
  rw [hh]
  unfold phaseMachine
  have interp : hashPort S ref (oracle g) = PublicHash.impl (randPrims ref) := by
    unfold hashPort
    rw [tablesOf_oracle]
    funext t
    cases t <;> rfl
  rw [interp, mainAt_eq S ref F rand seeds]

private noncomputable def tcrChoice : QTcrFV_Adversary (WS Input Output E) (baseProblem S seeds) where
  State := PhaseState S f₀
  choose := Open.forsPhase1 S.vp (randPrims f₀)
  forge := fun _ _ => pure (0,default)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private noncomputable def tcrEnd (H : Input → Output) (st : PhaseState S f₀) (pk : S.Node) :=
  phaseMachine S f₀ rand F st pk H >>= fun r => (liftU (pure (r.1.1,r.1.2)) : Closed (WS Input Output E) _)

private theorem tcr_eq (g : CompressionTables) :
    forsAdversary S seeds (tcrChoice S seeds F) (tcrEnd S rand F) g = qToTcr (reduced S rand seeds F g) := by
  have choose : (qToTcr (reduced S rand seeds F g)).choose = (tcrChoice S seeds F).choose := by
    refine (Open.toTcr_choose_eq (reduced S rand seeds F g).toClassical).trans ?_
    qm_kernel_rfl
  have forge : (qToTcr (reduced S rand seeds F g)).forge = tcrEnd S rand F (oracle g) := by
    funext (st : PhaseState S f₀) (pk : S.Node)
    exact congrArg (fun P : Closed (WS Input Output E) ((ℕ × S.Node) × List ℕ) =>
      P >>= fun r => (liftU (pure (r.1.1,r.1.2)) : Closed (WS Input Output E) _))
      (phase_oracle S rand seeds F g st pk).symm
  exact congrArg₂ (fun ch fo => (⟨PhaseState S f₀, ch, fo, F.ρ₀, F.posSemidef, F.trace_eq_one⟩ :
    QTcrFV_Adversary (WS Input Output E) (forsProblem S g seeds))) choose.symm forge.symm

theorem fors_tcr_reduction (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ g : CompressionTables, unifW _ g * qTcrFV_Advantage (qToTcr (reduced S rand seeds F g))) ≤
      (2*(forsBudget S c.ml q qs : ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  simp_rw [← tcr_eq S rand seeds F]
  apply fors_tcr_port
  intro st pk
  have h := PUE.bind (q₂ := 0) (phaseMachine_pue S f₀ rand F c st pk q qs hq hs hc)
    (B := fun r _ => (pure (r.1.1,r.1.2) : Closed (WS Input Output E) _)) fun r => PUE.pure _ 0
  simpa [tcrEnd] using h

private noncomputable def dsprChoice : QDsprFV_Adversary (WS Input Output E) (SM_DT_DSPR_SourceFinalValidity.Problem.standalone (baseProblem S seeds).th (openPreTargets S.vp)) where
  State := PhaseState S f₀
  choose := Open.forsPhase1 S.vp (randPrims f₀)
  guess := fun _ _ => pure (0,false)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private noncomputable def dsprEnd (H : Input → Output) (st : PhaseState S f₀) (pk : S.Node) :=
  phaseMachine S f₀ rand F st pk H >>= fun r => (liftU (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨ r.1.1 ∈ r.2))) : Closed (WS Input Output E) _)

private theorem dspr_eq (g : CompressionTables) :
    dsprAdversary S seeds (dsprChoice S seeds F) (dsprEnd S rand F) g = qToDspr (reduced S rand seeds F g) := by
  have choose : (qToDspr (reduced S rand seeds F g)).choose = (dsprChoice S seeds F).choose := by
    refine (Open.toDspr_choose_eq (reduced S rand seeds F g).toClassical).trans ?_
    qm_kernel_rfl
  have forge : (qToDspr (reduced S rand seeds F g)).guess = dsprEnd S rand F (oracle g) := by
    funext (st : PhaseState S f₀) (pk : S.Node)
    exact congrArg (fun P : Closed (WS Input Output E) ((ℕ × S.Node) × List ℕ) =>
      P >>= fun r => (liftU (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨ r.1.1 ∈ r.2))) : Closed (WS Input Output E) _))
      (phase_oracle S rand seeds F g st pk).symm
  exact congrArg₂ (fun ch fo => (⟨PhaseState S f₀, ch, fo, F.ρ₀, F.posSemidef, F.trace_eq_one⟩ :
    QDsprFV_Adversary (WS Input Output E) (dsprProblem S g seeds))) choose.symm forge.symm

theorem fors_dspr_reduction (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ g : CompressionTables, unifW _ g * qDsprFV_Success (qToDspr (reduced S rand seeds F g))) ≤
      (∑ g : CompressionTables, unifW _ g * qDsprFV_SPProbability (qToDspr (reduced S rand seeds F g))) +
      ENNReal.ofReal (168*(forsBudget S c.ml q qs : ℝ)^2 / 2^(8*S.vp.params.n)) := by
  simp_rw [← dspr_eq S rand seeds F]
  apply fors_dspr_port
  intro st pk
  have h := PUE.bind (q₂ := 0) (phaseMachine_pue S f₀ rand F c st pk q qs hq hs hc)
    (B := fun r _ => (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨ r.1.1 ∈ r.2)) : Closed (WS Input Output E) _)) fun r => PUE.pure _ 0
  simpa [dsprEnd] using h

end Reduction.Compression
#print axioms Reduction.Compression.fors_tcr_reduction
#print axioms Reduction.Compression.fors_dspr_reduction
