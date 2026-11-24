import Integration.SlhDsaCompressionPrfInterp
import Integration.SlhDsaCompressionWotsTransport
import Ideal.Realize.PrfTr

namespace Reduction.Compression.SkGame
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg Ideal.Transport
open scoped Kronecker
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

theorem answered_eq (H : Input → Output) (a : S.Node × Adrs → S.Node) (pk : S.Node) :
    answered S (functions S (tablesOf H)) rand a F pk H = answered S (carrier S) rand a F pk H := by
  let real := functions S (tablesOf H)
  let base := {carrier S with thash := real.thash, hmsg := real.hmsg}
  let P := randPrims base
  let r := fun (k : PublicKeyCore P.core) => rand k.pkSeed k.pkRoot
  let r' := fun (k : PublicKeyCore (setPrfC P.core real.prf real.prfMsg)) => rand k.pkSeed k.pkRoot
  let codec := SetOracle.codecFor S base
  let seed : ProbComp S.Node := pure pk
  let B := F.at H (pureBytesAlg S.vp P codec r seed)
  rw [answered_carrier S rand F a pk H real]
  unfold answered
  apply bind_congr
  intro sk
  refine bind_congr_k (by qm_kernel_rfl) fun root => ?_
  let sign (m : List Byte) := simulateQ (handler S base a H) (openSignP (vp := S.vp) r ⟨pk,root⟩ sk m)
  let sign' (m : List Byte) := simulateQ (handler S real a H)
    (openSignP (vp := S.vp) (prims := randPrims real) (fun k => rand k.pkSeed k.pkRoot) ⟨pk,root⟩ sk m)
  have hs (m) : sign' m = trSig _ real.prf real.prfMsg <$> sign m := by
    have h := Realize.Prf.openSignP_tr P real.prf real.prfMsg r r' (fun _ => rfl) ⟨pk,root⟩ sk m
    have h' := congrArg (simulateQ (handler S real a H)) h
    rw [simulateQ_map] at h'
    kexact h'
  let log := trLog (vp := S.vp) (prims := P) real.prf real.prfMsg
  have step (m) (s : SigLog S.vp P) :
      (sigSignOracle sign' m).run (log s) =
        (fun z => (trSig _ real.prf real.prfMsg z.1,log z.2)) <$> (sigSignOracle sign m).run s := by
    simp only [sigSignOracle,run_appendLog_apply,hs,bind_map_left,map_bind,map_pure]
    apply bind_congr
    intro sig
    simp [log,trLog]
    rfl
  have tr := QInd.close_qPureBytesToInternal_tr real.prf real.prfMsg codec r r' seed log B
    (sigSignOracle sign) (sigSignOracle sign') step ⟨pk,root⟩ []
  rw [mainAt_eq S base F rand seed,mainAt_eq S real F rand seed]
  refine (bind_congr_k tr fun _ => rfl).trans ?_
  rw [bind_map_left]
  apply bind_congr
  intro z
  have hb : (fun t => pure (hashPort S base H t) : QueryImpl _ ProbComp) = (PublicHash.impl P).liftTarget ProbComp := by
    funext t; cases t <;> rfl
  have hr : (fun t => pure (hashPort S real H t) : QueryImpl _ ProbComp) =
      (PublicHash.impl (randPrims real)).liftTarget ProbComp := by funext t; cases t <;> rfl
  rw [hb,hr,simulateQ_liftTarget,simulateQ_liftTarget,sufCheckOpen_eq,sufCheckOpen_eq]
  exact congrArg (fun b : Bool => liftU (pure b : ProbComp Bool)) (sufCheck_setPrf P real.prf real.prfMsg ⟨pk,root⟩ z.1 z.2)

variable (seeds : ProbComp S.Node)

theorem machine_budget (c : Caps) (pk : S.Node) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PrfAnswerCost (machine S rand seeds F pk) (budget S c.ml q qs) := by
  intro a
  let total := fun d => ((skRestrict S.vp (randPrims (carrier S)) d).map (fun p => a p.2)).getD default
  have same : (fun H => ansRun a (machine S rand seeds F pk H)) =
      answered S (carrier S) rand total F pk := by
    funext H
    let f := functions S (tablesOf H)
    let B := F.at H (pureBytesAlg S.vp (randPrims f) (SetOracle.codecFor S f)
      (fun k => rand k.pkSeed k.pkRoot) seeds)
    refine (ans_project sufCheck (qPureBytesToInternal B) pk a).trans ?_
    exact (answer_body S rand seeds F H total pk).trans (answered_eq S rand F H total pk)
  rw [same]
  exact answered_cost S (carrier S) rand total F c pk q qs hq hs hc

/-- Secret-address PRF contribution to the signature bound for all six parameter sets.
Only the byte forger's own query and message limits are hypotheses. -/
theorem real_le_ideal_budget (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let Q := fun g => reduced S rand seeds F g
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (skPrfC S.vp (randPrims (functions S g)))
      (qbPrfWC sufCheck (Q g)) F.ρ₀) ≤
      (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (qbPrfWC sufCheck (Q g)) F.ρ₀) +
        ENNReal.ofReal (8*(budget S c.ml q qs : ℝ)^2 / 2^(8*S.vp.params.n)) :=
  real_le_ideal S rand seeds F _ (fun pk => machine_budget S rand F seeds c pk q qs hq hs hc)

end Reduction.Compression.SkGame
#print axioms Reduction.Compression.SkGame.answered_eq
#print axioms Reduction.Compression.SkGame.real_le_ideal_budget
