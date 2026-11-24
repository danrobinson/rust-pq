import Integration.SlhDsaCompressionPrfMachine
import Integration.SlhDsaCompressionPrfRestrict

namespace Reduction.Compression.SkGame
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

/-- Answering a PRF after both address restrictions evaluates the unrestricted
signing branch with the corresponding total function. -/
theorem ans_project {vp : ValidatedParams} {prims : Primitives vp.params}
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
    [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
    [Inhabited prims.Y] [Fintype prims.Y] {W : Type} [Fintype W]
    {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}
    (w : WinCheck vp prims) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (pk : prims.PkSeed) (a : SkAdrs vp → prims.Y) :
    ansRun a (project (checkedBody w Q pk)) =
      ansRun (fun d => ((skRestrict vp prims d).map (fun p => a p.2)).getD default) (body w Q pk) := by
  unfold project checkedBody
  rw [← ansRun_restrict _ (fun d => a d.2) a (fun _ => rfl)]
  apply Eq.symm
  apply ansRun_restrict
  intro d
  cases skRestrict vp prims d <;> rfl

theorem answered_carrier (a : S.Node × Adrs → S.Node) (pk : S.Node) (H : Input → Output)
    (f : RandFns S.vp.params) :
    answered S (carrier S) rand a F pk H = answered S {carrier S with thash := f.thash, hmsg := f.hmsg} rand a F pk H := by
  qm_kernel_rfl

section Closed
variable {D R W α β : Type} [Fintype W] (a : D → R)
local notation "PS" => PRFScheme.PRFOracleSpec D R

def answerImpl : QueryImpl PS ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr d => pure (a d)

theorem ans_bind (Q : QOC W PS α) (k : α → QOC W PS β) :
    ansRun a (Q >>= k) = ansRun a Q >>= fun x => ansRun a (k x) := by
  induction Q using OracleComp.inductionOn with
  | pure x => simp [ansRun_pure]
  | query_bind t r ih =>
    rcases t with j|n|d
    · simp only [bind_assoc,ansRun_instr,ih]
    · simp only [bind_assoc,ansRun_unif,ih]
    · simp only [bind_assoc,ansRun_oracle,ih]

theorem ans_classical (P : OracleComp PS α) :
    ansRun (W := W) a (liftQ P) = liftU (simulateQ (answerImpl a) P) := by
  induction P using OracleComp.inductionOn with
  | pure x => simp [ansRun_pure]
  | query_bind t k ih =>
    rcases t with n|d
    · rw [liftQ_query_bind,ansRun_unif,simulateQ_bind,simulateQ_spec_query]
      simp only [answerImpl,ih]
      exact (liftU_query_bind n (fun x => simulateQ (answerImpl a) (k x))).symm
    · rw [liftQ_query_bind,ansRun_oracle,simulateQ_bind,simulateQ_spec_query]
      simp only [answerImpl,pure_bind,ih]

theorem answer_uniform (P : ProbComp α) :
    simulateQ (answerImpl a) (liftM P : OracleComp PS α) = P := by
  induction P using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n k ih =>
    rw [liftM_bind,simulateQ_bind]
    simp only [ih]
    apply congrArg (fun b => b >>= k)
    change simulateQ (answerImpl a) (liftM ((PS).query (.inl n))) = _
    rw [simulateQ_spec_query]
    rfl

theorem ans_wrap {ι σ : Type} {sp : OracleSpec ι} (I : QueryImpl sp (StateT σ (OracleComp PS)))
    (Q : QOC W sp α) (s : σ) :
    ansRun a (wrap I Q s) = close (fun t => StateT.mk fun st => simulateQ (answerImpl a) ((I t).run st)) Q s := by
  induction Q using OracleComp.inductionOn generalizing s with
  | pure x => simp [ansRun_pure]
  | query_bind t k ih =>
    rcases t with j|t
    · simp only [wrap_instr_bind,ansRun_instr,close_instr_bind,ih]
    · simp only [wrap_query_bind,ans_bind,ans_classical,close_query_bind,StateT.run_mk,ih]

end Closed

theorem answer_open (H : Input → Output) (a : S.Node × Adrs → S.Node) {α : Type}
    (P : OracleComp (PSpec (randPrims (functions S (tablesOf H))) (S.Node × Adrs)) α) :
    simulateQ (answerImpl a) (simulateQ (Open.closeImpl _ _) P) =
      simulateQ (handler S (functions S (tablesOf H)) a H) P := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  rintro (n|d|t|m)
  · apply answer_uniform
  · change simulateQ (answerImpl a) (liftM ((PRFScheme.PRFOracleSpec _ _).query (.inr d))) = _
    rw [simulateQ_spec_query]
    rfl
  · rw [show Open.closeImpl _ _ (.inr (.inr (.inl t))) = pure _ from rfl,simulateQ_pure]
    cases t <;> rfl
  · rw [show Open.closeImpl _ _ (.inr (.inr (.inr m))) = pure _ from rfl,simulateQ_pure]
    rfl

theorem answer_body (H : Input → Output) (a : S.Node × Adrs → S.Node) (pk : S.Node) :
    let f := functions S (tablesOf H)
    let B := F.at H (pureBytesAlg S.vp (randPrims f) (SetOracle.codecFor S f)
      (fun k => rand k.pkSeed k.pkRoot) seeds)
    ansRun a (body sufCheck (qPureBytesToInternal B) pk) = answered S f rand a F pk H := by
  dsimp only
  let f := functions S (tablesOf H)
  let P := randPrims f
  let r := fun (k : PublicKeyCore P.core) => rand k.pkSeed k.pkRoot
  let B := F.at H (pureBytesAlg S.vp P (SetOracle.codecFor S f) r seeds)
  change ansRun a (body sufCheck (qPureBytesToInternal B) pk) = answered S f rand a F pk H
  unfold body answered
  rw [ans_bind,ans_classical,answer_uniform]
  refine bind_congr fun sk => ?_
  rw [ans_bind,ans_classical,← close_openKeygenP,answer_open]
  refine bind_congr fun root => ?_
  rw [ans_bind]
  unfold qRunForgerSig
  rw [ans_wrap,mainAt_eq S f F rand seeds]
  congr 1
  · congr 1
    funext t log
    rcases t with n|m
    · change simulateQ (answerImpl a) ((liftM ((PRFScheme.PRFOracleSpec (S.Node × Adrs) S.Node).query (.inl n))) >>= fun u => pure (u,log)) = _
      rw [simulateQ_bind,simulateQ_spec_query]
      simp only [simulateQ_pure]
      rfl
    · change simulateQ (answerImpl a) ((sigSignOracle (bSignC r ⟨pk,root⟩ sk) m).run log) = _
      simp only [sigSignOracle,run_appendLog_apply,simulateQ_bind,simulateQ_pure]
      rw [← close_openSignP,answer_open]
      exact (run_appendLog_apply (loggedSpec := List Byte →ₒ GeneralScheme.SignatureCore S.vp P.core)
        (fun m => simulateQ (handler S f a H) (openSignP r ⟨pk,root⟩ sk m)) m log).symm
  · funext z
    rw [liftQ_pure,ansRun_pure]
    have hh : (fun t => pure (hashPort S f H t) : QueryImpl _ ProbComp) =
        (PublicHash.impl P).liftTarget ProbComp := by
      funext t
      cases t <;> rfl
    rw [hh,simulateQ_liftTarget,sufCheckOpen_eq]
    rfl

end Reduction.Compression.SkGame
#print axioms Reduction.Compression.SkGame.ans_project
#print axioms Reduction.Compression.SkGame.answered_carrier
#print axioms Reduction.Compression.SkGame.ans_wrap
#print axioms Reduction.Compression.SkGame.answer_body
