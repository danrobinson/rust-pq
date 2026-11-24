import Integration.SlhDsaShakeApiSkMachine

namespace Reduction.ShakeApi.Sk
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg Ideal.Transport
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
open Compression.SkGame (answerImpl ans_bind ans_classical answer_uniform ans_wrap body)
variable (S : Sha2Set) (N : ℕ)
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)

theorem answer_open (H : RawTable S N) (a : S.Node × Adrs → S.Node) {α : Type}
    (P : OracleComp (PSpec (primitives S (extend H)) (S.Node × Adrs)) α) :
    simulateQ (answerImpl a) (simulateQ (Open.closeImpl _ _) P) =
      simulateQ (handler S N (extend H) a H) P := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  rintro (n|d|t|m)
  · apply answer_uniform
  · change simulateQ (answerImpl a) (liftM ((PRFScheme.PRFOracleSpec (S.Node × Adrs) S.Node).query (.inr d))) = _
    rw [simulateQ_spec_query]
    rfl
  · rw [show Open.closeImpl _ _ (.inr (.inr (.inl t))) = pure _ from rfl,simulateQ_pure]
    cases t <;> rfl
  · rw [show Open.closeImpl _ _ (.inr (.inr (.inr m))) = pure _ from rfl,simulateQ_pure]
    rfl

theorem answer_body (H : RawTable S N) (a : S.Node × Adrs → S.Node) (pk : S.Node) :
    ansRun a (body sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H)) pk) =
      answered S N (extend H) rand a F pk H := by
  let P := primitives S (extend H)
  let r := signRand S rand (extend H)
  unfold body answered
  rw [ans_bind,ans_classical,answer_uniform]
  refine bind_congr fun sk => ?_
  rw [ans_bind,ans_classical,← close_openKeygenP,answer_open]
  refine bind_congr fun root => ?_
  rw [ans_bind]
  unfold qRunForgerSig
  rw [ans_wrap,internal_main]
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
      exact (run_appendLog_apply (loggedSpec := List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp P.core)
        (fun m => simulateQ (handler S N (extend H) a H) (openSignP r ⟨pk,root⟩ sk m)) m log).symm
  · funext z
    rw [liftQ_pure,ansRun_pure]
    have hh : (fun t => pure (hashPort S N (extend H) H t) : QueryImpl _ ProbComp) =
        (PublicHash.impl P).liftTarget ProbComp := by
      funext t
      cases t <;> rfl
    rw [hh,simulateQ_liftTarget,sufCheckOpen_eq]
    rfl

theorem main_eq_any (base : Xof S) (H : RawTable S N) :
    (qPureBytesToInternal (forgerAt S rand seeds F base H)).main =
      qmForger S N F base H := by
  funext pk
  simp only [forgerAt,scheme,qPureBytesToInternal,qToInternal,qPureBytesToTyped,QForger.wrapForger,
    PortForger.at,qmCSign_eq,qmCRead_eq,pureBytesView]
  rfl

set_option maxHeartbeats 2500000 in
/-- With explicit interfaces for every honest hash, the closed branch has the same
output for either choice of the secret functions stored in the core's type. -/
theorem answered_eq (base : Xof S) (H : RawTable S N) (a : S.Node × Adrs → S.Node) (pk : S.Node) :
    answered S N (extend H) rand a F pk H = answered S N base rand a F pk H := by
  let real := primitives S (extend H)
  let P := { primitives S base with Thash := real.Thash, Hmsg := real.Hmsg }
  let pr : S.Node → S.Node → Adrs → S.Node := real.PRF
  let pm : S.Node → S.Node → List SLHDSA.Byte → S.Node := real.PRFmsg
  let r := fun (k : PublicKeyCore P.core) => rand k.pkSeed k.pkRoot
  let r' := fun (k : PublicKeyCore (setPrfC P.core pr pm)) => rand k.pkSeed k.pkRoot
  let c := codec S base
  let seed : ProbComp S.Node := pure pk
  let B := F.at H (pureBytesAlg S.vp P c r seed)
  unfold answered
  apply bind_congr
  intro sk
  refine bind_congr_k (by qm_kernel_rfl) fun root => ?_
  let sign (m : List SLHDSA.Byte) := simulateQ (handler S N base a H) (openSignP (vp := S.vp) r ⟨pk,root⟩ sk m)
  let sign' (m : List SLHDSA.Byte) := simulateQ (handler S N (extend H) a H) (openSignP (vp := S.vp) r' ⟨pk,root⟩ sk m)
  have hs (m) : sign' m = trSig P.core pr pm <$> sign m := by
    have h := Realize.Prf.openSignP_tr P pr pm r r' (fun _ => rfl) ⟨pk,root⟩ sk m
    have h' := congrArg (simulateQ (handler S N (extend H) a H)) h
    rw [simulateQ_map] at h'
    kexact h'
  let log := trLog (vp := S.vp) (prims := P) pr pm
  have step (m) (s : SigLog S.vp P) :
      (sigSignOracle sign' m).run (log s) =
        (fun z => (trSig P.core pr pm z.1,log z.2)) <$> (sigSignOracle sign m).run s := by
    simp only [sigSignOracle,run_appendLog_apply,hs,bind_map_left,map_bind,map_pure]
    apply bind_congr
    intro sig
    simp [log,trLog]
  have tr := QInd.close_qPureBytesToInternal_tr (prims := P) pr pm c r r' seed log B
    (sigSignOracle sign) (sigSignOracle sign') step ⟨pk,root⟩ []
  rw [← main_eq_any S N rand seed F base H,← main_eq_any S N rand seed F (extend H) H]
  refine (bind_congr_k tr fun _ => rfl).trans ?_
  rw [bind_map_left]
  apply bind_congr
  intro z
  have hb : (fun t => pure (hashPort S N base H t) : QueryImpl _ ProbComp) = (PublicHash.impl P).liftTarget ProbComp := by
    funext t; cases t <;> rfl
  have hr : (fun t => pure (hashPort S N (extend H) H t) : QueryImpl _ ProbComp) =
      (PublicHash.impl real).liftTarget ProbComp := by funext t; cases t <;> rfl
  rw [hb,hr,simulateQ_liftTarget,simulateQ_liftTarget,sufCheckOpen_eq]
  kexact congrArg (fun b : Bool => liftU (W := WS (Input N) (Bytes S.vp.params.m) E) (pure b : ProbComp Bool)) ((sufCheck_setPrf P pr pm ⟨pk,root⟩ z.1 z.2).trans
    (sufCheckOpen_eq (prims := P) ⟨pk,root⟩ z.1 z.2).symm)

end Reduction.ShakeApi.Sk
#print axioms Reduction.ShakeApi.Sk.answer_body
#print axioms Reduction.ShakeApi.Sk.answered_eq
