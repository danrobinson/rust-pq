import Integration.SlhDsaShakeXofSkOpenCost
import Integration.SlhDsaShakeApiMsgBridge

namespace Reduction.ShakeApi.Msg.Mixed
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg Open
open ShakePermutation.Honest (RawSpec hashWeight)
open Compression.SkGame (answerImpl ans_bind ans_classical answer_uniform)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => primitives S base
local notation "Raw" => RawSpec S N
local notation "OS" => Lazy.OSpec P₀ (Lazy.msgG P₀)
local notation "OSU" => Lazy.RSpec (Lazy.msgG P₀) Unit S.Node (publicHashSpec (Primitives.core (primitives S base)))
local notation "Sig" => GeneralScheme.SignatureCore S.vp (Primitives.core (primitives S base))
local notation "PS" => PRFScheme.PRFOracleSpec (S.Node × List SLHDSA.Byte) S.Node

def rawEnd (a : S.Node × List SLHDSA.Byte → S.Node) : QueryImpl OSU (OracleComp Raw)
  | .inl n => liftM ((Raw).query (.inl n))
  | .inr (.inl d) => pure (a d)
  | .inr (.inr (.inl _)) => liftM ($ᵗ S.Node : ProbComp S.Node)
  | .inr (.inr (.inr h)) => Sk.Mixed.rawPublic S N base h

private theorem end_eq (a : S.Node × List SLHDSA.Byte → S.Node) (H : RawTable S N) (t : (OSU).Domain) :
    simulateQ (answerImpl H) (rawEnd S N base a t) =
      simulateQ (answerImpl a) ((Lazy.interp (hashPort S N base H) : QueryImpl OSU (OracleComp PS)) t) := by
  rcases t with n|d|u|h
  · simp only [rawEnd,Lazy.interp,simulateQ_spec_query]; rfl
  · simp only [rawEnd,Lazy.interp,simulateQ_pure,simulateQ_spec_query]; rfl
  · exact (answer_uniform H _).trans (answer_uniform a _).symm
  · exact (Sk.Mixed.public_eval S N base H h).trans (simulateQ_pure _ _).symm

private theorem answer_wrap0 {D D' V V' W α ι : Type} [Fintype W] {sp : OracleSpec ι}
    (a : D → V) (b : D' → V')
    (l : QueryImpl sp (OracleComp (PRFScheme.PRFOracleSpec D V)))
    (r : QueryImpl sp (OracleComp (PRFScheme.PRFOracleSpec D' V')))
    (h : ∀ t, simulateQ (answerImpl a) (l t) = simulateQ (answerImpl b) (r t)) (Q : QOC W sp α) :
    ansRun a (wrap0 l Q) = ansRun b (wrap0 r Q) := by
  induction Q using OracleComp.inductionOn with
  | pure x => simp [ansRun_pure]
  | query_bind t k ih =>
    rcases t with j|i
    · simp only [wrap0_instr_bind,ansRun_instr,ih]
    · simp only [wrap0_query_bind,ans_bind,ans_classical,h,ih]

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)
local notation "Work" => WS (Input N) (Bytes S.vp.params.m) E

abbrev Result := PublicKeyCore (P₀).core × ((List SLHDSA.Byte × Sig) × SigLog S.vp P₀)

noncomputable def beforeCheck (H : RawTable S N) : QOC Work OS (Result S base) := do
  let pk ← liftQ (liftM seeds : OracleComp OS S.Node)
  let root ← liftQ (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk)
  let z ← wrap (Msg.signImpl S base rand ⟨pk,root⟩) (qmForger S N F base H ⟨pk,root⟩) []
  pure (⟨pk,root⟩, z)

theorem factor_open (H : RawTable S N) : Msg.openMachine S N base rand seeds F H =
    (fun z : Result S base => Msg.verdict S N base H z.1 z.2) <$> beforeCheck S N base rand seeds F H := by
  simp only [Msg.openMachine,beforeCheck,map_bind,map_pure]

private theorem lazy_map {W : Type} [Fintype W] {α β : Type} (H : RawTable S N) (P : QOC W OS α) (f : α → β) :
    qLazyRun (hashPort S N base H) (f <$> P) = f <$> qLazyRun (hashPort S N base H) P := by
  unfold qLazyRun
  rw [QInd.wrap_map,Functor.map_map,QInd.wrap0_map,QInd.wrap0_map,Functor.map_map]

noncomputable def interpreted (a : S.Node × List SLHDSA.Byte → S.Node) (H : RawTable S N) : QOC Work Raw Bool := do
  let z ← wrap0 (rawEnd S N base a) (Prod.fst <$> wrap Lazy.lazyImplR (beforeCheck S N base rand seeds F H) [])
  liftQ (simulateQ (Sk.Mixed.rawPublic S N base) (sufCheckOpen z.1 z.2.1 z.2.2))

theorem interprets (a : S.Node × List SLHDSA.Byte → S.Node) (H : RawTable S N) :
    ansRun H (interpreted S N base rand seeds F a H) = ansRun a (Msg.machine S N base rand seeds F H) := by
  rw [Msg.machine,factor_open,lazy_map,interpreted,ans_bind]
  conv_rhs => rw [map_eq_bind_pure_comp,ans_bind]
  rw [answer_wrap0 H a _ (Lazy.interp (hashPort S N base H)) (end_eq S N base a H)]
  apply bind_congr
  intro z
  simp only [Function.comp_apply,ansRun_pure,ans_classical]
  have h := QueryImpl.simulateQ_simulateQ_eq_of_apply (Sk.Mixed.public_eval S N base H)
    (sufCheckOpen z.1 z.2.1 z.2.2)
  rw [h]
  change liftU (simulateQ ((hashPort S N base H).liftTarget ProbComp) _) = _
  rw [simulateQ_liftTarget]
  rfl

def total (c : Caps) (a : ShakeXof.MsgDomain S c.ml → S.Node) (d : S.Node × List SLHDSA.Byte) : S.Node :=
  match SetOracle.restrictMessage S c d with | some z => a z | none => default

noncomputable def machine (c : Caps) (a : ShakeXof.MsgDomain S c.ml → S.Node) (H : RawTable S N) :=
  interpreted S N (fun _ => default) rand seeds F (total S c a) H

theorem represented (c : Caps) (a : ShakeXof.MsgDomain S c.ml → S.Node) (H : RawTable S N) :
    ansRun H (machine S N rand seeds F c a H) =
      ansRun a (wrap0 (Restrict.restrictImpl (SetOracle.restrictMessage S c))
        (qbPrfMsgWL sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H)))) := by
  rw [machine,interprets,Msg.machine_oracle]
  exact ansRun_restrict (SetOracle.restrictMessage S c) (total S c a) a (fun d => by unfold total; cases SetOracle.restrictMessage S c d <;> rfl) _

end Reduction.ShakeApi.Msg.Mixed
#print axioms Reduction.ShakeApi.Msg.Mixed.represented
