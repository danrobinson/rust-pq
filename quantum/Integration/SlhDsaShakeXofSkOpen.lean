import Integration.SlhDsaShakePermutationHonestBudget
import Integration.SlhDsaShakeApiSkBound

namespace Reduction.ShakeApi.Sk.Mixed
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg
open ShakePermutation.Honest (RawSpec readRaw hashWeight)
open Compression.SkGame (answerImpl ans_bind ans_classical ans_wrap answer_uniform)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => primitives S base
local notation "PS" => PSpec P₀ (S.Node × Adrs)
local notation "Raw" => RawSpec S N

def rawPublic (i : (publicHashSpec (P₀).core).Domain) : OracleComp Raw ((publicHashSpec (P₀).core).Range i) :=
  ShakePermutation.Honest.rawHash S N base (.inl i)

def rawHandler (a : S.Node × Adrs → S.Node) : QueryImpl PS (OracleComp Raw)
  | .inl n => liftM ((Raw).query (.inl n))
  | .inr (.inl d) => pure (a d)
  | .inr (.inr (.inl t)) => rawPublic S N base t
  | .inr (.inr (.inr (k,r,m))) => prefixBytes _ <$> readRaw S N (k.toList ++ r.toList ++ m)

theorem public_eval (H : RawTable S N) (i) : simulateQ (answerImpl H) (rawPublic S N base i) =
    pure (hashPort S N base H i) := by
  cases i <;> simp only [rawPublic,ShakePermutation.Honest.rawHash,simulateQ_map,
    ShakePermutation.Honest.runRead,map_pure] <;> rfl

theorem handler_eval (a : S.Node × Adrs → S.Node) (H : RawTable S N) {α : Type} (P : OracleComp PS α) :
    simulateQ (answerImpl H) (simulateQ (rawHandler S N base a) P) = simulateQ (Sk.handler S N base a H) P := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  rintro (n|d|t|⟨k,r,m⟩)
  · exact simulateQ_spec_query _ _
  · rfl
  · exact public_eval S N base H t
  · simp only [rawHandler,simulateQ_map,ShakePermutation.Honest.runRead,map_pure]; rfl

theorem read_count (xs : List SLHDSA.Byte) : WCount hashWeight (readRaw S N xs) 1 := by
  unfold readRaw
  split
  · exact wCount_liftM_query _ _ le_rfl
  · trivial

theorem public_count (i) : WCount hashWeight (rawPublic S N base i) 1 := by
  cases i with
  | thash pk a xs => exact WCount.map (read_count S N _) _
  | hmsg r pk root m => exact read_count S N _

private theorem handler_count {α : Type} (a : S.Node × Adrs → S.Node) (P : OracleComp PS α) (q p : ℕ)
    (hh : IsQueryBoundP P (fun t => hkind t = .hash) q) (hm : IsQueryBoundP P (fun t => hkind t = .prfmsg) p) :
    WCount hashWeight (simulateQ (rawHandler S N base a) P) (q+p) := by
  refine WCount.simulateQ _ ?_ (wCount_of_isQueryBoundP _ _ _ (hh.or hm))
  rintro (n|d|t|⟨k,r,m⟩)
  · exact wCount_liftM_query _ _ le_rfl
  · trivial
  · exact public_count S N base t
  · exact WCount.map (read_count S N _) _

theorem key_count (a : S.Node × Adrs → S.Node) (pk : S.Node) :
    WCount hashWeight (simulateQ (rawHandler S N base a) (openKeygenP (vp := S.vp) P₀ pk)) (Lazy.keygenHashes S.vp) := by
  rw [← Nat.add_zero (Lazy.keygenHashes S.vp)]
  apply handler_count
  · exact (openKeygenP_kindBound (vp := S.vp) (prims := P₀) .hash pk).mono
      (by simpa [hind] using Lazy.keygenB_hash (vp := S.vp))
  · exact (openKeygenP_kindBound (vp := S.vp) (prims := P₀) .prfmsg pk).mono
      (by change Lazy.keygenB S.vp 0 0 ≤ 0; cases S <;> decide)

theorem sign_count (a : S.Node × Adrs → S.Node) (r : PublicKeyCore (P₀).core → ProbComp S.Node)
    (pk : PublicKeyCore (P₀).core) (sk : S.Node) (m : List SLHDSA.Byte) :
    WCount hashWeight (simulateQ (rawHandler S N base a) (openSignP (vp := S.vp) r pk sk m)) (Lazy.signHashes S.vp + 1) := by
  apply handler_count
  · exact (openSignP_kindBound (vp := S.vp) (prims := P₀) (optRand := r) .hash (by decide) pk sk m).mono
      (by simpa [hind] using Lazy.signB_hash (vp := S.vp))
  · exact (openSignP_kindBound (vp := S.vp) (prims := P₀) (optRand := r) .prfmsg (by decide) pk sk m).mono
      (by change 1 + Lazy.signB S.vp 0 0 ≤ 1; cases S <;> decide)

theorem check_count (pk : PublicKeyCore (P₀).core)
    (z : List SLHDSA.Byte × GeneralScheme.SignatureCore S.vp (P₀).core) (log : SigLog S.vp P₀) :
    WCount hashWeight (simulateQ (rawPublic S N base) (sufCheckOpen pk z log)) (1+Resources2.verifyHashes S.vp) := by
  apply WCount.simulateQ (w := fun _ => 1) _ (public_count S N base)
  simpa only [ite_true] using wCount_of_isQueryBoundP (fun _ => True) _ _ (sufCheckOpen_bound pk z log)

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)
local notation "Work" => WS (Input N) (Bytes S.vp.params.m) E

noncomputable def signer (a : S.Node × Adrs → S.Node) (pk root sk : S.Node) :
    QueryImpl (unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core))
      (StateT (SigLog S.vp P₀) (OracleComp Raw)) :=
  (QueryImpl.ofLift unifSpec (OracleComp Raw)).liftTarget (StateT (SigLog S.vp P₀) (OracleComp Raw)) +
    sigSignOracle (vp := S.vp) (prims := P₀) (fun m => simulateQ (rawHandler S N base a)
      (openSignP (signRand S rand base) ⟨pk,root⟩ sk m))

noncomputable def body (a : S.Node × Adrs → S.Node) (pk : S.Node) (H : RawTable S N) :
    QOC Work Raw Bool := do
  let sk ← liftQ (liftM ($ᵗ S.Node : ProbComp S.Node))
  let root ← liftQ (simulateQ (rawHandler S N base a) (openKeygenP (vp := S.vp) P₀ pk))
  let z ← wrap (signer S N base rand a pk root sk) (qmForger S N F base H ⟨pk,root⟩) []
  liftQ (simulateQ (rawPublic S N base) (sufCheckOpen ⟨pk,root⟩ z.1 z.2))

theorem body_eval (a : S.Node × Adrs → S.Node) (pk : S.Node) (H : RawTable S N) :
    ansRun H (body S N base rand F a pk H) = Sk.answered S N base rand a F pk H := by
  unfold body Sk.answered
  rw [ans_bind,ans_classical,answer_uniform]
  apply bind_congr
  intro sk
  rw [ans_bind,ans_classical,handler_eval]
  apply bind_congr
  intro root
  rw [ans_bind,ans_wrap]
  congr 1
  · congr 1
    funext t log
    rcases t with n|m
    · simp only [signer,Sk.signer,QueryImpl.add_apply_inl,QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply]
      change simulateQ (answerImpl H) ((fun x => (x,log)) <$> liftM ((Raw).query (.inl n))) = _
      rw [simulateQ_map,simulateQ_spec_query]
      rfl
    · simp only [signer,Sk.signer,QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply,
        simulateQ_bind,simulateQ_pure]
      dsimp only [StateT.mk]
      rw [handler_eval]
      exact (run_appendLog_apply (loggedSpec := List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core)
        (fun u => simulateQ (Sk.handler S N base a H) (openSignP (signRand S rand base) ⟨pk,root⟩ sk u)) m log).symm
  · funext z
    rw [ans_classical]
    congr 1
    exact QueryImpl.simulateQ_simulateQ_eq_of_apply (public_eval S N base H) _

def total (a : S.Node × SkAdrs S.vp → S.Node) (d : S.Node × Adrs) : S.Node :=
  if h : SkDom S.vp d.2 then a (d.1,⟨d.2,h⟩) else default

noncomputable def machine (a : S.Node × SkAdrs S.vp → S.Node) (H : RawTable S N) : QOC Work Raw Bool :=
  liftQ (liftM seeds : OracleComp Raw S.Node) >>= fun pk => body S N (fun _ => default) rand F (total S a) pk H

theorem represented (a : S.Node × SkAdrs S.vp → S.Node) (H : RawTable S N) :
    ansRun H (machine S N rand seeds F a H) =
      ansRun a (qbPrfWC sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))) := by
  rw [machine,ans_bind,ans_classical,answer_uniform,Compression.SkGame.qbPrfWC_draw,
    Compression.drawThen,ans_bind,ans_classical,answer_uniform]
  apply bind_congr
  intro pk
  unfold Compression.SkGame.checkedBody
  rw [body_eval,← ansRun_restrict _ (total S a) a (fun d => by by_cases h : SkDom S.vp d.2 <;> simp [total,skRestrict,h])]
  exact ((Sk.answer_body S N rand seeds F H (total S a) pk).trans (Sk.answered_eq S N rand F _ H (total S a) pk)).symm

end Reduction.ShakeApi.Sk.Mixed
#print axioms Reduction.ShakeApi.Sk.Mixed.represented
