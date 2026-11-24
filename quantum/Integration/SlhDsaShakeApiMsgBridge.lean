import Integration.SlhDsaShakeApiMsgMachine
import Integration.SlhDsaShakeXofPrf
import Integration.SlhDsaCompressionHmacSignature

namespace Reduction.ShakeApi.Msg
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ)
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)
set_option maxHeartbeats 1300000 in
theorem machine_oracle (base : Xof S) (H : RawTable S N) :
    machine S N base rand seeds F H = qbPrfMsgWL sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H)) := by
  let real := primitives S (extend H)
  let P := {primitives S base with Thash := real.Thash, Hmsg := real.Hmsg}
  let c := codec S base
  let r := fun (k : PublicKeyCore P.core) => rand k.pkSeed k.pkRoot
  let r' := fun (k : PublicKeyCore real.core) => rand k.pkSeed k.pkRoot
  let B := F.at H (pureBytesAlg S.vp P c r seeds)
  have hp : hashPort S N base H = PublicHash.impl P := by funext t; cases t <;> rfl
  have hm : machine S N base rand seeds F H = qbPrfMsgWL sufCheck (qPureBytesToInternal B) := by
    unfold machine qbPrfMsgWL
    rw [hp]
    congr 1
    unfold openMachine qMsgOpenW
    apply bind_congr
    intro pk
    apply bind_congr
    intro root
    unfold qRunForgerSig
    have main : (qPureBytesToInternal B).main = qmForger S N F base H := by
      funext pk
      simp only [B,qPureBytesToInternal,qToInternal,qPureBytesToTyped,QForger.wrapForger,
        PortForger.at,qmCSign_eq,qmCRead_eq,pureBytesView]
      rfl
    rw [main]
    apply bind_congr
    intro z
    simp only [liftQ_pure]
    unfold verdict
    rw [hp]
    kexact congrArg (fun b : Bool => (pure b : QOC (WS (Input N) (Bytes S.vp.params.m) E)
      (Lazy.OSpec P (Lazy.msgG P)) Bool)) (sufCheckOpen_eq (prims := P) ⟨pk,root⟩ z.1 z.2)
  refine hm.trans ?_
  have tr := QMsg.qbPrfMsgWL_setPrf (prims := P) real.PRF real.PRFmsg c r r' (fun _ => rfl) seeds B
  kexact tr.symm

/-- Restriction preserves the real experiment when it agrees on each reached query. -/
private theorem run_short {D D' R W α : Type} [Fintype W] [Inhabited R] (r : D → Option D')
    (f : D → R) (g : D' → R) (Q : QOC W (PRFScheme.PRFOracleSpec D R) α)
    (hQ : AllQueries (InDom (W := W) (R := R) r) (fun _ => True) Q)
    (h : ∀ d z, r d = some z → f d = g z) :
    ansRun f Q = ansRun g (wrap0 (Restrict.restrictImpl r) Q) := by
  induction Q using OracleComp.inductionOn with
  | pure a => simp [ansRun_pure]
  | query_bind t k ih =>
    rcases t with j|n|d
    · rw [wrap0_instr_bind,ansRun_instr,ansRun_instr]
      exact bind_congr fun i => ih i (hQ.2 i)
    · rw [wrap0_query_bind,liftQ_restrict_unif,ansRun_unif,ansRun_unif]
      exact bind_congr fun i => ih i (hQ.2 i)
    · rcases hr : r d with _|z
      · have he : (r d).isSome := hQ.1
        simp [hr] at he
      · rw [wrap0_query_bind, liftQ_restrict_some r d z hr,ansRun_oracle,ansRun_oracle,h d z hr]
        exact ih _ (hQ.2 _)

private theorem restrict_inj (c : Caps) (d₁ d₂ : S.Node × List SLHDSA.Byte) (z : SetOracle.MessageDomain S c)
    (h₁ : SetOracle.restrictMessage S c d₁ = some z) (h₂ : SetOracle.restrictMessage S c d₂ = some z) : d₁ = d₂ := by
  unfold SetOracle.restrictMessage at h₁ h₂
  split_ifs at h₁ h₂ with e₁ e₂
  cases h₁
  obtain ⟨a,b⟩ := d₁
  obtain ⟨a',b'⟩ := d₂
  obtain ⟨h,h'⟩ := Prod.mk.inj (Option.some.inj h₂)
  have hb := congrArg (fun x : BList SLHDSA.Byte c.ml => List.ofFn x.2) h'.symm
  exact Prod.ext h.symm (by simpa only [BList.ofFn_ofList] using hb)

/-- Restricting the PRF challenge domain to the capped encoded messages
preserves both probabilities of the actual signature distinguisher. -/
theorem capped_games (c : Caps)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (H : RawTable S N) :
    let P := primitives S (extend H)
    let A := qbPrfMsgWL sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    let short := wrap0 (Restrict.restrictImpl (SetOracle.restrictMessage S c)) A
    qPrfRealPr (msgPrf S.vp P) A F.ρ₀ = qPrfRealPr (ShakeXof.boundedMsgScheme (L := c.ml) S H) short F.ρ₀ ∧
      qPrfIdealPr A F.ρ₀ = qPrfIdealPr short F.ρ₀ := by
  intro P A short
  let res := SetOracle.restrictMessage S c
  have dom : AllQueries (InDom (R := S.Node) res) (fun _ => True) A := by
    apply allQ_mono _ (fun _ _ => trivial) (allQ_qLazyRun (W := WS (Input N) (Bytes S.vp.params.m) E)
      (PublicHash.impl P) (fun d : S.Node × List SLHDSA.Byte => d.2.length ≤ c.ml) _
      (allQ_qMsgOpenW P c.ml sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
        (allQ_qPureBytesToInternal c.ml _ fun pk => allQ_compileQ c _ (F.main pk) (hcap pk))))
    rintro (j|n|d) ht
    · trivial
    · trivial
    · have hd : d.2.length ≤ c.ml := ht
      change (SetOracle.restrictMessage S c d).isSome
      simp [SetOracle.restrictMessage,hd]
  constructor
  · unfold qPrfRealPr qPrfRealExperiment
    congr 2
    funext k
    apply run_short res _ _ _ dom
    rintro ⟨r,m⟩ ⟨z,b⟩ hz
    unfold res SetOracle.restrictMessage at hz
    split_ifs at hz with hl
    cases hz
    simp [P,BList.ofFn_ofList]
  · exact qPrfIdealPr_restrict res (restrict_inj S c) _ dom _

theorem real_le_ideal (c : Caps) (cap : 2*S.vp.params.n+c.ml ≤ N)
    (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let P := fun H : RawTable S N => primitives S (extend H)
    let A := fun H : RawTable S N => qbPrfMsgWL sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    SetOracle.uniformMean (fun H => qPrfRealPr (msgPrf S.vp (P H)) (A H) F.ρ₀) ≤
      SetOracle.uniformMean (fun H => qPrfIdealPr (A H) F.ρ₀) +
        ENNReal.ofReal (8*(budget S q qs : ℝ)^2 / 2^(8*S.vp.params.n)) := by
  intro P A
  let res := SetOracle.restrictMessage S c
  let base : Xof S := fun _ => default
  let short : RawTable S N → QOC (WS (Input N) (Bytes S.vp.params.m) E)
      (PRFScheme.PRFOracleSpec (ShakeXof.MsgDomain S c.ml) S.Node) Bool := fun H => wrap0 (Restrict.restrictImpl res) (A H)
  have hpu : PUE (fun _ => 0) short (budget S q qs) := by
    have same : A = machine S N base rand seeds F := funext fun H => (machine_oracle S N rand seeds F base H).symm
    unfold short
    rw [same]
    exact PUE.wrap0 _ (fun t => wCount_zero _ _) (machine_cost S N base rand seeds F q qs hq hs)
  have games := capped_games S N rand seeds F c hcap
  have hr (H) := (games H).1
  have hi (H) := (games H).2
  change (SetOracle.uniformMean fun H => qPrfRealPr (msgPrf S.vp (P H)) (A H) F.ρ₀) ≤ _
  change ∀ H, qPrfRealPr (msgPrf S.vp (P H)) (A H) F.ρ₀ = qPrfRealPr (ShakeXof.boundedMsgScheme S H) (short H) F.ρ₀ at hr
  change ∀ H, qPrfIdealPr (A H) F.ρ₀ = qPrfIdealPr (short H) F.ρ₀ at hi
  simp_rw [hr,hi]
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input N × Bytes S.vp.params.m) × E) F.ρ₀ F.posSemidef F.trace_eq_one
  rw [hρ]
  exact ShakeXof.msg_prf S cap short _ hpu.prfAnswerCost ρ

end Reduction.ShakeApi.Msg
#print axioms Reduction.ShakeApi.Msg.real_le_ideal
