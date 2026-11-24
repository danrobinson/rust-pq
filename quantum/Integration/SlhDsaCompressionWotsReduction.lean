import Integration.SlhDsaCompressionWotsMachine
import Integration.SlhDsaCompressionWotsTransport
import Integration.SlhDsaCompressionForsReduction
import Integration.SlhDsaCompressionWotsTcr
import Integration.SlhDsaCompressionWotsUd

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash Resources2
attribute [local irreducible] wotsChainTargets wotsStepTargetsT
variable (S : Sha2Set)
local notation "f₀" => carrier S
local notation "P₀" => randPrims (carrier S)
private def ref (g : CompressionTables) : RandFns S.vp.params :=
  { carrier S with thash := (functions S g).thash, hmsg := (functions S g).hmsg }

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

private theorem wOracle {β : Type} (g : CompressionTables) (st : WState S f₀) (pk : S.Node)
    (post : WAnswer S f₀ → OracleComp (Lazy.OSpec P₀ []ₒ) β)
    (result : WAnswer S f₀ → β)
    (hpost : ∀ x, simulateQ (Lazy.tblImpl (gspec := []ₒ) (PublicHash.impl (randPrims (ref S g))) st.1)
      (post x) = pure (result x)) :
    wMachine S f₀ rand F st pk post (oracle g) =
      (qWotsForge (reduced S rand seeds F g) st pk >>= fun x => liftU (pure (result x))) := by
  let real := functions S g
  let r := fun (k : PublicKeyCore (randPrims (ref S g)).core) => rand k.pkSeed k.pkRoot
  let r' := fun (k : PublicKeyCore (randPrims real).core) => rand k.pkSeed k.pkRoot
  let codec := SetOracle.codecFor S (ref S g)
  let B := F.at (oracle g) (pureBytesAlg S.vp (randPrims (ref S g)) codec r seeds)
  have tr := QInd.qWotsForge_tr (prims := randPrims (ref S g)) real.prf real.prfMsg codec r r' seeds
    (fun _ => rfl) B st pk
  refine Eq.trans ?_ (congrArg (fun v : Closed (WS Input Output E) (WAnswer S f₀) =>
    v >>= fun x => (liftU (pure (result x)) : Closed (WS Input Output E) β)) tr.symm)
  have core := qWotsForge_post_eq r (qPureBytesToInternal B) st pk result post hpost
  refine Eq.trans ?_ core.symm
  have hh : wMachine S f₀ rand F st pk post (oracle g) =
      wMachine S (ref S g) rand F st pk post (oracle g) := by qm_kernel_rfl
  rw [hh]
  unfold wMachine
  have interp : hashPort S (ref S g) (oracle g) = PublicHash.impl (randPrims (ref S g)) := by
    unfold hashPort
    rw [tablesOf_oracle]
    funext t
    cases t <;> rfl
  rw [interp, mainAt_eq S (ref S g) F rand seeds]

noncomputable def preSelect : QSM_DT_PRE_Adversary (WS Input Output E) (basePre S seeds) where
  State := Open.RState S.vp P₀
  choose := Open.prePhase1 (vp := S.vp) (prims := P₀) seeds
  invert := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

noncomputable def preMachine (H : Input → Output) (st : Open.RState S.vp P₀) (pk : S.Node) :=
  wMachine S f₀ rand F st.1 pk (fun x => wotsPreAnswerO (prims := P₀) pk st.2 x.1 x.2.1 x.2.2) H

theorem preGame_eq (g : CompressionTables) :
    preAdversary S seeds (preSelect S seeds F) (preMachine S rand F) g = qrPre (reduced S rand seeds F g) := by
  let real := functions S g
  let hf : Open.HashFns P₀ := ⟨real.thash,real.hmsg,real.prf,real.prfMsg⟩
  have choose : (qrPre (reduced S rand seeds F g)).choose = (preSelect S seeds F).choose := by
    kexact Open.wotsPre_phase1_q1_zero (prims := P₀) (pkSeedDist := seeds) hf (reduced S rand seeds F g).toClassical
  have last : (qrPre (reduced S rand seeds F g)).invert = preMachine S rand F (oracle g) := by
    funext (st : Open.RState S.vp P₀) (pk : S.Node)
    kexact (wOracle S rand seeds F g st.1 pk
      (fun x => wotsPreAnswerO (prims := randPrims (ref S g)) pk st.2 x.1 x.2.1 x.2.2)
      (fun x => preAnswer (prims := randPrims (ref S g)) pk st.2 x.1 x.2.1 x.2.2)
      (fun x => wotsPreAnswerO_tbl (prims := randPrims (ref S g)) (gspec := []ₒ) st.1.1 pk st.2 x.1 x.2.1 x.2.2)).symm
  kexact congrArg₂ (fun ch fo => (⟨Open.RState S.vp P₀,ch,fo,F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
    QSM_DT_PRE_Adversary (WS Input Output E) (preProblem S seeds g))) choose.symm last.symm

theorem preMachine_budget (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => preMachine S rand F H st pk)
      (wotsBudget S c.ml q qs (wotsPreHashes S.vp)) := by
  intro st pk
  apply wMachine_pue S f₀ rand F c st.1 pk _ _ q qs _ _ hq hs hc
  · intro x
    exact (wotsPreAnswerO_kindBound (prims := P₀) .hash pk st.2 x.1 x.2.1 x.2.2).mono (by simp [Lazy.ind,wotsPreHashes])
  · intro x L
    exact Realize.Wots.pw_pre _ (okLength_cost S f₀ L) pk st.2 x.1 x.2.1 x.2.2

theorem wide_pre_reduction (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ g : CompressionTables, unifW _ g * qSM_DT_PRE_Advantage (qrPre (reduced S rand seeds F g))) ≤
      SetOracle.epsPreSet S (wotsBudget S c.ml q qs (wotsPreHashes S.vp)) := by
  simp_rw [← preGame_eq S rand seeds F]
  apply wide_pre_port _ _ _ _ hw
  exact preMachine_budget S rand F c q qs hq hs hc

noncomputable def chainTcrSelect : QSM_DT_TCR_Adversary (WS Input Output E) (baseWotsTcr S seeds) where
  State := Open.RState S.vp P₀
  choose := Open.wotsTcrPhase1 (vp := S.vp) (prims := P₀) seeds
  forge := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

noncomputable def chainTcrMachine (H : Input → Output) (st : Open.RState S.vp P₀) (pk : S.Node) :=
  wMachine S f₀ rand F st.1 pk (fun x => wotsTcrAnswerO (prims := P₀) pk st.2 x.1 x.2.1 x.2.2) H

theorem chainTcrGame_eq (g : CompressionTables) :
    chainTcrAdversary S seeds (chainTcrSelect S seeds F) (chainTcrMachine S rand F) g = qrTcrT (reduced S rand seeds F g) := by
  let real := functions S g
  let hf : Open.HashFns P₀ := ⟨real.thash,real.hmsg,real.prf,real.prfMsg⟩
  have choose : (qrTcrT (reduced S rand seeds F g)).choose = (chainTcrSelect S seeds F).choose := by
    kexact Open.wotsTcrT_phase1_q1_zero (prims := P₀) (pkSeedDist := seeds) hf (reduced S rand seeds F g).toClassical
  have last : (qrTcrT (reduced S rand seeds F g)).forge = chainTcrMachine S rand F (oracle g) := by
    funext (st : Open.RState S.vp P₀) (pk : S.Node)
    kexact (wOracle S rand seeds F g st.1 pk
      (fun x => wotsTcrAnswerO (prims := randPrims (ref S g)) pk st.2 x.1 x.2.1 x.2.2)
      (fun x => tcrAnswer (prims := randPrims (ref S g)) pk st.2 x.1 x.2.1 x.2.2)
      (fun x => wotsTcrAnswerO_tbl (prims := randPrims (ref S g)) (gspec := []ₒ) st.1.1 pk st.2 x.1 x.2.1 x.2.2)).symm
  kexact congrArg₂ (fun ch fo => (⟨Open.RState S.vp P₀,ch,fo,F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
    QSM_DT_TCR_Adversary (WS Input Output E) (chainTcrProblem S seeds g))) choose.symm last.symm

theorem chainTcrMachine_budget (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => chainTcrMachine S rand F H st pk)
      (wotsBudget S c.ml q qs (wotsTcrHashes S.vp)) := by
  intro st pk
  apply wMachine_pue S f₀ rand F c st.1 pk _ _ q qs _ _ hq hs hc
  · intro x
    exact (wotsTcrAnswerO_kindBound (prims := P₀) .hash pk st.2 x.1 x.2.1 x.2.2).mono (by rw [show Lazy.ind Lazy.Kind.hash Lazy.Kind.hash = 1 from rfl,wotsTcrHashes]; exact le_of_eq (by ring))
  · intro x L
    exact Realize.Wots.pw_tcr (prims := P₀) (gspec := []ₒ) (exceeds S f₀ L) (okLength_cost S f₀ L) pk st.2 x.1 x.2.1 x.2.2

theorem wide_chainTcr_reduction (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ g : CompressionTables, unifW _ g * qSM_DT_TCR_Advantage (qrTcrT (reduced S rand seeds F g))) ≤
      epsTcr S (wotsBudget S c.ml q qs (wotsTcrHashes S.vp)) := by
  simp_rw [← chainTcrGame_eq S rand seeds F]
  apply wide_chain_tcr_port _ _ _ _ hw
  exact chainTcrMachine_budget S rand F c q qs hq hs hc

noncomputable def udSelect : QSM_DT_UD_Adversary (WS Input Output E) (baseUd S seeds) where
  State := Open.RState S.vp P₀
  pick := Open.udPhase1 (vp := S.vp) (prims := P₀) seeds
  distinguish := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

noncomputable def udMachine (H : Input → Output) (st : Open.RState S.vp P₀) (pk : S.Node) :=
  wMachine S f₀ rand F st.1 pk (fun x => wotsWinO (prims := P₀) pk st.2 x.1 x.2.1 x.2.2) H

theorem udGame_eq (g : CompressionTables) :
    udAdversary S seeds (udSelect S seeds F) (udMachine S rand F) g = qrUd (reduced S rand seeds F g) := by
  let real := functions S g
  let hf : Open.HashFns P₀ := ⟨real.thash,real.hmsg,real.prf,real.prfMsg⟩
  have choose : (qrUd (reduced S rand seeds F g)).pick = (udSelect S seeds F).pick := by
    kexact Open.wotsUd_phase1_q1_zero (prims := P₀) (pkSeedDist := seeds) hf (reduced S rand seeds F g).toClassical
  have last : (qrUd (reduced S rand seeds F g)).distinguish = udMachine S rand F (oracle g) := by
    funext (st : Open.RState S.vp P₀) (pk : S.Node)
    kexact (wOracle S rand seeds F g st.1 pk
      (fun x => wotsWinO (prims := randPrims (ref S g)) pk st.2 x.1 x.2.1 x.2.2)
      (fun x => WotsGame.win (prims := randPrims (ref S g)) pk st.2 x.1 x.2.1 x.2.2)
      (fun x => wotsWinO_tbl (prims := randPrims (ref S g)) (gspec := []ₒ) st.1.1 pk st.2 x.1 x.2.1 x.2.2)).symm
  kexact congrArg₂ (fun ch fo => (⟨Open.RState S.vp P₀,ch,fo,F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
    QSM_DT_UD_Adversary (WS Input Output E) (udProblem S seeds g))) choose.symm last.symm

theorem udMachine_budget (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => udMachine S rand F H st pk)
      (wotsBudget S c.ml q qs (wotsWinHashes S.vp)) := by
  intro st pk
  apply wMachine_pue S f₀ rand F c st.1 pk _ _ q qs _ _ hq hs hc
  · intro x
    exact (wotsWinO_kindBound (prims := P₀) .hash pk st.2 x.1 x.2.1 x.2.2).mono (by simp [Lazy.ind,wotsWinHashes])
  · intro x L
    exact Realize.Wots.pw_win _ (okLength_cost S f₀ L) pk st.2 x.1 x.2.1 x.2.2

theorem wide_ud_reduction (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ g : CompressionTables, unifW _ g * qSM_DT_UD_RealSuccess (qrUd (reduced S rand seeds F g))) ≤
      (∑ g : CompressionTables, unifW _ g * qSM_DT_UD_IdealSuccess (qrUd (reduced S rand seeds F g))) + SetOracle.epsUdSet S (wotsBudget S c.ml q qs (wotsWinHashes S.vp)) := by
  simp_rw [← udGame_eq S rand seeds F]
  apply wide_ud_port _ _ _ _ hw
  exact udMachine_budget S rand F c q qs hq hs hc

end Reduction.Compression
#print axioms Reduction.Compression.wide_pre_reduction
#print axioms Reduction.Compression.wide_chainTcr_reduction
#print axioms Reduction.Compression.wide_ud_reduction
