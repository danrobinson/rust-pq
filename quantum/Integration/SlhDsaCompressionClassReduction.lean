import Integration.SlhDsaCompressionClassMachine
import Integration.SlhDsaCompressionClassTransport
import Integration.SlhDsaCompressionForsReduction
import Ideal.Realize.Phase1

namespace Reduction.Compression.ClassOne
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash Resources2
attribute [local irreducible] arityTargets tcrTargets
variable (S : Sha2Set)
local notation "f₀" => carrier S
local notation "P₀" => randPrims (carrier S)
private def ref (g : CompressionTables) : RandFns S.vp.params :=
  { carrier S with thash := (functions S g).thash, hmsg := (functions S g).hmsg }
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

theorem atOracle (g : CompressionTables) (n : ℕ) (st : State S f₀) (pk : S.Node) :
    machine S f₀ rand F n st pk (oracle g) = qMemoForge n (reduced S rand seeds F g) st pk := by
  let real := functions S g
  let r := fun (k : PublicKeyCore (randPrims (ref S g)).core) => rand k.pkSeed k.pkRoot
  let r' := fun (k : PublicKeyCore (randPrims real).core) => rand k.pkSeed k.pkRoot
  let codec := SetOracle.codecFor S (ref S g)
  let B := F.at (oracle g) (pureBytesAlg S.vp (randPrims (ref S g)) codec r seeds)
  have tr := QInd.qMemoForge_tr (prims := randPrims (ref S g)) real.prf real.prfMsg codec r r' seeds
    (fun _ => rfl) n B st pk
  refine Eq.trans ?_ tr.symm
  rw [qMemoForge_eq_qmMach]
  have hh : machine S f₀ rand F n st pk (oracle g) = machine S (ref S g) rand F n st pk (oracle g) := by qm_kernel_rfl
  rw [hh]
  unfold machine
  have interp : hashPort S (ref S g) (oracle g) = PublicHash.impl (randPrims (ref S g)) := by
    unfold hashPort
    rw [tablesOf_oracle]
    funext t
    cases t <;> rfl
  rw [interp, mainAt_eq S (ref S g) F rand seeds]

private noncomputable def select : QSM_DT_TCR_Adversary (WS Input Output E) (base S seeds) where
  State := State S f₀
  choose := Open.tcrPhase1 S.vp P₀ 1
  forge := fun _ _ => pure (0,asMsg S default)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private def clamp (s : State S f₀) : State S f₀ := (s.1,Realize.clampL S.vp.params.len s.2)

set_option maxHeartbeats 2000000 in
private theorem clamp_choose : clamp S <$> Open.tcrPhase1 S.vp P₀ 1 = Open.tcrPhase1 S.vp P₀ 1 := by
  have ok (xs : List S.Node) (hx : Realize.OkLen S.vp xs) : xs.length ≤ S.vp.params.len := by
    rcases hx with h|h|h|h <;> rw [h] <;> cases S <;> decide +kernel
  kexact Realize.routeHF_clamp (fun xs : List S.Node => xs.length = 1) (tcrTargets S.vp)
    S.vp.params.len (Open.tcrChooseHF S.vp P₀)
    (Realize.tcrChooseHF_len (vp := S.vp) (prims := P₀) S.vp.params.len ok) [] (by simp)

private noncomputable def endAt (H : Input → Output) (st : State S f₀) (pk : S.Node) :=
  machine S f₀ rand F 1 st pk H

private theorem unclamped (g : CompressionTables) :
    adversary S seeds (select S seeds F) (endAt S rand F) g = qbTcrArM 1 (reduced S rand seeds F g) := by
  let real := functions S g
  let hf : Open.HashFns P₀ := ⟨real.thash,real.hmsg,real.prf,real.prfMsg⟩
  have choose : (qbTcrArM 1 (reduced S rand seeds F g)).choose = (select S seeds F).choose := by
    kexact (Open.bTcrArM_choose_eq 1 (reduced S rand seeds F g).toClassical).trans
      (Open.tcrPhase1_withHash (prims := P₀) (vp := S.vp) hf 1)
  have last : (qbTcrArM 1 (reduced S rand seeds F g)).forge = endAt S rand F (oracle g) := by
    funext st pk
    kexact (atOracle S rand seeds F g 1 st pk).symm
  kexact congrArg₂ (fun ch fo => (⟨State S f₀,ch,fo,F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
    QSM_DT_TCR_Adversary (WS Input Output E) (problem S seeds g))) choose.symm last.symm

private theorem normalize_inner {W I K T M Y : Type} [Fintype W] [DecidableEq T] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem I K T M Y} (A : QSM_DT_TCR_Adversary W P) (φ : A.State → A.State)
    (hc : φ <$> A.choose = A.choose) (pk : K) :
    tcrInner A pk = tcrInner { A with forge := fun s => A.forge (φ s) } pk := by
  unfold tcrInner
  apply congrArg (fun prog => qWeight (· = true) prog A.ρ₀)
  conv_lhs => rw [← hc]
  simp only [simulateQ_map,StateT.run_map,liftU_map,bind_map_left]

private theorem normalize_adv {W I K T M Y : Type} [Fintype W] [DecidableEq T] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem I K T M Y} (A : QSM_DT_TCR_Adversary W P) (φ : A.State → A.State)
    (hc : φ <$> A.choose = A.choose) :
    qSM_DT_TCR_Advantage A = qSM_DT_TCR_Advantage { A with forge := fun s => A.forge (φ s) } := by
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  apply tsum_congr
  intro pk
  exact congrArg (_ * ·) (normalize_inner A φ hc pk)

private theorem clamp_adv (g : CompressionTables) :
    qSM_DT_TCR_Advantage (adversary S seeds (select S seeds F) (endAt S rand F) g) =
    qSM_DT_TCR_Advantage (adversary S seeds (select S seeds F) (fun H s => endAt S rand F H (clamp S s)) g) := by
  let A := adversary S seeds (select S seeds F) (endAt S rand F) g
  have hc : clamp S <$> A.choose = A.choose := by kexact clamp_choose S
  kexact normalize_adv A (clamp S) hc

theorem wide_class_tcr_reduction (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ g : CompressionTables, unifW _ g * qSM_DT_TCR_Advantage (qbTcrArM 1 (reduced S rand seeds F g))) ≤
      epsTcr S (budget S c.ml q qs) := by
  apply le_trans (le_of_eq (Finset.sum_congr rfl (fun g _ => congrArg (fun z => unifW _ g * z)
    ((congrArg qSM_DT_TCR_Advantage (unclamped S rand seeds F g).symm).trans (clamp_adv S rand seeds F g)))))
  have h := wide_class_tcr_port S seeds (select S seeds F) (fun H s => endAt S rand F H (clamp S s))
    hw (budget S c.ml q qs) (fun s pk => machine_pue S f₀ rand F c 1 (clamp S s) pk q qs
      (Realize.clampL_mem _ _) hq hs hc)
  exact h

end Reduction.Compression.ClassOne
#print axioms Reduction.Compression.ClassOne.wide_class_tcr_reduction
