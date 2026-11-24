import Integration.SlhDsaCompressionClassReduction
import Integration.SlhDsaCompressionHiddenWeight

namespace Reduction.Compression.ClassOne
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash
open HiddenWeight (mean)
attribute [local irreducible] arityTargets tcrTargets
variable (S : Sha2Set)
local notation "f₀" => carrier S
local notation "P₀" => randPrims (carrier S)
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

private def trim (st : State S f₀) : State S f₀ := (st.1,Realize.clampL S.vp.params.len st.2)

set_option maxHeartbeats 2000000 in
private theorem choose_trim (ar : ℕ) : trim S <$> Open.tcrPhase1 S.vp P₀ ar = Open.tcrPhase1 S.vp P₀ ar := by
  have ok (xs : List S.Node) (hx : Realize.OkLen S.vp xs) : xs.length ≤ S.vp.params.len := by
    rcases hx with h|h|h|h <;> rw [h] <;> cases S <;> decide +kernel
  kexact Realize.routeHF_clamp (fun xs : List S.Node => xs.length = ar) (tcrTargets S.vp)
    S.vp.params.len (Open.tcrChooseHF S.vp P₀)
    (Realize.tcrChooseHF_len (vp := S.vp) (prims := P₀) S.vp.params.len ok) [] (by simp)

noncomputable def classEnd (ar : ℕ) (H : Input → Output) (st : State S f₀) (pk : S.Node) :=
  machine S f₀ rand F ar (st.1, Realize.clampL S.vp.params.len st.2) pk H

noncomputable def classActual (ar : ℕ) (g : CompressionTables) :
    QSM_DT_TCR_Adversary (WS Input Output E) (thashArityProblemT S.vp (randPrims (functions S g)) seeds ar) where
  State := State S f₀
  choose := Open.tcrPhase1 S.vp P₀ ar
  forge := classEnd S rand F ar (oracle g)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private theorem inner_map {W I K T M Y : Type} [Fintype W] [DecidableEq T] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem I K T M Y} (A : QSM_DT_TCR_Adversary W P) (φ : A.State → A.State)
    (hc : φ <$> A.choose = A.choose) (pk : K) :
    tcrInner A pk = tcrInner { A with forge := fun s => A.forge (φ s) } pk := by
  unfold tcrInner
  apply congrArg (fun prog => qWeight (· = true) prog A.ρ₀)
  conv_lhs => rw [← hc]
  simp only [simulateQ_map,StateT.run_map,liftU_map,bind_map_left]

private noncomputable def original (ar : ℕ) (g : CompressionTables) :
    QSM_DT_TCR_Adversary (WS Input Output E) (thashArityProblemT S.vp (randPrims (functions S g)) seeds ar) where
  State := State S f₀
  choose := Open.tcrPhase1 S.vp P₀ ar
  forge := fun st pk => machine S f₀ rand F ar st pk (oracle g)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private theorem original_eq (ar : ℕ) (g : CompressionTables) :
    qbTcrArM ar (reduced S rand seeds F g) = original S rand seeds F ar g := by
  let B := original S rand seeds F ar g
  let real := functions S g
  let hf : Open.HashFns P₀ := ⟨real.thash,real.hmsg,real.prf,real.prfMsg⟩
  have hch : (qbTcrArM ar (reduced S rand seeds F g)).choose = B.choose := by
    kexact (Open.bTcrArM_choose_eq ar (reduced S rand seeds F g).toClassical).trans
      (Open.tcrPhase1_withHash (prims := P₀) (vp := S.vp) hf ar)
  have hfo : (qbTcrArM ar (reduced S rand seeds F g)).forge = B.forge := by
    funext st pk
    kexact (atOracle S rand seeds F g ar st pk).symm
  kexact congrArg₂ (fun ch fo => (⟨State S f₀,ch,fo,F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
    QSM_DT_TCR_Adversary (WS Input Output E) (thashArityProblemT S.vp (randPrims (functions S g)) seeds ar))) hch hfo

private theorem trimmed_inner (ar : ℕ) (g : CompressionTables) (pk : S.Node) :
    tcrInner (original S rand seeds F ar g) pk = tcrInner (classActual S rand seeds F ar g) pk := by
  let B := original S rand seeds F ar g
  have hc : trim S <$> B.choose = B.choose := by kexact choose_trim S ar
  have h := inner_map B (trim S) hc pk
  dsimp only [B,original,trim,classActual,classEnd] at h ⊢
  kexact h

private theorem inner_mean {W I K T M Y : Type} [Fintype W] [DecidableEq T] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem I K T M Y} (A : QSM_DT_TCR_Adversary W P) :
    qSM_DT_TCR_Advantage A = mean P.th.seedGen (tcrInner A) := qSM_DT_TCR_Advantage_eq_tsum A

attribute [local irreducible] qbTcrArM qSM_DT_TCR_Advantage tcrInner mean
theorem classMean (ar : ℕ) (g : CompressionTables) :
    qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g)) =
      mean seeds (tcrInner (classActual S rand seeds F ar g)) := by
  let B := original S rand seeds F ar g
  refine (congrArg qSM_DT_TCR_Advantage (original_eq S rand seeds F ar g)).trans ?_
  have h := inner_mean B
  dsimp only [thashArityProblemT] at h
  refine h.trans ?_
  exact congrArg (mean seeds) (funext (trimmed_inner S rand seeds F ar g))

theorem class_cost (ar : ℕ) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (st : State S f₀) (pk : S.Node) :
    PUE (spec := unifSpec) cnt0 (fun H => classEnd S rand F ar H st pk) (budget S c.ml q qs) :=
  machine_pue S f₀ rand F c ar _ pk q qs (Realize.clampL_mem _ _) hq hs hc

end Reduction.Compression.ClassOne
#print axioms Reduction.Compression.ClassOne.classMean
#print axioms Reduction.Compression.ClassOne.class_cost
