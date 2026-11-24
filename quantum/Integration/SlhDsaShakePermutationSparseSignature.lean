import Integration.SlhDsaShakePermutationSparseCap
import Integration.SlhDsaShakePermutationSparseNumbers

/-! The actual one- and two-node TCR terms of the linear quantum signature
reduction for the shared two-way permutation at the SHA-2 benchmark. -/
namespace Reduction.ShakePermutation.SparsePort.Memo
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash SetOracle
open ShakeApi (Xof RawTable extend)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] arityTargets tcrTargets Select.choice Phase.erase Select.prog
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
variable (S : Sha2Set) (ar : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "T₀" => (fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m))
local notation "P₀" => ShakeApi.primitives S (extend T₀)
local notation "tab" => SkCost.table S N
local notation "pr" => fun π : Permutation => ShakeApi.primitives S (extend (tab (oracle π)))
local notation "rpr" => fun π : Permutation => primitives (lanes π) S.vp.params
local notation "B" => fun π : Permutation => qPureBytesToInternal (SkCost.capped S rand seeds F N π)

noncomputable def selection : QSM_DT_TCR_Adversary (ArityGame.Work E) (ArityGame.Base S ar seeds) where
  State := Open.TcrP1State S.vp P₀
  choose := Select.choice S ar (extend T₀)
  forge := fun _ _ => pure (0,⟨List.replicate ar default,by simp⟩)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

local notation "A" => selection S ar seeds F
local notation "M" => fun H st pk => machine S N rand F T₀ ar st pk H

noncomputable def capAdv (π : Permutation) : QSM_DT_TCR_Adversary (ArityGame.Work E) (cappedGame S ar seeds π) where
  State := (A).State
  choose := (A).choose
  forge := M (oracle π)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

theorem capAdv_eq (π : Permutation) : capAdv S ar rand seeds F π = qbTcrArM ar (B π) := by
  let real := pr π
  let hf : Open.HashFns P₀ := ⟨real.Thash,real.Hmsg,real.PRF,real.PRFmsg⟩
  have ch : (qbTcrArM ar (B π)).choose = (A).choose := by
    kexact (Open.bTcrArM_choose_eq ar (B π).toClassical).trans
      (Open.tcrPhase1_withHash (prims:=P₀) (vp:=S.vp) hf ar)
  have fg : M (oracle π) = (qbTcrArM ar (B π)).forge :=
    funext fun st => funext fun pk => machine_oracle S N rand seeds F T₀ ar st pk π
  kexact congrArg₂ (fun c f => (⟨Open.TcrP1State S.vp P₀,c,f,F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
    QSM_DT_TCR_Adversary (ArityGame.Work E) (cappedGame S ar seeds π))) ch.symm fg

theorem cap_inner (π : Permutation) (pk : S.Node) (h : ar ≤ 67) :
    tcrInner (capAdv S ar rand seeds F π) pk =
      tcrInner (ArityGame.adversary S ar seeds A M π) pk := by
  let r := (rpr π).Thash
  let p := (pr π).Thash
  have hp := Select.choice_len S ar (extend T₀)
  have same := choose_same S ar seeds π pk (Select.choice S ar (extend T₀)) ([],[]) hp
  let run (op : S.Node → Bytes 32 → List S.Node → S.Node) :=
    (simulateQ (interp S ar seeds op pk) (A).choose).run ([],[])
  have hr : run p = run r := same
  let lc := (simulateQ (SM_DT_TCR_oracles (cappedGame S ar seeds π) pk) (A).choose).run ([],[])
  let rc := (simulateQ (SM_DT_TCR_oracles (ArityGame.actualGame S ar seeds π) pk) (A).choose).run ([],[])
  have hr' : lc = rc := by kexact hr
  unfold tcrInner
  apply congrArg (fun prog : Closed (ArityGame.Work E) Bool => qWeight (· = true) prog F.ρ₀)
  refine congrArg₂ (fun u k => (liftU u : Closed (ArityGame.Work E) ((A).State × Select.History S ar)) >>= k) hr' ?_
  funext v
  apply congrArg (fun k => M (oracle π) v.1 pk >>= k)
  funext jm
  cases v.2.1[jm.1]? with
  | none => rfl
  | some tm =>
    have left := short S π pk tm.1 jm.2.val (jm.2.property.le.trans h)
    have right := short S π pk tm.1 tm.2.val (tm.2.property.le.trans h)
    let dec (u v : S.Node) : Closed (ArityGame.Work E) Bool := pure (decide (jm.2 ≠ tm.2 ∧ u=v))
    kexact congrArg₂ dec left right

theorem cap_advantage (π : Permutation) (h : ar ≤ 67) : qSM_DT_TCR_Advantage (qbTcrArM ar (B π)) =
    qSM_DT_TCR_Advantage (ArityGame.adversary S ar seeds A M π) := by
  rw [← capAdv_eq S ar rand seeds F π]
  have eq : (∑' pk, PQ.Interactive.prob seeds (· = pk) * tcrInner (capAdv S ar rand seeds F π) pk) =
      ∑' pk, PQ.Interactive.prob seeds (· = pk) * tcrInner (ArityGame.adversary S ar seeds A M π) pk :=
    tsum_congr (fun pk => congrArg (fun v => PQ.Interactive.prob seeds (· = pk) * v) (cap_inner S ar rand seeds F π pk h))
  kexact (qSM_DT_TCR_Advantage_eq_tsum (capAdv S ar rand seeds F π)).trans (eq.trans
    (qSM_DT_TCR_Advantage_eq_tsum (ArityGame.adversary S ar seeds A M π)).symm)

/-- Numerical bound on the native arity-1 or arity-2 SM-TCR term
appearing in the linear SUF-CMA bound for each FIPS 205 SHAKE set. -/
theorem signature_tcr (h : ar ≤ 2)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    uniformMean (fun π => qSM_DT_TCR_Advantage (qbTcrArM ar (B π))) ≤ ((2:ℝ≥0∞)^38)⁻¹ := by
  let q := 2^40 + 483 * tcrMHashes S.vp 1
  let Q := 17*tcrTargets S.vp
  rw [show (fun π => qSM_DT_TCR_Advantage (qbTcrArM ar (B π))) = (fun π => qSM_DT_TCR_Advantage (ArityGame.adversary S ar seeds A M π)) from funext (fun π => cap_advantage S ar rand seeds F π (h.trans (by decide)))]
  have phase2 (st : (A).State) (pk : S.Node) : PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q := by
    kexact machine_cost S N rand F T₀ (le_refl N) ar st pk (2^40) 1 hq hs
  have phase1 (pk : S.Node) : CountBound (fun i => i.isRight = true)
      (simulateQ Phase.erase (Select.prog S ar pk (A).choose ([],[]))) Q := by
    kexact Select.native_cost S ar pk (extend T₀)
  exact (ArityGame.bound S ar seeds A M h q Q phase2 phase1).trans
    (ArityGame.benchmark_loss S ar h q Q (ArityGame.memo_queries S) (Select.benchmark_calls S))

end Reduction.ShakePermutation.SparsePort.Memo
#print axioms Reduction.ShakePermutation.SparsePort.Memo.signature_tcr
