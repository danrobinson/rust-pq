import Integration.SlhDsaShakeXofTcrMachine
import Integration.SlhDsaShakeXofTcr

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash ShakeApi
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] arityTargets tcrTargets
variable (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
abbrev zeroTable := fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m)
local notation "H₀" => zeroTable S N
local notation "P₀" => primitives S (extend H₀)
local notation "internal" => rawInternal S N rand seeds F

private noncomputable def arityChoice (ar : ℕ) : QSM_DT_TCR_Adversary (Work S N E) (Arity.base S ar seeds) where
  State := Open.TcrP1State S.vp P₀
  choose := Open.tcrPhase1 S.vp P₀ ar
  forge := fun _ _ => pure (0,⟨List.replicate ar default,by simp⟩)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private theorem arity_eq (H : RawTable S N) (ar : ℕ) :
    Arity.adversary S ar seeds (arityChoice S N seeds F ar)
      (fun G st pk => (qbTcrArM ar (internal G)).forge st pk) H = qbTcrArM ar (internal H) := by
  let real := primitives S (extend H)
  let hf : Open.HashFns P₀ := ⟨real.Thash,real.Hmsg,real.PRF,real.PRFmsg⟩
  have ch : (qbTcrArM ar (internal H)).choose = (arityChoice S N seeds F ar).choose := by
    kexact (Open.bTcrArM_choose_eq ar (internal H).toClassical).trans
      (Open.tcrPhase1_withHash (prims := P₀) (vp := S.vp) hf ar)
  kexact congrArg (fun c => (⟨Open.TcrP1State S.vp P₀,c,(qbTcrArM ar (internal H)).forge,
    F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QSM_DT_TCR_Adversary (Work S N E) (Arity.problem S ar seeds H))) ch.symm

/-- Each of the four arity-class games of the byte-signature reduction, at
its actual public and signing query budgets on the same raw XOF. -/
theorem arity_reduction (ar : ℕ) (cap : S.vp.params.n + 32 + S.vp.params.n*ar ≤ N)
    (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    SetOracle.uniformMean (fun H => qSM_DT_TCR_Advantage (qbTcrArM ar (internal H))) ≤
      (2*((q+tcrMHashes S.vp qs : ℕ):ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  simp_rw [← arity_eq S N rand seeds F _ ar]
  apply Arity.bound S ar seeds _ _ cap
  intro st pk
  obtain ⟨M,hm,he⟩ := ShakeApi.tcr_mach_exists S N rand seeds F H₀ ar st pk q qs hq hs
  exact (funext he) ▸ hm

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.arity_reduction
