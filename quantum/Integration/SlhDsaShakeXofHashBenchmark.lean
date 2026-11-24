import Integration.SlhDsaShakeXofWotsReduction
import Integration.SlhDsaShakeXofForsReduction

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
variable (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "B" => ShakeApi.rawInternal S N rand seeds F
variable {q Q : ℕ}
local notation "tcr" => ((2*(Q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n))

/-- Actual FORS, tweak-arity and WOTS games of the shared-XOF signature
forger, with one signing query and a common bound on all reduction query counts. -/
theorem hash_games (room : q + 2^40 ≤ Q)
    (fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    (uniformMean (fun H => qDsprFV_Success (qToDspr (B H))) ≤
      uniformMean (fun H => qDsprFV_SPProbability (qToDspr (B H))) + ENNReal.ofReal (168*(Q:ℝ)^2 / 2^(8*S.vp.params.n))) ∧
    (uniformMean (fun H => qTcrFV_Advantage (qToTcr (B H))) ≤ tcr) ∧
    (∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], uniformMean (fun H => qSM_DT_TCR_Advantage (qbTcrArM k (B H))) ≤ tcr) ∧
    (uniformMean (fun H => qSM_DT_UD_RealSuccess (qrUd (B H))) ≤
      uniformMean (fun H => qSM_DT_UD_IdealSuccess (qrUd (B H))) + SetOracle.epsUdSet S Q) ∧
    (uniformMean (fun H => qSM_DT_PRE_Advantage (qrPre (B H))) ≤ SetOracle.epsPreSet S Q) ∧
    (uniformMean (fun H => qSM_DT_TCR_Advantage (qrTcrT (B H))) ≤ tcr) := by
  have cap : FitsSingleton S (N := N) := by
    have h := fit 1 (by simp)
    simp only [Nat.mul_one] at h
    unfold FitsSingleton
    omega
  have honest : forsMHashes S.vp 1 ≤ 2^40 ∧ tcrMHashes S.vp 1 ≤ 2^40 ∧
      qmWotsUdHashes S.vp 1 ≤ 2^40 ∧ qmWotsPreHashes S.vp 1 ≤ 2^40 ∧
      qmWotsTcrTHashes S.vp 1 ≤ 2^40 := by cases S <;> decide +kernel
  obtain ⟨f,a,u,p,c⟩ := honest
  replace f := (Nat.add_le_add_left f q).trans room
  replace a := (Nat.add_le_add_left a q).trans room
  replace u := (Nat.add_le_add_left u q).trans room
  replace p := (Nat.add_le_add_left p q).trans room
  replace c := (Nat.add_le_add_left c q).trans room
  refine ⟨(actualForsDspr S N rand seeds F cap _ _ hq hs).trans ?_,
    (actualForsTcr S N rand seeds F cap _ _ hq hs).trans ?_, ?_,
    (actualWotsUd S N rand seeds F cap _ _ hq hs).trans ?_,
    (actualWotsPre S N rand seeds F cap _ _ hq hs).trans ?_,
    (actualWotsTcr S N rand seeds F cap _ _ hq hs).trans ?_⟩
  · refine add_le_add le_rfl ?_
    gcongr
  · gcongr
  · intro k hk
    refine (arity_reduction S N rand seeds F k (fit k hk) _ _ hq hs).trans ?_
    gcongr
  · refine add_le_add le_rfl ?_
    unfold SetOracle.epsUdSet
    gcongr
  · unfold SetOracle.epsPreSet
    gcongr
  · unfold epsTcr
    gcongr

section
local notation "C" => (2^41 : ℕ)
/-- Actual FORS, tweak-arity and WOTS games of the shared-XOF signature
forger, with one signing query and at most 2^40 public raw queries. -/
theorem benchmark_hash_games
    (fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    (uniformMean (fun H => qDsprFV_Success (qToDspr (B H))) ≤
      uniformMean (fun H => qDsprFV_SPProbability (qToDspr (B H))) + ENNReal.ofReal (168*(C:ℝ)^2 / 2^(8*S.vp.params.n))) ∧
    (uniformMean (fun H => qTcrFV_Advantage (qToTcr (B H))) ≤ ((2*(C:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n))) ∧
    (∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], uniformMean (fun H => qSM_DT_TCR_Advantage (qbTcrArM k (B H))) ≤ ((2*(C:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n))) ∧
    (uniformMean (fun H => qSM_DT_UD_RealSuccess (qrUd (B H))) ≤
      uniformMean (fun H => qSM_DT_UD_IdealSuccess (qrUd (B H))) + SetOracle.epsUdSet S C) ∧
    (uniformMean (fun H => qSM_DT_PRE_Advantage (qrPre (B H))) ≤ SetOracle.epsPreSet S C) ∧
    (uniformMean (fun H => qSM_DT_TCR_Advantage (qrTcrT (B H))) ≤ ((2*(C:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n))) := hash_games S N rand seeds F (by decide) fit hq hs
end

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.benchmark_hash_games
