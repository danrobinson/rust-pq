import Integration.SlhDsaShakeXofSignature

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives ShakeApi.primitives ShakeApi.scheme
attribute [local irreducible] arityTargets tcrTargets

/-- Sum the component losses, keeping the two PRF bounds and the adaptive
digest-covering probability separate. -/
noncomputable def repeatedLossWithPrfs (S : Sha2Set) (q s : ℕ) (sk msg cover : ℝ≥0∞) : ℝ≥0∞ :=
  let f := q+forsMHashes S.vp s
  let a := epsTcr S (q+tcrMHashes S.vp s)
  sk + msg + cover +
    (ENNReal.ofReal (168*(f:ℝ)^2 / 2^(8*S.vp.params.n))+3*epsTcr S f) + (a+a+a+a) +
    ((S.vp.params.w-2:ℕ):ℝ≥0∞)*SetOracle.epsUdSet S (q+qmWotsUdHashes S.vp s) +
    SetOracle.epsPreSet S (q+qmWotsPreHashes S.vp s) + epsTcr S (q+qmWotsTcrTHashes S.vp s)

noncomputable def repeatedLoss (S : Sha2Set) (q s : ℕ) (cover : ℝ≥0∞) : ℝ≥0∞ :=
  let prf := fun (t : ℕ) => ENNReal.ofReal (8*(t:ℝ)^2 / 2^(8*S.vp.params.n))
  repeatedLossWithPrfs S q s (prf (ShakeApi.Sk.budget S q s)) (prf (ShakeApi.Msg.budget S q s)) cover

variable (S : Sha2Set) (N : ℕ) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "A" => ShakeApi.rawForger S N r seeds F
local notation "B" => fun H => qPureBytesToInternal (A H)
local notation "P" => fun H => ShakeApi.primitives S (ShakeApi.extend H)

/-- Reduction of both byte-level forgery probabilities to the remaining digest
covering game for arbitrary public and signing-query budgets. -/
theorem signature_with_prfs (q s : ℕ) (sk msg : ℝ≥0∞)
    (fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hsk : uniformMean (fun H => qPrfRealPr (skPrfC S.vp (P H)) (qbPrfWC sufCheck (B H)) F.ρ₀) ≤
      uniformMean (fun H => qPrfIdealPr (qbPrfWC sufCheck (B H)) F.ρ₀) + sk)
    (hmsg : uniformMean (fun H => qPrfRealPr (msgPrf S.vp (P H)) (qbPrfMsgWL sufCheck (B H)) F.ρ₀) ≤
      uniformMean (fun H => qPrfIdealPr (qbPrfMsgWL sufCheck (B H)) F.ρ₀) + msg) :
    let risk := uniformMean (fun H => qItsrAdvantage (itsrProblem S.vp (P H)) (qbItsrL (B H)) F.ρ₀)
    uniformMean (fun H => qStrongUnforgeableAdvantage (A H)) ≤ repeatedLossWithPrfs S q s sk msg risk ∧
    uniformMean (fun H => qUnforgeableAdvantage (A H)) ≤ repeatedLossWithPrfs S q s sk msg risk := by
  have singleton := fit 1 (by simp)
  simp only [Nat.mul_one] at singleton
  have short : 2*S.vp.params.n+32 ≤ N := by omega
  have one : FitsSingleton S (N := N) := by unfold FitsSingleton; omega
  have linear := avg_of_pointwise (unifW (ShakeApi.RawTable S N)) _ _ _ (fun H =>
    slhdsa_pure_bytes_suf_cma_final_linear_quantum_all (ShakeApi.structural S (ShakeApi.extend H)) (A H))
  simp only [qLinRealSuf,qLinIdealSuf] at linear
  have ar k hk := arity_reduction S N r seeds F k (fit k hk) q s hq hs
  have strong := SetOracle.composeFamily S.vp P B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one)
    (fun _ => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one) linear
    hsk hmsg (le_refl _)
    (actualForsDspr S N r seeds F one q s hq hs) (actualForsTcr S N r seeds F one q s hq hs)
    (ar 1 (by simp)) (ar 2 (by simp)) (ar _ (by simp)) (ar _ (by simp))
    (actualWotsUd S N r seeds F one q s hq hs) (actualWotsPre S N r seeds F one q s hq hs)
    (actualWotsTcr S N r seeds F one q s hq hs)
  exact ⟨strong,(Finset.sum_le_sum fun H _ => mul_le_mul' (a:=unifW _ H) le_rfl (quantum_euf_le_suf (A H))).trans strong⟩

/-- Reduction of both byte-level forgery probabilities to the remaining digest
covering game for arbitrary public and signing-query budgets. -/
theorem signature_repeated (q s : ℕ) (c : Caps) (raw : 2*S.vp.params.n+c.ml ≤ N)
    (fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let risk := uniformMean (fun H => qItsrAdvantage (itsrProblem S.vp (P H)) (qbItsrL (B H)) F.ρ₀)
    uniformMean (fun H => qStrongUnforgeableAdvantage (A H)) ≤ repeatedLoss S q s risk ∧
    uniformMean (fun H => qUnforgeableAdvantage (A H)) ≤ repeatedLoss S q s risk := by
  have singleton := fit 1 (by simp)
  simp only [Nat.mul_one] at singleton
  exact signature_with_prfs S N r seeds F q s _ _ fit hq hs
    (ShakeApi.Sk.real_le_ideal S N r seeds F (by omega) q s hq hs)
    (ShakeApi.Msg.real_le_ideal S N r seeds F c raw q s hq hs hc)

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.signature_repeated
