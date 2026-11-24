import Integration.SlhDsaShakeXofWotsPre

namespace Reduction.ShakeXof
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
open scoped ComplexOrder Kronecker
variable (S : Sha2Set) {N : ℕ} (cap : FitsSingleton S (N := N))

noncomputable def baseUd (seeds : ProbComp S.Node) : SM_DT_UD_Problem Unit S.Node (Bytes 32) S.Node S.Node S.Node where
  th := (basePre S seeds).th
  thColl := (basePre S seeds).thColl
  emb := id
  emb_injective := Function.injective_id
  inputGen := $ᵗ S.Node
  outputGen := $ᵗ S.Node
  numTargets := wotsChainTargets S.vp

noncomputable def udProblem (seeds : ProbComp S.Node) (g : ShakeApi.RawTable S N) := udWithEval (baseUd S seeds)
  (leafHash S g) (collection S g)

theorem udProblem_eq (seeds : ProbComp S.Node) (g : ShakeApi.RawTable S N) :
    udProblem S seeds g = wotsUdProblem S.vp (ShakeApi.primitives S (ShakeApi.extend g)) seeds := rfl

attribute [local irreducible] wotsChainTargets
variable {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
  (A : QSM_DT_UD_Adversary (Work S N E) (baseUd S seeds))
  (dist : ShakeApi.RawTable S N → A.State → S.Node → Closed (Work S N E) Bool)

def udAdversary (g : ShakeApi.RawTable S N) : QSM_DT_UD_Adversary (Work S N E) (udProblem S seeds g) where
  State := A.State
  pick := A.pick
  distinguish := dist g
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

include cap in
theorem wots_ud_fixed (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => dist H s pk) q) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * udInner .real (udAdversary S seeds A dist g) pk) ≤
    (∑ g : ShakeApi.RawTable S N, unifW _ g * udInner .ideal (udAdversary S seeds A dist g) pk) +
      SetOracle.epsUdSet S q := by
  let val := fun w g => udInner w (udAdversary S seeds A dist g) pk
  have inner (g : ShakeApi.RawTable S N) :
      (∑ R : SingletonRow S, unifW _ R * val .real (replaceSingleton S cap pk g R)) ≤
      (∑ R : SingletonRow S, unifW _ R * val .ideal (replaceSingleton S cap pk g R)) + SetOracle.epsUdSet S q := by
    let th := fun R => leafHash S (replaceSingleton S cap pk g R)
    let ce := fun R => collection S (replaceSingleton S cap pk g R)
    have ht (s : A.State) : ∃ b : SingletonRow S → ℝ≥0∞, Tight.TightAvgBound (fun R => (b R).toReal) q ∧
        ∀ R, b R = qWeight (· = true) (dist (replaceSingleton S cap pk g R) s pk) A.ρ₀ := by
      classical
      obtain ⟨ρ,hρ⟩ := exists_subState (A := (ShakeApi.Input N × Bytes S.vp.params.m) × E) A.ρ₀ A.posSemidef A.trace_eq_one
      obtain ⟨x,hx,he⟩ := (hq s).exists_prog_qprob
      let b := fun H => qprob LocalSig.Interp.instruments H x ρ (fun p => p.2 = true)
      have hb := Tight.qprob_tightAvgBound LocalSig.Interp.instruments x ρ q hx (fun p => p.2 = true)
      refine ⟨fun R => b (replaceSingleton S cap pk g R), wq_tightAvgBound_pullback
        (fun H => (b H).toReal) q hb (singletonEmbedding S cap pk) _ (different_at (singletonEmbedding S cap pk) g), ?_⟩
      intro R
      exact (he (· = true) _ ρ).trans (by rw [hρ])
    have h := ud_row_avg_le (baseUd S seeds) pk th (replacedF S cap g pk) ce
      (fun R T _ a xs => collection_local S cap g pk R T a xs) rfl rfl A.pick
      (fun R s => dist (replaceSingleton S cap pk g R) s pk) A.ρ₀ A.posSemidef A.trace_eq_one q ht
    have e : ENNReal.ofReal (8*(q:ℝ)^2 / Fintype.card S.Node) = SetOracle.epsUdSet S q := by
      unfold SetOracle.epsUdSet
      rw [card_bytes',pow_mul]; norm_num
    rw [e] at h
    exact h
  change (∑ g, unifW _ g * val .real g) ≤ (∑ g, unifW _ g * val .ideal g) + _
  rw [average_singleton S cap pk (val .real), average_singleton S cap pk (val .ideal)]
  calc _ ≤ ∑ g : ShakeApi.RawTable S N, unifW _ g * (_ + SetOracle.epsUdSet S q) :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (inner g)
       _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul]

include cap in
theorem wots_ud_port (q : ℕ)
    (hq : ∀ s pk, PUE (spec := unifSpec) cnt0 (fun H => dist H s pk) q) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qSM_DT_UD_RealSuccess (udAdversary S seeds A dist g)) ≤
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qSM_DT_UD_IdealSuccess (udAdversary S seeds A dist g)) +
      SetOracle.epsUdSet S q := by
  let a := fun g pk => udInner .real (udAdversary S seeds A dist g) pk
  let b := fun g pk => udInner .ideal (udAdversary S seeds A dist g) pk
  let eps := SetOracle.epsUdSet S q
  simp only [qSM_DT_UD_RealSuccess_eq_tsum, qSM_DT_UD_IdealSuccess_eq_tsum]
  change (∑ g : ShakeApi.RawTable S N, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * a g pk) ≤
    (∑ g : ShakeApi.RawTable S N, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * b g pk) + eps
  rw [average_seed S seeds a, average_seed S seeds b]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * ((∑ g : ShakeApi.RawTable S N, unifW _ g * b g pk) + eps) :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (wots_ud_fixed S cap seeds A dist pk q (fun s => hq s pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk) * ∑ g : ShakeApi.RawTable S N, unifW _ g * b g pk) +
          (∑' pk, PQ.Interactive.prob seeds (· = pk)) * eps := by simp only [mul_add]; rw [tsum_add, ENNReal.tsum_mul_right]
       _ ≤ _ := add_le_add le_rfl ((mul_le_mul' (tsum_prob_eq_le_one seeds) le_rfl).trans (one_mul eps).le)

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.wots_ud_fixed
#print axioms Reduction.ShakeXof.wots_ud_port
