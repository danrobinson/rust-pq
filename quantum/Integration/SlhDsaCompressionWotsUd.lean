import Integration.SlhDsaCompressionWotsPre

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
open scoped ComplexOrder Kronecker
variable (S : Sha2Set)

noncomputable def baseUd (seeds : ProbComp S.Node) : SM_DT_UD_Problem Unit S.Node (Bytes 22) S.Node S.Node S.Node where
  th := (basePre S seeds).th
  thColl := (basePre S seeds).thColl
  emb := id
  emb_injective := Function.injective_id
  inputGen := $ᵗ S.Node
  outputGen := $ᵗ S.Node
  numTargets := wotsChainTargets S.vp

noncomputable def udProblem (seeds : ProbComp S.Node) (g : CompressionTables) := udWithEval (baseUd S seeds)
  (leafHash S g) (collection S g)

theorem udProblem_eq (seeds : ProbComp S.Node) (g : CompressionTables) :
    udProblem S seeds g = wotsUdProblem S.vp (randPrims (functions S g)) seeds := rfl

attribute [local irreducible] wotsChainTargets
variable {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
  (A : QSM_DT_UD_Adversary (WS Input Output E) (baseUd S seeds))
  (dist : (Input → Output) → A.State → S.Node → Closed (WS Input Output E) Bool)

def udAdversary (g : CompressionTables) : QSM_DT_UD_Adversary (WS Input Output E) (udProblem S seeds g) where
  State := A.State
  pick := A.pick
  distinguish := dist (oracle g)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

theorem wide_ud_fixed (hw : S.vp.params.n ≠ 16) (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => dist H s pk) q) :
    (∑ g : CompressionTables, unifW _ g * udInner .real (udAdversary S seeds A dist g) pk) ≤
    (∑ g : CompressionTables, unifW _ g * udInner .ideal (udAdversary S seeds A dist g) pk) +
      SetOracle.epsUdSet S q := by
  let val := fun w g => udInner w (udAdversary S seeds A dist g) pk
  have inner (g : CompressionTables) :
      (∑ R : SingletonRow S, unifW _ R * val .real (replaceSingleton S pk g R)) ≤
      (∑ R : SingletonRow S, unifW _ R * val .ideal (replaceSingleton S pk g R)) + SetOracle.epsUdSet S q := by
    let th := fun R => leafHash S (replaceSingleton S pk g R)
    let ce := fun R => collection S (replaceSingleton S pk g R)
    have ht (s : A.State) : ∃ b : SingletonRow S → ℝ≥0∞, Tight.TightAvgBound (fun R => (b R).toReal) q ∧
        ∀ R, b R = qWeight (· = true) (dist (oracle (replaceSingleton S pk g R)) s pk) A.ρ₀ := by
      classical
      obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input × Output) × E) A.ρ₀ A.posSemidef A.trace_eq_one
      obtain ⟨x,hx,he⟩ := (hq s).exists_prog_qprob
      let b := fun H => qprob LocalSig.Interp.instruments H x ρ (fun p => p.2 = true)
      have hb := Tight.qprob_tightAvgBound LocalSig.Interp.instruments x ρ q hx (fun p => p.2 = true)
      refine ⟨fun R => b (oracle (replaceSingleton S pk g R)), wq_tightAvgBound_pullback
        (fun H => (b H).toReal) q hb (singletonEmbedding S g pk) _ (singleton_local S g pk), ?_⟩
      intro R
      exact (he (· = true) _ ρ).trans (by rw [hρ])
    have h := ud_row_avg_le (baseUd S seeds) pk th (replacedF S g pk) ce
      (fun R T _ a xs => wideCollection_local S hw g pk R T a xs) rfl rfl A.pick
      (fun R s => dist (oracle (replaceSingleton S pk g R)) s pk) A.ρ₀ A.posSemidef A.trace_eq_one q ht
    have e : ENNReal.ofReal (8*(q:ℝ)^2 / Fintype.card S.Node) = SetOracle.epsUdSet S q := by
      unfold SetOracle.epsUdSet
      rw [card_bytes',pow_mul]; norm_num
    rw [e] at h
    exact h
  change (∑ g, unifW _ g * val .real g) ≤ (∑ g, unifW _ g * val .ideal g) + _
  rw [average_singleton S pk (val .real), average_singleton S pk (val .ideal)]
  calc _ ≤ ∑ g : CompressionTables, unifW _ g * (_ + SetOracle.epsUdSet S q) :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (inner g)
       _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul]

theorem wide_ud_port (hw : S.vp.params.n ≠ 16) (q : ℕ)
    (hq : ∀ s pk, PUE (spec := unifSpec) cnt0 (fun H => dist H s pk) q) :
    (∑ g : CompressionTables, unifW _ g * qSM_DT_UD_RealSuccess (udAdversary S seeds A dist g)) ≤
    (∑ g : CompressionTables, unifW _ g * qSM_DT_UD_IdealSuccess (udAdversary S seeds A dist g)) +
      SetOracle.epsUdSet S q := by
  let a := fun g pk => udInner .real (udAdversary S seeds A dist g) pk
  let b := fun g pk => udInner .ideal (udAdversary S seeds A dist g) pk
  let eps := SetOracle.epsUdSet S q
  simp only [qSM_DT_UD_RealSuccess_eq_tsum, qSM_DT_UD_IdealSuccess_eq_tsum]
  change (∑ g : CompressionTables, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * a g pk) ≤
    (∑ g : CompressionTables, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * b g pk) + eps
  rw [average_seed S seeds a, average_seed S seeds b]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * ((∑ g : CompressionTables, unifW _ g * b g pk) + eps) :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (wide_ud_fixed S seeds A dist hw pk q (fun s => hq s pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk) * ∑ g : CompressionTables, unifW _ g * b g pk) +
          (∑' pk, PQ.Interactive.prob seeds (· = pk)) * eps := by simp only [mul_add]; rw [tsum_add, ENNReal.tsum_mul_right]
       _ ≤ _ := add_le_add le_rfl ((mul_le_mul' (tsum_prob_eq_le_one seeds) le_rfl).trans (one_mul eps).le)

end Reduction.Compression
#print axioms Reduction.Compression.wide_ud_fixed
#print axioms Reduction.Compression.wide_ud_port
