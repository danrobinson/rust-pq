import Integration.SlhDsaBridgeWotsRow
import PQ.Interactive.QromBridgeWotsUd

/-!
# The WOTS-chain UD bridge (`qrUd`, term `ud`), game side

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

**Headline** `ud_term`: for every port forger `F` over `encΩ` and every `q'`, with `1 ≤ c.tl`,

  `avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) ≤
     avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + epsUdTight q'`

(`B = internalΩ c optRand₀ pkSeedDist₀ encΩ F`) under ONE hypothesis `hTight` (machine side):
for every world `ω₀`, state `st` and seed `pk`, the success weight of the second phase
`(qrUd …).distinguish st pk`, as a function of the port function, is (on the worlds
`{ω₀ with thash := T}`) a functional with the TIGHT hidden-set bound with `q'` queries
(`PQ.QROM.Tight.TightAvgBound`).  A `HybridModel` would only give `4 q' / 2^64`.
`ud_term_hud` is the fact `hud` of `composed_of_linear_eps` with `eUd = epsUdTight (q + r.ud)`.

Route: as `Integration/SlhDsaBridgeWotsPre.lean`, with `PQ.Interactive.ud_row_avg_le` (lazy
sampling of both worlds, `PQ.QROM.ud_tight_obs_real_le_ideal_add`) and the pull-back of the tight
bound along the row (`PQ.QROM.wq_tightAvgBound_pullback`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Reduction

attribute [local irreducible] wotsChainTargets

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- The first phase of `qrUd` at a world with the same non-`Thash` components is the forger-free
program `Open.udPhase1` at `ω`. -/
theorem qrUd_pick_eq (ω ω' : Ω128 c) (T : WqTab c) (hω : ω' = ω.wqWithThash T) :
    ((qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω')).pick :
      OracleComp (Open.udSpecC (Bytes 22) BN) (Open.RState Link.vp (primsΩ ω))) =
      Open.udPhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀ := by
  subst hω
  have h2 := Open.wotsUd_phase1_q1_zero (prims := primsΩ (ω.wqWithThash T))
    (pkSeedDist := pkSeedDist₀)
    (Open.hashFnsOf _) (internalΩ c optRand₀ pkSeedDist₀ encΩ F (ω.wqWithThash T)).toClassical
  have h3 : (Open.udPhase1 (vp := Link.vp) (prims := primsΩ (ω.wqWithThash T)) pkSeedDist₀ :
      OracleComp (Open.udSpecC (Bytes 22) BN) (Open.RState Link.vp (primsΩ ω))) =
      Open.udPhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀ := by
    wq_kernel_rfl
  unfold qrUd
  dsimp only
  exact h2.trans h3

theorem udInnerW_row_eq (world : TweakableHash.SM_DT_UD_World) (ω : Ω128 c) (pk : BN)
    (R : Bytes 22 × BN → BN) :
    udInner world (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.wqWithThash (wqRowT ω.thash pk R)))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_UD_oracles world
          (udWithEval (wotsUdProblem Link.vp (primsΩ ω) pkSeedDist₀)
            (wotsUdProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
              pkSeedDist₀).th.eval
            (wotsUdProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
              pkSeedDist₀).thColl.eval) pk)
          (Open.udPhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀)).run ([], [])) >>=
        fun r ↦
        (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.wqWithThash (wqRowT ω.thash pk R)))).distinguish r.1 pk) F.ρ₀ := by
  unfold udInner
  rw [qrUd_pick_eq c optRand₀ pkSeedDist₀ F ω _ _ rfl]
  wq_kernel_rfl

/-- **Per world and seed**, WOTS-chain UD. -/
theorem ud_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : Ω128 c) (pk : BN)
    (hTight : ∀ st : Open.RState Link.vp (primsΩ ω),
      ∃ f : (EncX c → EncY) → ℝ≥0∞, PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) q' ∧
        ∀ T : WqTab c, f (encΩ (ω.wqWithThash T)) =
          qWeight (· = true) ((qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            (ω.wqWithThash T))).distinguish st pk) F.ρ₀) :
    ∑ R : Bytes 22 × BN → BN, (Fintype.card (Bytes 22 × BN → BN) : ℝ≥0∞)⁻¹ *
      udInner .real (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
        (ω.wqWithThash (wqRowT ω.thash pk R)))) pk ≤
      ∑ R : Bytes 22 × BN → BN, (Fintype.card (Bytes 22 × BN → BN) : ℝ≥0∞)⁻¹ *
        udInner .ideal (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.wqWithThash (wqRowT ω.thash pk R)))) pk +
      ENNReal.ofReal (8 * (q' : ℝ) ^ 2 / Fintype.card BN) := by
  have hT : ∀ s : Open.RState Link.vp (primsΩ ω),
      ∃ f : (Bytes 22 × BN → BN) → ℝ≥0∞,
        PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) q' ∧
        ∀ R, f R = qWeight (· = true) ((qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            (ω.wqWithThash (wqRowT ω.thash pk R)))).distinguish s pk) F.ρ₀ := by
    intro s
    obtain ⟨f, hf, hfe⟩ := hTight s
    refine ⟨fun R ↦ f (encΩ (ω.wqWithThash (wqRowT ω.thash pk R))),
      wq_tightAvgBound_pullback (fun H ↦ (f H).toReal) q' hf (wqRowEmb c hn pk)
        (fun R ↦ encΩ (ω.wqWithThash (wqRowT ω.thash pk R))) (encΩ_wq_row_local c hn ω pk),
      fun R ↦ hfe _⟩
  have key := ud_row_avg_le (wotsUdProblem Link.vp (primsΩ ω) pkSeedDist₀) pk
    (fun R ↦ (wotsUdProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ wq_F_row c hn ω pk R t m)
    (fun R ↦ (wotsUdProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
      pkSeedDist₀).thColl.eval)
    (fun R R' i t x h ↦ wq_thash_row_local c ω pk R R' t x h) rfl rfl
    (Open.udPhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀)
    (fun R s ↦ (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.wqWithThash (wqRowT ω.thash pk R)))).distinguish s pk) F.ρ₀ F.posSemidef
    F.trace_eq_one q' hT
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_))
    (le_trans key (add_le_add (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) le_rfl))
  · rw [udInnerW_row_eq]
  · rw [udInnerW_row_eq]

/-- **The WOTS-chain UD term** (`qrUd`), given the tight bound of its second phase. -/
theorem ud_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hTight : ∀ (ω₀ : Ω128 c) (st : Open.RState Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ f : (EncX c → EncY) → ℝ≥0∞,
        PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) q' ∧
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n),
          f (encΩ { ω₀ with thash := T }) =
            qWeight (· = true) ((qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).distinguish st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess
      (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess
        (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) + epsUdTight q' := by
  set δ : ℝ≥0∞ := ENNReal.ofReal (8 * (q' : ℝ) ^ 2 / Fintype.card BN) with hδ
  have hδe : δ = epsUdTight q' := by
    have hc : (Fintype.card BN : ℝ) = 2 ^ 128 := by
      rw [card_bytes_n, Nat.cast_pow, Nat.cast_ofNat]
    rw [hδ, epsUdTight, hc]
  rw [← hδe]
  simp only [qSM_DT_UD_RealSuccess_eq_tsum, qSM_DT_UD_IdealSuccess_eq_tsum]
  set gR : Ω128 c → BN → ℝ≥0∞ := fun ω pk ↦
    udInner .real (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) pk with hgR
  set gI : Ω128 c → BN → ℝ≥0∞ := fun ω pk ↦
    udInner .ideal (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) pk with hgI
  have hsd : ∀ ω : Ω128 c,
      (wotsUdProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ :=
    fun _ ↦ rfl
  change avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob
      (wotsUdProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen (· = pk) * gR ω pk) ≤
    avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob
      (wotsUdProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen (· = pk) * gI ω pk) + δ
  simp only [hsd]
  have hswap : ∀ g : Ω128 c → BN → ℝ≥0∞,
      avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * g ω pk) =
        ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ g ω pk) := by
    intro g
    unfold avΩ
    simp only [← ENNReal.tsum_mul_left, Finset.mul_sum]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine tsum_congr fun pk ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [hswap gR, hswap gI]
  have hpk : ∀ pk, avΩ c (fun ω ↦ gR ω pk) ≤ avΩ c (fun ω ↦ gI ω pk) + δ := by
    intro pk
    rw [avΩ_wq_resample c hn pk (fun ω ↦ gR ω pk), avΩ_wq_resample c hn pk (fun ω ↦ gI ω pk),
      ← avΩ_const c δ, ← avΩ_add]
    exact avΩ_mono c fun ω ↦
      ud_row_inner_le c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hTight ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ gR ω pk)
      ≤ ∑' pk, (PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ gI ω pk) +
          PQ.Interactive.prob pkSeedDist₀ (· = pk) * δ) :=
        tsum_le_tsum fun pk ↦ by rw [← mul_add]; exact mul_le_mul' le_rfl (hpk pk)
    _ = ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ gI ω pk) +
          (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * δ := by
        rw [tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := by
        gcongr
        calc (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * δ ≤ 1 * δ :=
              mul_le_mul' (wq_tsum_prob_le_one _) le_rfl
          _ = δ := one_mul δ

/-- **`hud` of `composed_of_linear_eps`**: the UD term at the composed theorem's count
`q + r.ud`, in exactly the form consumed (`eUd := epsUdTight (q + r.ud)`). -/
theorem ud_term_hud (q : ℕ) (r : RedCounts) (htl : 35 ≤ c.tl)
    (hTight : ∀ (ω₀ : Ω128 c) (st : Open.RState Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ f : (EncX c → EncY) → ℝ≥0∞,
        PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) (q + r.ud) ∧
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n),
          f (encΩ { ω₀ with thash := T }) =
            qWeight (· = true) ((qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).distinguish st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess
      (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess
        (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) + epsUdTight (q + r.ud) :=
  ud_term c optRand₀ pkSeedDist₀ F (by omega) _ hTight

end inst

end Reduction

#print axioms Reduction.qrUd_pick_eq
#print axioms Reduction.udInnerW_row_eq
#print axioms Reduction.ud_row_inner_le
#print axioms Reduction.ud_term
#print axioms Reduction.ud_term_hud
