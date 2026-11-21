import Integration.SlhDsaBridgeTcr
import Reduction.Open.Phase1Fors
import PQ.Interactive.QromBridgeFors

/-!
# The FORS-leaf TCR bridge (`tcrFv`), game side

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

**Headline** `tcrFv_term`: for every port forger `F` over the fixed encoding `encΩ`, with
`1 ≤ c.tl` and every `q'`,

  `avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)))
     ≤ epsTcr0 q'`

(the hypothesis `hfv` of `composed_of_linear_eps` at `eFv = epsTcr0 (q + r.tcrFv)`), under ONE
hypothesis `hModel`: for every world `ω₀`, first-phase state `st` and seed `pk`, the second
phase of the reduction (`(qToTcr …).forge st pk`) has a `q'`-query hybrid model over the port
function, uniformly in the `Thash` component `T` of the world.  `hModel` is the machine-side
statement (agent `qmach`); it is NOT proved here.  The seed distribution is arbitrary.

Route (no `TcrFvValue`/`MixLE`):
1. `qTcrFV_Advantage_eq_tsum` (seed average), exchange with `avΩ`;
2. `fors_avΩ_resample_frow`: resample the arity-one `Thash` row at `pk` (the row of `F`), indexed by
   `Bytes 22 × BN` (`frowEquiv`, `thRowT 1`);
3. the first phase is the forger-free program `Open.forsPhase1` (`Open.toTcr_choose_eq`,
   kernel-checked `rfl` for the `Thash`-independence); the game oracles at the resampled world are
   those of the game at `ω` with the row as hash (`fors_eval_row`); the collection is empty;
4. the model is pulled back along `T ↦ encΩ {ω with thash := T}` restricted to the row
   (`HybridModel.pullback`, locality `fors_encΩ_frow_local`);
5. `PQ.Interactive.tcrFv_row_avg_le` (generic: invariance of the first phase under non-target row
   changes at valid final states + `spr_embedded_obs_weighted_le`), `card_bytes_n`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Reduction

/-! ## The arity-one row of `Thash` (the row of `F`) -/

/-- Arity-one messages are single values. -/
def am1Equiv : ArMsg 1 ≃ BN where
  toFun xs := xs.1.head (List.ne_nil_of_length_eq_add_one xs.2)
  invFun x := ⟨[x], rfl⟩
  left_inv xs := by
    obtain ⟨l, hl⟩ := xs
    cases l with
    | nil => simp at hl
    | cons a t =>
      cases t with
      | nil => rfl
      | cons b t => simp at hl
  right_inv _ := rfl

/-- A row of `F` at one seed: tweak and input to value. -/
abbrev FRow : Type := Bytes 22 × BN → BN

/-- Rows of `F` as arity-one rows of `Thash`. -/
def frowEquiv : FRow ≃ ThRow 1 :=
  Equiv.arrowCongr (Equiv.prodCongr (Equiv.refl _) am1Equiv.symm) (Equiv.refl _)

theorem frowEquiv_apply (R : FRow) (a : Bytes 22) (xs : ArMsg 1) :
    frowEquiv R (a, xs) = R (a, am1Equiv xs) := rfl

/-- Resampling the row of `F` at `pk` does not change a uniform average. -/
theorem fors_avΩ_resample_frow (c : Caps) (hn : 1 ≤ c.tl) (pk : BN) (f : Ω128 c → ℝ≥0∞) :
    avΩ c f = avΩ c fun ω ↦ ∑ R : FRow,
      (Fintype.card FRow : ℝ≥0∞)⁻¹ * f (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))) := by
  rw [avΩ_resample_row c 1 hn pk f]
  refine congrArg (avΩ c) (funext fun ω ↦ ?_)
  have hc : Fintype.card (ThRow 1) = Fintype.card FRow := Fintype.card_congr frowEquiv.symm
  rw [hc]
  exact (Equiv.sum_comp frowEquiv
    (fun R ↦ (Fintype.card FRow : ℝ≥0∞)⁻¹ * f (ω.withThash (thRowT 1 ω.thash pk R)))).symm

/-- The row embedding of `F` into the port domain. -/
def frowEmb (c : Caps) (hn : 1 ≤ c.tl) (pk : BN) : Bytes 22 × BN ↪ EncX c :=
  (Equiv.toEmbedding (Equiv.prodCongr (Equiv.refl _) am1Equiv.symm)).trans (thRowEmb c 1 hn pk)

theorem fors_encΩ_frow_local (c : Caps) (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (H G : FRow)
    (x : EncX c)
    (h : encΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv H))) x ≠
      encΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv G))) x) :
    ∃ x', frowEmb c hn pk x' = x ∧ H x' ≠ G x' := by
  obtain ⟨x'', hx, hne⟩ := encΩ_row_local c 1 hn ω pk (frowEquiv H) (frowEquiv G) x h
  refine ⟨(x''.1, am1Equiv x''.2), ?_, hne⟩
  rw [← hx]
  change thRowEmb c 1 hn pk (x''.1, am1Equiv.symm (am1Equiv x''.2)) = _
  rw [Equiv.symm_apply_apply]

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- `F` at the world with the resampled row is the row. -/
theorem fors_eval_row (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : FRow) (a : Bytes 22)
    (x : BN) :
    (forsTcrProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
      pkSeedDist₀).th.eval pk a x = R (a, x) := by
  change (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R)))).Thash pk a [x] = R (a, x)
  rw [thash_thRowT, dif_pos (show [x].length ≤ c.tl from hn)]
  exact thRowT_ofList 1 hn ω.thash pk (frowEquiv R) a ⟨[x], rfl⟩

/-- The per-seed game at the world with a resampled row, written over the game at `ω` with the
row as hash and the forger-free first phase. -/
theorem tcrFvInner_row_eq (ω : Ω128 c) (pk : BN) (R : FRow) :
    tcrFvInner (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles
          (fvWithEval (forsTcrProblem Link.vp (primsΩ ω) pkSeedDist₀)
            (forsTcrProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
              pkSeedDist₀).th.eval) pk)
          (Open.forsPhase1 Link.vp (primsΩ ω))).run .initial) >>= fun r ↦
        (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).forge r.1 pk >>= fun jm ↦
        liftU (match r.2.challenges[jm.1]? with
          | none => pure false
          | some tm =>
            pure (r.2.valid && decide (jm.2 ≠ tm.2 ∧
              (forsTcrProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk
                (frowEquiv R)))) pkSeedDist₀).th.eval pk tm.1 jm.2 =
              (forsTcrProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk
                (frowEquiv R)))) pkSeedDist₀).th.eval pk tm.1 tm.2)))) F.ρ₀ := by
  have hch : ((qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).choose :
      OracleComp (Open.ForsP1Spec (primsΩ ω)) (Open.ForsP1State Link.vp (primsΩ ω))) =
      Open.forsPhase1 Link.vp (primsΩ ω) := by
    have h2 := Open.toTcr_choose_eq (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R)))).toClassical
    have h3 : (Open.forsPhase1 Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk
        (frowEquiv R)))) : OracleComp (Open.ForsP1Spec (primsΩ ω)) _) =
        Open.forsPhase1 Link.vp (primsΩ ω) := by
      qtcr_kernel_rfl
    unfold qToTcr
    dsimp only
    exact h2.trans h3
  unfold tcrFvInner
  rw [hch]
  qtcr_kernel_rfl

/-- **Per world and seed**: the row-average of the TCR-FV game's winning weight at the seed. -/
theorem tcrFv_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : Ω128 c) (pk : BN)
    (hModel : ∀ st : Open.ForsP1State Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × BN) q',
        ∀ (T : ThTab c) (Ev : ℕ × BN → Prop) [DecidablePred Ev],
          Mo.prob (encΩ (ω.withThash T)) Ev =
            qWeight Ev ((qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              (ω.withThash T))).forge st pk) F.ρ₀) :
    ∑ R : FRow, (Fintype.card FRow : ℝ≥0∞)⁻¹ *
      tcrFvInner (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
        (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card BN : ℝ≥0∞) := by
  have hM : ∀ s : Open.ForsP1State Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × BN) BN (ℕ × BN) q',
        ∀ R (Ev : ℕ × BN → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).forge s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (frowEmb c hn pk)
      (fun R ↦ encΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
      (fors_encΩ_frow_local c hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := tcrFv_row_avg_le (forsTcrProblem Link.vp (primsΩ ω) pkSeedDist₀) pk
    (fun R ↦ (forsTcrProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ fors_eval_row c pkSeedDist₀ hn ω pk R t m)
    (Open.forsPhase1 Link.vp (primsΩ ω))
    (fun R s ↦ (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).forge s pk) F.ρ₀ q' hM
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) key
  rw [tcrFvInner_row_eq]
  qtcr_kernel_rfl

/-- **The FORS-leaf TCR term** (`hfv` of `composed_of_linear_eps`), for every port forger over
the fixed encoding, given the hybrid model of the reduction's second phase (`hModel`). -/
theorem tcrFv_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n) q',
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      epsTcr0 q' := by
  set ε : ℝ≥0∞ := (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card BN : ℝ≥0∞) with hε
  have hεe : ε = epsTcr0 q' := by
    rw [hε, epsTcr0, card_cast_N128 card_bytes_n]
  rw [← hεe]
  simp only [qTcrFV_Advantage_eq_tsum]
  set g : Ω128 c → BN → ℝ≥0∞ := fun ω pk ↦
    tcrFvInner (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) pk with hg
  have hsd : ∀ ω : Ω128 c,
      (forsTcrProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ := fun _ ↦ rfl
  change avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob
    (forsTcrProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen (· = pk) * g ω pk) ≤ ε
  simp only [hsd]
  have hswap : avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * g ω pk) =
      ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ g ω pk) := by
    unfold avΩ
    simp only [← ENNReal.tsum_mul_left, Finset.mul_sum]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine tsum_congr fun pk ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [hswap]
  have hpk : ∀ pk, avΩ c (fun ω ↦ g ω pk) ≤ ε := by
    intro pk
    rw [fors_avΩ_resample_frow c hn pk]
    refine le_trans (avΩ_mono c fun ω ↦ ?_) (le_of_eq (avΩ_const c ε))
    exact tcrFv_row_inner_le c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ g ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * ε :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' (tsum_prob_eq_le_one _) le_rfl
    _ = ε := one_mul ε

end inst

end Reduction

#print axioms Reduction.fors_avΩ_resample_frow
#print axioms Reduction.fors_encΩ_frow_local
#print axioms Reduction.fors_eval_row
#print axioms Reduction.tcrFvInner_row_eq
#print axioms Reduction.tcrFv_row_inner_le
#print axioms Reduction.tcrFv_term
