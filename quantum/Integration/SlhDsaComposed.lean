import Integration.SlhDsaRandomFinite
import PQ.Interactive.QromBridgeSpec

/-!
# The conditional composed QROM statement for SLH-DSA-SHA2-128s

NOT part of the default target; checked by `scripts/check-integration.sh`.

See `Integration/SlhDsaComposedFinal.lean` for the form in which every numerical term bound is
derived from the Part-2 theorems and only the bridge statements remain as hypotheses.

Hash components: a uniformly random element `ω` of the finite function space `Ω128 c`
(`Integration/SlhDsaRandomFinite.lean`), constant outside the caps `c`.

## Statement

`slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_conditional`: FIPS 205 external (pure) interface
on byte strings.  The forger is ONE syntactic object `F : PortForger X Y E` — a program with
instruments on its workspace, an oracle port (quantum access to the hash, presented through an
encoding `enc : Ω128 c → X → Y` of the function tuple as one function), uniform sampling and the
classical signing oracle; in world `ω` it is the Part-1 machine `F.at (enc ω)` (port calls
replaced by `U_{enc ω}`).  `optRand₀`, `pkSeedDist` do not depend on `ω`.  Then

  `E_ω[qAdv(F.at (enc ω))] ≤ composedBound (countsOf q qs r)`.

## Hypotheses of the theorem — ALL UNPROVED here except where marked

Hypotheses on the forger (these define the class of forgers; they are premises of `hT`):

* `hq : ∀ pk, CountBound isPort (F.main pk) q` — at most `q` quantum hash queries per run;
* `hqs : ∀ pk, CountBound isSign (F.main pk) qs` — at most `qs` signing queries per run;
* `hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)` — every signing query `(M, ctx)` and
  the forgery satisfy `|M| + |ctx| + 2 ≤ c.ml` (so `H_msg`/`PRF_msg` are only evaluated within the
  caps; outside them the functions of `Ω128 c` are constant and forging is trivial).  The cap
  `c.tl ≥ 35` on `Thash` lists is NOT a hypothesis of the theorem: it only enters through `hT`.

Hypothesis `hT : (hq) → (hqs) → (hcap) → TermBounds… (countsOf q qs r)`: one named field per term
of the linear headline.  `r : QromCounts` are the reduction's own oracle-call counts (functions
of `qs`: requests R1–R3, R7 of `STATUS.md` §0), `r.q1` its first-phase quantum hash-query count
(`r.q1 = 0` is request R4; `composedBound_zeroPre` simplifies the bound under this named
hypothesis `hq1`).  For each field, what would discharge it:

| field | statement (ω-average, reduction machine around the forger) | open form | bridge | Part-2 theorem |
|---|---|---|---|---|
| `prf` | `qPrfRealPr ≤ qPrfIdealPr + 8q²/2^128` (`qbPrfC`/`qbPrfWC`) | R1 | `QromBridgePrf.lean` (`prf_port_real_le_ideal_add`) + hash-tuple reduction | `prfExact_tight_real_le_ideal_add` |
| `msg` | same for `qbPrfMsgL`/`qbPrfMsgWL` | R2 | same | `prfExact_tight_real_le_ideal_add` |
| `itsr` | `qItsrAdvantage (qbItsrL)` | exists (`itsrOpen`) | missing | `itsr4_adaptive_fors_le` (no collision term; general regime with reprogramming loss `2q√(s/|K|)`) |
| `dspr` | `Success ≤ SPprob + 168q₂²/N + 2·(4q₁/√N)` | R3 | missing (two-port, `IAdv`) | `dspr_exact_tight_of_card` (tight, `2 ≤ |Y| ≤ |Msg|`) |
| `tcrFv` | `qTcrFV_Advantage ≤ (√((2q₂+1)²/N) + 2q₁/√N)²` | R3 | missing | `tcr_fv_exact_le` |
| `tcr1`,`tcr2`,`tcrLen`,`tcrK`,`tcrT` | `qSM_DT_TCR_Advantage ≤` same | R3, R4 | missing | `tcr_exact_le` |
| `ud` | `Real ≤ Ideal + (16(q₁+q₂)²+2n)/2^128` | R3, R4 | missing | `ud_exact_tight_real_le_ideal_add` (generalised game: `ExactGenUd*`) |
| `pre` | `≤ (√((2q₂+1)²·2/N) + 2q₁/√N)²` | R3, R4 | missing | `gen_pre_sub_exact_le` |

"hash-tuple reduction": the reduction of the four independent random functions of `Ω128 c` to the
single (seed-)keyed random function of the Part-2 game; not available for any term.
"missing" bridge: the Part-2 two-phase games use two oracle ports (`qrom2Spec`) and `IAdv`;
`QromBridge*.lean` covers one-port programs with classical requests (and the PRF game end to end
for port programs), not the two-port two-phase games.

PROVED here: the arithmetic (`composed_of_linear`: additivity of the average, cancellation of the
ideal side, from the unconditional uniformly averaged linear headline), `composedBound_zeroPre`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive
open scoped ComplexOrder

namespace Reduction

/-- Uniform average over the hash functions with caps `c`. -/
noncomputable def avΩ (c : Caps) (f : Ω128 c → ℝ≥0∞) : ℝ≥0∞ := ∑ ω, unifW (Ω128 c) ω * f ω

lemma avΩ_add (c : Caps) (f g : Ω128 c → ℝ≥0∞) : avΩ c (fun ω ↦ f ω + g ω) = avΩ c f + avΩ c g := by
  simp only [avΩ, mul_add, Finset.sum_add_distrib]

lemma avΩ_const_mul (c : Caps) (a : ℝ≥0∞) (f : Ω128 c → ℝ≥0∞) :
    avΩ c (fun ω ↦ a * f ω) = a * avΩ c f := by
  simp only [avΩ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

lemma avΩ_ne_top (c : Caps) (f : Ω128 c → ℝ≥0∞) (hf : ∀ ω, f ω ≠ ⊤) : avΩ c f ≠ ⊤ := by
  refine ENNReal.sum_ne_top.2 fun ω _ ↦ ENNReal.mul_ne_top ?_ (hf ω)
  exact ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- Oracle-call counts of the reduction machines, one per term.  `q1`: quantum hash queries of
the first phases (two-phase games); the other counts: second phases (PRF and ITSR machines: whole
run); `s`: ITSR target requests; `udReq`: classical requests of the UD first phase. -/
structure QromCounts where
  q1 : ℕ
  prf : ℕ
  msg : ℕ
  itsr : ℕ
  s : ℕ
  dspr : ℕ
  tcrFv : ℕ
  tcr1 : ℕ
  tcr2 : ℕ
  tcrLen : ℕ
  tcrK : ℕ
  ud : ℕ
  udReq : ℕ
  pre : ℕ
  tcrT : ℕ

/-- Counts of the reduction around a forger with `q` quantum hash queries and `qs` signing
queries: the forger's `q` queries are made in the second phase (PRF/ITSR: during the run), `r`
are the reduction's own counts. -/
def countsOf (q qs : ℕ) (r : QromCounts) : QromCounts where
  q1 := r.q1
  prf := q + r.prf
  msg := q + r.msg
  itsr := q + r.itsr
  s := qs
  dspr := q + r.dspr
  tcrFv := q + r.tcrFv
  tcr1 := q + r.tcr1
  tcr2 := q + r.tcr2
  tcrLen := q + r.tcrLen
  tcrK := q + r.tcrK
  ud := q + r.ud
  udReq := r.udReq
  pre := q + r.pre
  tcrT := q + r.tcrT

/-- `|Bytes 16| = 2^128`: number of seeds, keys, hash values and single-block messages. -/
noncomputable def N128 : ℝ≥0∞ := (2 : ℝ≥0∞) ^ 128

/-- PRF term, `8 q² / |K|` (`prfExact_tight_real_le_ideal_add`). -/
noncomputable def epsPrf (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal (8 * (q : ℝ) ^ 2 / 2 ^ 128)

/-- TCR term, `(√((2q₂+1)²/|Y|) + 2q₁/√|Sd|)²` (`tcr_exact_le`, `tcr_fv_exact_le`). -/
noncomputable def epsTcr (q₁ q₂ : ℕ) : ℝ≥0∞ :=
  (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / N128) ^ (2⁻¹ : ℝ) + 2 * q₁ * (N128⁻¹) ^ (2⁻¹ : ℝ)) ^ 2

/-- The trivial DSPR term `max 0 (2γ − 1)`, `γ = (1 − 1/|Y|)^(|Msg| − 1)`, for `|Msg| = |Y| = 2^128`
(`dsprTrivial`). -/
noncomputable def dsprTriv128 : ℝ≥0∞ :=
  (1 - N128⁻¹) ^ (2 ^ 128 - 1) - (1 - (1 - N128⁻¹) ^ (2 ^ 128 - 1))

/-- DSPR term, tight and target-count-free: `168 q₂²/|Y| + 2·(4 q₁/√|Sd|)`
(`dspr_exact_tight_of_card`, `PQ/QROM/ExactDsprTightGame.lean`; `2 ≤ |Y| ≤ |Msg|`).  Replaces the
older one-way-to-hiding shape `τ + 8 q₂/√|Y| + 2·(4 q₁/√|Sd|)` of `dspr_exact_adv_le`
(`dsprTriv128` is no longer used). -/
noncomputable def epsDspr (q₁ q₂ : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (168 * (q₂ : ℝ) ^ 2 / 2 ^ 128) + 2 * (2 * (2 * q₁ * (N128⁻¹) ^ (2⁻¹ : ℝ)))

/-- UD term, tight: `(16 (q₁+q₂)² + 2 n) / |Msg|` (`ud_exact_tight_real_le_ideal_add`). -/
noncomputable def epsUd (q₁ q₂ n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((16 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 + 2 * n) / 2 ^ 128)

/-- PRE term, `(√((2q₂+1)² (1/|Y| + 1/|Mp|)) + 2q₁/√|Sd|)²` (`gen_pre_sub_exact_le`). -/
noncomputable def epsPre (q₁ q₂ : ℕ) : ℝ≥0∞ :=
  (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 * (N128⁻¹ + N128⁻¹)) ^ (2⁻¹ : ℝ) +
    2 * q₁ * (N128⁻¹) ^ (2⁻¹ : ℝ)) ^ 2

/-- ITSR term (shape of `itsr4_adaptive_fors_le`, `PQ/QROM/ExactItsr4.lean`: no randomizer-collision
term; general regime, with the reprogramming loss): `q` quantum queries, `s` targets, `|Ix| = 2^h` hypertree
leaves, `k` FORS trees with `t = 2^a` leaves, `|K| = 2^128`. -/
noncomputable def epsItsr (p : Params) (q s : ℕ) : ℝ≥0∞ :=
  (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
      (∑ γ ∈ Finset.range (s + 1),
        (s.choose γ : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ p.h)⁻¹) ^ γ * (1 - ((2 : ℝ≥0∞) ^ p.h)⁻¹) ^ (s - γ) *
          (1 - (1 - ((2 : ℝ≥0∞) ^ p.a)⁻¹) ^ γ) ^ p.k)) ^ (2⁻¹ : ℝ) +
    2 * q * ((s : ℝ≥0∞) * N128⁻¹) ^ (2⁻¹ : ℝ)) ^ 2

/-- **The composed bound**: explicit in the counts and the parameters. -/
noncomputable def composedBound (n : QromCounts) : ℝ≥0∞ :=
  epsPrf n.prf + epsPrf n.msg + epsItsr Link.vp.params n.itsr n.s +
    (epsDspr n.q1 n.dspr + 3 * epsTcr n.q1 n.tcrFv) +
    (epsTcr n.q1 n.tcr1 + epsTcr n.q1 n.tcr2 + epsTcr n.q1 n.tcrLen + epsTcr n.q1 n.tcrK) +
    ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) * epsUd n.q1 n.ud n.udReq + epsPre n.q1 n.pre +
    epsTcr n.q1 n.tcrT

/-- The composed bound without first-phase quantum queries. -/
noncomputable def composedBound0 (n : QromCounts) : ℝ≥0∞ :=
  epsPrf n.prf + epsPrf n.msg + epsItsr Link.vp.params n.itsr n.s +
    (ENNReal.ofReal (168 * (n.dspr : ℝ) ^ 2 / 2 ^ 128) +
      3 * ((2 * (n.tcrFv : ℝ≥0∞) + 1) ^ 2 / N128)) +
    ((2 * (n.tcr1 : ℝ≥0∞) + 1) ^ 2 / N128 + (2 * (n.tcr2 : ℝ≥0∞) + 1) ^ 2 / N128 +
      (2 * (n.tcrLen : ℝ≥0∞) + 1) ^ 2 / N128 + (2 * (n.tcrK : ℝ≥0∞) + 1) ^ 2 / N128) +
    ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((16 * (n.ud : ℝ) ^ 2 + 2 * n.udReq) / 2 ^ 128) +
    (2 * (n.pre : ℝ≥0∞) + 1) ^ 2 * (N128⁻¹ + N128⁻¹) +
    (2 * (n.tcrT : ℝ≥0∞) + 1) ^ 2 / N128

lemma sq_sqrt' (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- **Zero first-phase queries** (the named hypothesis `n.q1 = 0`, request R4): all seed-hiding
terms vanish. -/
theorem composedBound_zeroPre (n : QromCounts) (hq1 : n.q1 = 0) :
    composedBound n = composedBound0 n := by
  unfold composedBound composedBound0 epsTcr epsDspr epsUd epsPre
  simp only [hq1, Nat.cast_zero, mul_zero, zero_mul, add_zero, sq_sqrt', zero_add]

variable {W : Type} [Fintype W]

section
variable (c : Caps)
  (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
  (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)

/-- **The named hypotheses**: for each term of the linear headline, the Part-2 bound for the
ω-averaged Part-1 game of the reduction machine around `B ω`.  `R₁/I₁`, `R₂/I₂` are the real/ideal
probabilities of the two PRF distinguishers (they differ between EUF and SUF). -/
structure TermBounds
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (R₁ I₁ R₂ I₂ : Ω128 c → ℝ≥0∞) (n : QromCounts) : Prop where
  /-- `PRF` (secret-key PRF, domain-restricted distinguisher). -/
  prf : avΩ c R₁ ≤ avΩ c I₁ + epsPrf n.prf
  /-- `PRF_msg`. -/
  msg : avΩ c R₂ ≤ avΩ c I₂ + epsPrf n.msg
  /-- ITSR of `H_msg`. -/
  itsr : avΩ c (fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (B ω)) (B ω).ρ₀) ≤
    epsItsr Link.vp.params n.itsr n.s
  /-- DSPR (source final validity), FORS leaves. -/
  dspr : avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (B ω))) ≤
    avΩ c (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) + epsDspr n.q1 n.dspr
  /-- TCR (source final validity), FORS leaves. -/
  tcrFv : avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) ≤ epsTcr n.q1 n.tcrFv
  /-- SM-DT-TCR, arity 1. -/
  tcr1 : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) ≤ epsTcr n.q1 n.tcr1
  /-- SM-DT-TCR, arity 2. -/
  tcr2 : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) ≤ epsTcr n.q1 n.tcr2
  /-- SM-DT-TCR, arity `len`. -/
  tcrLen : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.len (B ω))) ≤
    epsTcr n.q1 n.tcrLen
  /-- SM-DT-TCR, arity `k`. -/
  tcrK : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.k (B ω))) ≤ epsTcr n.q1 n.tcrK
  /-- SM-DT-UD of the WOTS chains. -/
  ud : avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) ≤
    avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + epsUd n.q1 n.ud n.udReq
  /-- SM-DT-PRE of the WOTS chains. -/
  pre : avΩ c (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) ≤ epsPre n.q1 n.pre
  /-- SM-DT-TCR of the WOTS chains. -/
  tcrT : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) ≤ epsTcr n.q1 n.tcrT

variable {c optRand pkSeedDist}

/-- Arithmetic core: the averaged linear inequality and the term bounds give the composed bound. -/
theorem composed_of_linear
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (adv R₁ I₁ R₂ I₂ : Ω128 c → ℝ≥0∞) (n : QromCounts)
    (hI₁ : ∀ ω, I₁ ω ≤ 1) (hI₂ : ∀ ω, I₂ ω ≤ 1)
    (hlin : avΩ c adv + avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) ≤
      avΩ c (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)))
    (hT : TermBounds c optRand pkSeedDist B R₁ I₁ R₂ I₂ n) :
    avΩ c adv ≤ composedBound n := by
  have hfin : avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) ≠ ⊤ := by
    refine avΩ_ne_top c _ fun ω ↦ ?_
    have h1 := hI₁ ω
    have h2 := hI₂ ω
    have h3 : qDsprFV_SPProbability (qToDspr (B ω)) ≤ 1 :=
      qWeight_le_one _ _ (qToDspr (B ω)).posSemidef (qToDspr (B ω)).trace_eq_one
    have h4 : qSM_DT_UD_IdealSuccess (qrUd (B ω)) ≤ 1 :=
      qWeight_le_one _ _ (qrUd (B ω)).posSemidef (qrUd (B ω)).trace_eq_one
    unfold qLinearIdealSide
    refine ne_top_of_le_ne_top (b := 1 + 1 + 1 + ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) * 1) ?_ ?_
    · simp
    · gcongr
  have hId : avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) =
      avΩ c I₁ + avΩ c I₂ + avΩ c (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) +
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) := by
    unfold qLinearIdealSide
    simp only [avΩ_add, avΩ_const_mul]
  have hRe : avΩ c (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)) =
      avΩ c R₁ + avΩ c R₂ +
        avΩ c (fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (B ω)) (B ω).ρ₀) +
        (avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (B ω))) +
          3 * avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω)))) +
        (avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) +
          avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) +
          avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.len (B ω))) +
          avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.k (B ω)))) +
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) +
        avΩ c (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) +
        avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) := by
    unfold qLinearRealSide
    simp only [avΩ_add, avΩ_const_mul]
  have hle : avΩ c (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)) ≤
      composedBound n + avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) := by
    rw [hRe, hId]
    have hud : ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) ≤
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          (avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + epsUd n.q1 n.ud n.udReq) := by
      gcongr
      exact hT.ud
    have hfv : 3 * avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) ≤ 3 * epsTcr n.q1 n.tcrFv := by
      gcongr
      exact hT.tcrFv
    calc _ ≤ (avΩ c I₁ + epsPrf n.prf) + (avΩ c I₂ + epsPrf n.msg) +
          epsItsr Link.vp.params n.itsr n.s +
          ((avΩ c (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) + epsDspr n.q1 n.dspr) +
            3 * epsTcr n.q1 n.tcrFv) +
          (epsTcr n.q1 n.tcr1 + epsTcr n.q1 n.tcr2 + epsTcr n.q1 n.tcrLen + epsTcr n.q1 n.tcrK) +
          ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
            (avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + epsUd n.q1 n.ud n.udReq) +
          epsPre n.q1 n.pre + epsTcr n.q1 n.tcrT :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add hT.prf hT.msg) hT.itsr) (add_le_add hT.dspr hfv))
          (add_le_add (add_le_add (add_le_add hT.tcr1 hT.tcr2) hT.tcrLen) hT.tcrK)) hud)
          hT.pre) hT.tcrT
      _ = _ := by unfold composedBound; ring
  exact (ENNReal.add_le_add_iff_right hfin).1 (hlin.trans hle)

/-- Named hypotheses, SUF-CMA (PRF distinguishers `qbPrfWC sufCheck`, `qbPrfMsgWL sufCheck`). -/
abbrev TermBoundsSuf (c : Caps)
    (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
    (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (n : QromCounts) : Prop :=
  TermBounds c optRand pkSeedDist B
    (fun ω ↦ qPrfRealPr (skPrfC Link.vp (primsΩ ω)) (qbPrfWC sufCheck (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfIdealPr (qbPrfWC sufCheck (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω)) (qbPrfMsgWL sufCheck (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfIdealPr (qbPrfMsgWL sufCheck (B ω)) (B ω).ρ₀) n

/-- Named hypotheses, EUF-CMA (PRF distinguishers `qbPrfC`, `qbPrfMsgL`). -/
abbrev TermBoundsEuf (c : Caps)
    (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
    (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (n : QromCounts) : Prop :=
  TermBounds c optRand pkSeedDist B
    (fun ω ↦ qPrfRealPr (skPrfC Link.vp (primsΩ ω)) (qbPrfC (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfIdealPr (qbPrfC (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω)) (qbPrfMsgL (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfIdealPr (qbPrfMsgL (B ω)) (B ω).ρ₀) n

lemma qPrfIdealPr_le_one' {D R : Type} [DecidableEq D] [SampleableType R]
    (X : QOC W (PRFScheme.PRFOracleSpec D R) Bool) {ρ : Matrix W W ℂ} (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) : qPrfIdealPr X ρ ≤ 1 := qWeight_le_one _ _ hρ h1

end

/-! ## The forger as one syntactic object -/

/-- Index type of a port forger's oracles: instruments, the hash port, uniform sampling, signing
queries `(M, ctx)`. -/
abbrev FIdx (X Y E : Type) [Fintype X] [Fintype Y] [Fintype E] : Type :=
  InstrIdx ((X × Y) × E) ⊕ (Unit ⊕ (ℕ ⊕ (List Byte × List Byte)))

/-- A signing query. -/
def isSign {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] : FIdx X Y E → Prop
  | .inr (.inr (.inr _)) => True
  | _ => False

instance {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] :
    DecidablePred (isSign (X := X) (Y := Y) (E := E)) := fun t ↦ by
  rcases t with _ | _ | _ | _ <;> unfold isSign <;> infer_instance

/-- A signing query within the message cap: `|M| + |ctx| + 2 ≤ c.ml` (the length of
`M' = 0 ‖ |ctx| ‖ ctx ‖ M`). -/
def capIdx {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] (c : Caps) : FIdx X Y E → Prop
  | .inr (.inr (.inr mc)) => mc.1.length + mc.2.length + 2 ≤ c.ml
  | _ => True

/-- A forgery within the message cap. -/
def capOut (c : Caps) : (List Byte × List Byte) × Option (List Byte) → Prop :=
  fun z ↦ z.1.1.length + z.1.2.length + 2 ≤ c.ml

/-- **A QROM forger against the external pure byte interface, as one program**: instruments on the
workspace `(X × Y) × E`, an oracle port on the `X × Y` factor, uniform sampling, signing queries.
Its syntax does not depend on the hash functions. -/
structure PortForger (X Y E : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Fintype E] [DecidableEq E] where
  /-- The program run on the encoded public key. -/
  main : List Byte → QOC ((X × Y) × E)
    (portSpec + (unifSpec + ((List Byte × List Byte) →ₒ Option (List Byte))))
    ((List Byte × List Byte) × Option (List Byte))
  /-- Initial state of the workspace (program register next to the trivial runtime register). -/
  ρ₀ : Matrix (WS X Y E) (WS X Y E) ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The Part-1 quantum forger of a port forger when the oracle port computes `H`. -/
noncomputable def PortForger.at {X Y E SK : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] [Fintype E] [DecidableEq E] (F : PortForger X Y E)
    (H : X → Y)
    (sigAlg : SignatureAlg ProbComp (List Byte × List Byte) (List Byte) SK (Option (List Byte))) :
    QForger (WS X Y E) sigAlg where
  main pk := compileQ H (F.main pk)
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

section port

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

/-- Oracle-independent signing randomness. -/
abbrev optRandOf (ω : Ω128 c) : PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y :=
  fun pk ↦ optRand₀ pk.pkSeed pk.pkRoot

/-- The scheme in world `ω`: SLH-DSA-SHA2-128s, external pure interface on byte strings, hash
components `ω`. -/
noncomputable abbrev algΩ (ω : Ω128 c) :=
  pureBytesAlg Link.vp (primsΩ ω) (codecR ω.toRand) (optRandOf c optRand₀ ω) pkSeedDist₀

/-- The internal forger of the reduction in world `ω`, built around the port forger. -/
noncomputable abbrev internalΩ (enc : Ω128 c → X → Y) (F : PortForger X Y E) (ω : Ω128 c) :=
  qPureBytesToInternal (F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))

/-- **Conditional composed theorem, SUF-CMA, FIPS 205 external pure interface on byte strings,
hash components uniformly random in `Ω128 c`.**  See the file header for the list of unproved
hypotheses (`hT`, with premises `hq`, `hqs`, `hcap`). -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_conditional
    (enc : Ω128 c → X → Y) (F : PortForger X Y E) (q qs : ℕ) (r : QromCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (hT : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      TermBoundsSuf c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ enc F) (countsOf q qs r)) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBound (countsOf q qs r) :=
  composed_of_linear (internalΩ c optRand₀ pkSeedDist₀ enc F) _ _ _ _ _ _
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ enc F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ enc F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ enc F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ enc F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (hT hq hqs hcap)

/-- **Conditional composed theorem, EUF-CMA** (same interface and hypotheses, PRF distinguishers
`qbPrfC`, `qbPrfMsgL`). -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_conditional
    (enc : Ω128 c → X → Y) (F : PortForger X Y E) (q qs : ℕ) (r : QromCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (hT : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      TermBoundsEuf c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ enc F) (countsOf q qs r)) :
    avΩ c (fun ω ↦ qUnforgeableAdvantage (F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBound (countsOf q qs r) :=
  composed_of_linear (internalΩ c optRand₀ pkSeedDist₀ enc F) _ _ _ _ _ _
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ enc F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ enc F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ enc F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ enc F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (hT hq hqs hcap)

end port

end Reduction

#print axioms Reduction.composed_of_linear
#print axioms Reduction.composedBound_zeroPre
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_conditional
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_conditional
