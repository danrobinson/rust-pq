import Ideal.Compose

/-!
# SLH-DSA-SHA2-128s in the ideal-compression-function model: numeric corollaries

`Realizers` bundles the eleven realisability hypotheses of `Ideal.suf_ideal_bound` /
`Ideal.euf_ideal_bound` with their query parameters; `Realizers.Le Qc N qs ℓ` says that

* every own-compression-query parameter (`q`, `q₁`, `q₂`) is at most `Qc`,
* every challenge / collection / `PRF`-oracle query count is at most `N`,
* the `PRF_msg` distinguisher makes at most `qs` oracle queries (one per signing query), on
  messages of at most `64 ℓ` bytes (`ℓ` SHA-256 blocks),
* every collection query has at most `10` blocks after the first.

`suf_ideal_bound_numeric` (uniform public seed, so `γ = 2^-128`):

`sufI S ≤ εI + (66 Qc + 40) / 2^128 + polyP Qc N qs ℓ / 2^256`,
`polyP = (Qc + N)² + (Qc + qs (ℓ + 1) + 2)² + 18 (2 Qc + 22 N + 21)² + 18 (2 Qc + 22 N + 9)²
          + 78 Qc + 1433 N + 47`

(`εI` bounds the table-averaged ITSR advantage of `H_msg`, which is not analysed here), for
`Qc ≤ 2^126`.  Two closed evaluations, at `N = 2^81`, `qs = 2^64`, `ℓ = 2^20`:

* `suf_ideal_bound_2_65` : `Qc = 2^65` gives `sufI S ≤ εI + 2^-56`;
* `suf_ideal_bound_2_90` : `Qc = 2^90` gives `sufI S ≤ εI + 2^-31`.

**Reading of the two evaluations.**  `Qc` bounds the compression queries of the *realisers*,
i.e. of the Reduction's adversaries once their hash evaluations are oracle queries.  (b)
`Qc = 2^90` corresponds to counting ALL post-seed hash evaluations of the reduction adversaries
as adversarial queries: about `qs · 2^21` hash calls of at most 11 blocks at `qs = 2^64` signing
queries (the resource bounds `final_resources_final_128s` of `Reduction/ResourcesFinal.lean`),
plus the forger's own queries.  (a) `Qc = 2^65` corresponds to counting only the forger's own
`2^64` compression queries plus lower-order terms; to justify it one would need ideal-model
bounds that charge only the queries at cells not already determined by the pre-seed phase (the
reduction's re-evaluations of values it has already computed are not "new" queries).  Such
refined bounds are NOT proved; (a) is a theorem only under the stated hypothesis that realisers
with these parameters exist.  In both cases the existence of the realisers is a hypothesis.

The same for EUF-CMA: `euf_ideal_bound_numeric`, `euf_ideal_bound_2_65`, `euf_ideal_bound_2_90`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

/-! ## The normal form `a / 2^128 + b / 2^256` -/

/-- `a / 2^128 + b / 2^256`. -/
noncomputable def nf (a b : ℕ) : ℝ≥0∞ :=
  (a : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + (b : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹

theorem nf_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : nf a b ≤ nf a' b' := by
  unfold nf
  gcongr

theorem nf_add (a b a' b' : ℕ) : nf a b + nf a' b' = nf (a + a') (b + b') := by
  unfold nf
  push_cast
  ring

theorem nf_mul (k a b : ℕ) : (k : ℝ≥0∞) * nf a b = nf (k * a) (k * b) := by
  unfold nf
  push_cast
  ring

theorem inv_pow_split (m k : ℕ) :
    ((2 : ℝ≥0∞) ^ k)⁻¹ = (2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞) ^ (m + k))⁻¹ := by
  have h0 : (2 : ℝ≥0∞) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : (2 : ℝ≥0∞) ^ m ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [pow_add, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), ← mul_assoc,
    ENNReal.mul_inv_cancel h0 ht, one_mul]

/-- `a / 2^128 + b / 2^256 ≤ 2^-k` as soon as `a · 2^128 + b ≤ 2^(256 - k)`. -/
theorem nf_le_inv_pow {a b : ℕ} (k m : ℕ) (hkm : m + k = 256)
    (h : a * 2 ^ 128 + b ≤ 2 ^ m) : nf a b ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  have e1 : nf a b = ((a * 2 ^ 128 + b : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
    unfold nf
    rw [inv_pow_split 128 128]
    push_cast
    ring
  rw [e1, inv_pow_split m k, hkm]
  have h' : ((a * 2 ^ 128 + b : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ m := by
    have := Nat.cast_le (α := ℝ≥0∞) |>.mpr h
    simpa using this
  exact mul_le_mul_left h' _

/-! ## Parameter bounds -/

/-- All compression-query parameters at most `Qc`, challenge queries at most `N`. -/
def P3.Le (p : P3) (Qc N : ℕ) : Prop := p.q₁ ≤ Qc ∧ p.qch ≤ N ∧ p.q₂ ≤ Qc

/-- All compression-query parameters at most `Qc`, challenge and collection queries at most `N`,
continuation length at most `10`. -/
def P5.Le (p : P5) (Qc N : ℕ) : Prop :=
  p.q₁ ≤ Qc ∧ p.qch ≤ N ∧ p.qc ≤ N ∧ p.L ≤ 10 ∧ p.q₂ ≤ Qc

/-- `2^-128`, the point probability of a uniform public seed. -/
noncomputable abbrev γu : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 128)⁻¹

theorem epsPrf_le {q qO Qc N : ℕ} (hq : q ≤ Qc) (hO : qO ≤ N) :
    epsPrf q qO ≤ nf Qc ((Qc + N) ^ 2) := by
  have e : epsPrf q qO = nf q ((q + qO) ^ 2) := by
    unfold epsPrf nf
    simp only [div_eq_mul_inv]
  rw [e]
  exact nf_mono hq (Nat.pow_le_pow_left (by omega) 2)

theorem epsMsg_le {q qO mlen Qc qs ℓ : ℕ} (hq : q ≤ Qc) (hO : qO ≤ qs) (hm : mlen ≤ 64 * ℓ) :
    epsMsg q qO mlen ≤ nf (2 * Qc) ((Qc + qs * (ℓ + 1) + 2) ^ 2) := by
  have e : epsMsg q qO mlen = nf (2 * q) ((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2) := by
    unfold epsMsg nf
    simp only [div_eq_mul_inv]
    push_cast
    ring
  rw [e]
  have h1 : qO * ((mlen + 24) / 64 + 1) ≤ qs * (ℓ + 1) := Nat.mul_le_mul hO (by omega)
  exact nf_mono (by omega) (Nat.pow_le_pow_left (by omega) 2)

theorem epsDspr_le {p : P3} {Qc N : ℕ} (h : p.Le Qc N) :
    epsDspr γu p ≤ nf (2 * Qc) (4 * Qc + 2 * N + 3) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : epsDspr γu p = nf (2 * p.q₁) (4 * p.q₁ + 2 * p.qch + 3) := by
    unfold epsDspr nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

theorem epsForsTcr_le {p : P3} {Qc N : ℕ} (h : p.Le Qc N) :
    epsForsTcr γu p ≤ nf (2 * Qc + 1) (2 * Qc + N + 2) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : epsForsTcr γu p = nf (p.q₂ + 1 + p.q₁) (2 * p.q₁ + p.qch + 2) := by
    unfold epsForsTcr nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

theorem coll_le {p : P5} {Qc N : ℕ} (h : p.Le Qc N) (c d : ℕ) (hd : c ≤ d) :
    (p.qch + p.qc) * c ≤ 2 * d * N := by
  obtain ⟨_, h2, h3, _, _⟩ := h
  calc (p.qch + p.qc) * c ≤ (2 * N) * d := Nat.mul_le_mul (by omega) hd
    _ = 2 * d * N := by ring

theorem epsTcr_le {p : P5} {Qc N : ℕ} (h : p.Le Qc N) :
    epsTcr γu p ≤ nf (2 * Qc + 1) (2 * Qc + 42 * N + 2) := by
  have hc := coll_le h (1 + 2 * p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsTcr γu p =
      nf (p.q₂ + 1 + p.q₁) (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 2) := by
    unfold epsTcr nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

theorem epsTcrLen_le {p : P5} {Qc N : ℕ} (h : p.Le Qc N) :
    epsTcrLen γu p ≤
      nf (2 * Qc + 22) (18 * (2 * Qc + 22 * N + 21) ^ 2 + 2 * Qc + 42 * N + 1) := by
  have hc1 := coll_le h (1 + max 9 p.L) 11 (by have := h.2.2.2.1; omega)
  have hc2 := coll_le h (1 + 2 * max 9 p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsTcrLen γu p = nf (p.q₂ + 22 + p.q₁)
      (18 * (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 9 p.L) + 21) ^ 2 + 2 * p.q₁ +
        (p.qch + p.qc) * (1 + 2 * max 9 p.L) + 1) := by
    unfold epsTcrLen nf
    push_cast
    ring
  rw [e]
  have hsq : (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 9 p.L) + 21) ^ 2 ≤
      (2 * Qc + 22 * N + 21) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact nf_mono (by omega) (by linarith)

theorem epsTcrK_le {p : P5} {Qc N : ℕ} (h : p.Le Qc N) :
    epsTcrK γu p ≤
      nf (2 * Qc + 10) (18 * (2 * Qc + 22 * N + 9) ^ 2 + 2 * Qc + 42 * N + 1) := by
  have hc1 := coll_le h (1 + max 3 p.L) 11 (by have := h.2.2.2.1; omega)
  have hc2 := coll_le h (1 + 2 * max 3 p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsTcrK γu p = nf (p.q₂ + 10 + p.q₁)
      (18 * (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 3 p.L) + 9) ^ 2 + 2 * p.q₁ +
        (p.qch + p.qc) * (1 + 2 * max 3 p.L) + 1) := by
    unfold epsTcrK nf
    push_cast
    ring
  rw [e]
  have hsq : (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 3 p.L) + 9) ^ 2 ≤
      (2 * Qc + 22 * N + 9) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact nf_mono (by omega) (by linarith)

theorem epsUd_le {p : P5} {Qc N : ℕ} (h : p.Le Qc N) :
    epsUd γu p ≤ nf (3 * Qc) (4 * Qc + 84 * N + 2) := by
  have hc := coll_le h (1 + 2 * p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsUd γu p =
      nf (p.q₂ + 2 * p.q₁) (2 * (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 1)) := by
    unfold epsUd nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

theorem epsPre_le {p : P5} {Qc N : ℕ} (h : p.Le Qc N) :
    epsPre γu p ≤ nf (3 * Qc + 2) (2 * Qc + 42 * N + 2) := by
  have hc := coll_le h (1 + 2 * p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsPre γu p =
      nf (2 * (p.q₂ + 1) + p.q₁) (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 2) := by
    unfold epsPre nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

/-! ## The bundle of realisers -/

/-- The eleven realisability hypotheses for families `B₁, …, B₈` of adversaries against the
games over the tables, with their query parameters. -/
structure Realizers (pkSeedDist : ProbComp (Bytes 16))
    (B₁ : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y)
    (B₂ : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g)))
    (D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (C₁ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 1))
    (C₂ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 2))
    (C₃ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.len))
    (C₄ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.k))
    (B₆ : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (B₇ : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (B₈ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist)) where
  q : ℕ
  qO : ℕ
  qm : ℕ
  qOm : ℕ
  mlen : ℕ
  pD : P3
  pT : P3
  pF : P5
  pH : P5
  pL : P5
  pK : P5
  pU : P5
  pP : P5
  pW : P5
  prf : RealizesPrf B₁ q qO
  msg : RealizesMsg B₂ qm qOm mlen
  dspr : RealizesDspr pkSeedDist D pD
  forsTcr : RealizesForsTcr pkSeedDist T pT
  tcrF : RealizesTcr pkSeedDist 1 C₁ pF
  tcrH : RealizesTcr pkSeedDist 2 C₂ pH
  tcrLen : RealizesTcr pkSeedDist Link.vp.params.len C₃ pL
  tcrK : RealizesTcr pkSeedDist Link.vp.params.k C₄ pK
  ud : RealizesUd pkSeedDist B₆ pU
  pre : RealizesPre pkSeedDist B₇ pP
  wotsTcr : RealizesWotsTcr pkSeedDist B₈ pW

section Bundle

variable {pkSeedDist : ProbComp (Bytes 16)}
  {B₁ : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y}
  {B₂ : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g))}
  {D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {C₁ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 1)}
  {C₂ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 2)}
  {C₃ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.len)}
  {C₄ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.k)}
  {B₆ : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {B₇ : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {B₈ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist)}

/-- The sum of the eleven explicit ideal-model bounds at the realisers' parameters. -/
noncomputable def Realizers.eps (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    (γ : ℝ≥0∞) : ℝ≥0∞ :=
  epsPrf R.q R.qO + epsMsg R.qm R.qOm R.mlen +
    (epsDspr γ R.pD + 3 * epsForsTcr γ R.pT) +
    (epsTcr γ R.pF + epsTcr γ R.pH + epsTcrLen γ R.pL + epsTcrK γ R.pK) +
    14 * epsUd γ R.pU + epsPre γ R.pP + epsTcr γ R.pW

/-- The resource bounds on the realisers (see the file header). -/
structure Realizers.Le (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    (Qc N qs ℓ : ℕ) : Prop where
  q : R.q ≤ Qc
  qO : R.qO ≤ N
  qm : R.qm ≤ Qc
  qOm : R.qOm ≤ qs
  mlen : R.mlen ≤ 64 * ℓ
  pD : R.pD.Le Qc N
  pT : R.pT.Le Qc N
  pF : R.pF.Le Qc N
  pH : R.pH.Le Qc N
  pL : R.pL.Le Qc N
  pK : R.pK.Le Qc N
  pU : R.pU.Le Qc N
  pP : R.pP.Le Qc N
  pW : R.pW.Le Qc N

/-- The polynomial of the `2^-256` term. -/
def polyP (Qc N qs ℓ : ℕ) : ℕ :=
  (Qc + N) ^ 2 + (Qc + qs * (ℓ + 1) + 2) ^ 2 + 18 * (2 * Qc + 22 * N + 21) ^ 2 +
    18 * (2 * Qc + 22 * N + 9) ^ 2 + 78 * Qc + 1433 * N + 47

/-- The explicit bounds at a uniform seed, under the resource bounds, in normal form. -/
theorem Realizers.eps_le (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    {Qc N qs ℓ : ℕ} (h : R.Le Qc N qs ℓ) :
    R.eps γu ≤ nf (66 * Qc + 40) (polyP Qc N qs ℓ) := by
  have e : nf (66 * Qc + 40) (polyP Qc N qs ℓ) =
      nf Qc ((Qc + N) ^ 2) + nf (2 * Qc) ((Qc + qs * (ℓ + 1) + 2) ^ 2) +
      (nf (2 * Qc) (4 * Qc + 2 * N + 3) + 3 * nf (2 * Qc + 1) (2 * Qc + N + 2)) +
      (nf (2 * Qc + 1) (2 * Qc + 42 * N + 2) + nf (2 * Qc + 1) (2 * Qc + 42 * N + 2) +
        nf (2 * Qc + 22) (18 * (2 * Qc + 22 * N + 21) ^ 2 + 2 * Qc + 42 * N + 1) +
        nf (2 * Qc + 10) (18 * (2 * Qc + 22 * N + 9) ^ 2 + 2 * Qc + 42 * N + 1)) +
      14 * nf (3 * Qc) (4 * Qc + 84 * N + 2) + nf (3 * Qc + 2) (2 * Qc + 42 * N + 2) +
      nf (2 * Qc + 1) (2 * Qc + 42 * N + 2) := by
    unfold nf polyP
    push_cast
    ring
  rw [e]
  unfold Realizers.eps
  gcongr
  · exact epsPrf_le h.q h.qO
  · exact epsMsg_le h.qm h.qOm h.mlen
  · exact epsDspr_le h.pD
  · exact epsForsTcr_le h.pT
  · exact epsTcr_le h.pF
  · exact epsTcr_le h.pH
  · exact epsTcrLen_le h.pL
  · exact epsTcrK_le h.pK
  · exact epsUd_le h.pU
  · exact epsPre_le h.pP
  · exact epsTcr_le h.pW

end Bundle

theorem hγ_uniform (s : Bytes 16) : Pr{let s' ← $ᵗ (Bytes 16)}[s' = s] ≤ γu :=
  (prEvent_uniform_bytes16_eq s).le

/-! ## SUF-CMA -/

section Suf

variable (S : ForgerI)
  (optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
  (pkSeedDist : ProbComp (Bytes 16))

/-- The realisers of the Reduction's SUF adversaries built from the ideal-model forger `S`
(`T g = S.typedS optRand pkSeedDist g`). -/
abbrev SufRealizers : Type 1 :=
  Realizers pkSeedDist
    (fun g => Reduction.bPrfWC Reduction.sufCheck (S.typedS optRand pkSeedDist g))
    (fun g => Reduction.Lazy.bPrfMsgWL Reduction.sufCheck (S.typedS optRand pkSeedDist g))
    (fun g => Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedS optRand pkSeedDist g)))
    (fun g => Reduction.toTcr (Reduction.Lazy.bOpenPreS (S.typedS optRand pkSeedDist g)))
    (fun g => Reduction.bTcrArM 1 (S.typedS optRand pkSeedDist g))
    (fun g => Reduction.bTcrArM 2 (S.typedS optRand pkSeedDist g))
    (fun g => Reduction.bTcrArM Link.vp.params.len (S.typedS optRand pkSeedDist g))
    (fun g => Reduction.bTcrArM Link.vp.params.k (S.typedS optRand pkSeedDist g))
    (fun g => Reduction.rUd pkSeedDist (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g)))
    (fun g => Reduction.rPre pkSeedDist (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g)))
    (fun g => Reduction.rTcrT pkSeedDist (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g)))

variable {S optRand pkSeedDist}

/-- `suf_ideal_bound` with the realisers bundled. -/
theorem suf_ideal_bound' {γ : ℝ≥0∞} (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrSufI S optRand pkSeedDist ≤ εI)
    (R : SufRealizers S optRand pkSeedDist) (hD : R.pD.q₂ ≤ 2 ^ 126) :
    sufI S optRand pkSeedDist ≤ εI + R.eps γ := by
  refine (suf_ideal_bound hγ hI R.prf R.msg R.dspr hD R.forsTcr R.tcrF R.tcrH R.tcrLen R.tcrK
    R.ud R.pre R.wotsTcr).trans (le_of_eq ?_)
  unfold Realizers.eps
  ring

end Suf

section SufNumeric

variable {S : ForgerI}
  {optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y}

/-- **Numeric SUF-CMA bound in the ideal-compression model** (uniform public seed). -/
theorem suf_ideal_bound_numeric {εI : ℝ≥0∞}
    (hI : itsrSufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : SufRealizers S optRand ($ᵗ (Bytes 16))) {Qc N qs ℓ : ℕ} (h : R.Le Qc N qs ℓ)
    (hQ : Qc ≤ 2 ^ 126) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      εI + ((66 * Qc + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 + (polyP Qc N qs ℓ : ℝ≥0∞) / 2 ^ 256 := by
  refine (suf_ideal_bound' hγ_uniform hI R (h.pD.2.2.trans hQ)).trans ?_
  rw [add_assoc]
  exact add_le_add le_rfl (R.eps_le h)

/-- The numeric bound is at most `εI + 2^-k` whenever
`(66 Qc + 40) · 2^128 + polyP Qc N qs ℓ ≤ 2^(256 - k)`. -/
theorem suf_ideal_bound_pow {εI : ℝ≥0∞}
    (hI : itsrSufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : SufRealizers S optRand ($ᵗ (Bytes 16))) {Qc N qs ℓ : ℕ} (h : R.Le Qc N qs ℓ)
    (hQ : Qc ≤ 2 ^ 126) (k m : ℕ) (hkm : m + k = 256)
    (hnum : (66 * Qc + 40) * 2 ^ 128 + polyP Qc N qs ℓ ≤ 2 ^ m) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤ εI + ((2 : ℝ≥0∞) ^ k)⁻¹ :=
  (suf_ideal_bound' hγ_uniform hI R (h.pD.2.2.trans hQ)).trans
    (add_le_add le_rfl ((R.eps_le h).trans (nf_le_inv_pow k m hkm hnum)))

theorem num_2_65 :
    (66 * 2 ^ 65 + 40) * 2 ^ 128 + polyP (2 ^ 65) (2 ^ 81) (2 ^ 64) (2 ^ 20) ≤ 2 ^ 200 := by
  unfold polyP
  norm_num

theorem num_2_90 :
    (66 * 2 ^ 90 + 40) * 2 ^ 128 + polyP (2 ^ 90) (2 ^ 81) (2 ^ 64) (2 ^ 20) ≤ 2 ^ 225 := by
  unfold polyP
  norm_num

/-- **(a)** Realisers with at most `2^65` compression queries, `2^81` challenge / collection /
PRF-oracle queries, `2^64` signing queries on messages of at most `2^20` blocks:
`sufI S ≤ εI + 2^-56`. -/
theorem suf_ideal_bound_2_65 {εI : ℝ≥0∞}
    (hI : itsrSufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 65) (2 ^ 81) (2 ^ 64) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤ εI + ((2 : ℝ≥0∞) ^ 56)⁻¹ :=
  suf_ideal_bound_pow hI R h (by norm_num) 56 200 rfl num_2_65

/-- **(b)** Realisers with at most `2^90` compression queries (all post-seed hash evaluations of
the reduction adversaries counted as queries), `2^81` challenge / collection / PRF-oracle
queries, `2^64` signing queries on messages of at most `2^20` blocks: `sufI S ≤ εI + 2^-31`. -/
theorem suf_ideal_bound_2_90 {εI : ℝ≥0∞}
    (hI : itsrSufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 90) (2 ^ 81) (2 ^ 64) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤ εI + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  suf_ideal_bound_pow hI R h (by norm_num) 31 225 rfl num_2_90

end SufNumeric

/-! ## EUF-CMA -/

section Euf

variable (S : ForgerI)
  (optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
  (pkSeedDist : ProbComp (Bytes 16))

/-- The realisers of the Reduction's EUF adversaries built from the ideal-model forger `S`
(`T g = S.typedE optRand pkSeedDist g`). -/
abbrev EufRealizers : Type 1 :=
  Realizers pkSeedDist
    (fun g => Reduction.bPrfC (S.typedE optRand pkSeedDist g))
    (fun g => Reduction.Lazy.bPrfMsgL (S.typedE optRand pkSeedDist g))
    (fun g => Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedE optRand pkSeedDist g)))
    (fun g => Reduction.toTcr (Reduction.Lazy.bOpenPreS (S.typedE optRand pkSeedDist g)))
    (fun g => Reduction.bTcrArM 1 (S.typedE optRand pkSeedDist g))
    (fun g => Reduction.bTcrArM 2 (S.typedE optRand pkSeedDist g))
    (fun g => Reduction.bTcrArM Link.vp.params.len (S.typedE optRand pkSeedDist g))
    (fun g => Reduction.bTcrArM Link.vp.params.k (S.typedE optRand pkSeedDist g))
    (fun g => Reduction.rUd pkSeedDist (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g)))
    (fun g => Reduction.rPre pkSeedDist (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g)))
    (fun g => Reduction.rTcrT pkSeedDist (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g)))

variable {S optRand pkSeedDist}

/-- `euf_ideal_bound` with the realisers bundled. -/
theorem euf_ideal_bound' {γ : ℝ≥0∞} (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrEufI S optRand pkSeedDist ≤ εI)
    (R : EufRealizers S optRand pkSeedDist) (hD : R.pD.q₂ ≤ 2 ^ 126) :
    eufI S optRand pkSeedDist ≤ εI + R.eps γ := by
  refine (euf_ideal_bound hγ hI R.prf R.msg R.dspr hD R.forsTcr R.tcrF R.tcrH R.tcrLen R.tcrK
    R.ud R.pre R.wotsTcr).trans (le_of_eq ?_)
  unfold Realizers.eps
  ring

end Euf

section EufNumeric

variable {S : ForgerI}
  {optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y}

/-- **Numeric EUF-CMA bound in the ideal-compression model** (uniform public seed). -/
theorem euf_ideal_bound_numeric {εI : ℝ≥0∞}
    (hI : itsrEufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : EufRealizers S optRand ($ᵗ (Bytes 16))) {Qc N qs ℓ : ℕ} (h : R.Le Qc N qs ℓ)
    (hQ : Qc ≤ 2 ^ 126) :
    eufI S optRand ($ᵗ (Bytes 16)) ≤
      εI + ((66 * Qc + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 + (polyP Qc N qs ℓ : ℝ≥0∞) / 2 ^ 256 := by
  refine (euf_ideal_bound' hγ_uniform hI R (h.pD.2.2.trans hQ)).trans ?_
  rw [add_assoc]
  exact add_le_add le_rfl (R.eps_le h)

theorem euf_ideal_bound_pow {εI : ℝ≥0∞}
    (hI : itsrEufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : EufRealizers S optRand ($ᵗ (Bytes 16))) {Qc N qs ℓ : ℕ} (h : R.Le Qc N qs ℓ)
    (hQ : Qc ≤ 2 ^ 126) (k m : ℕ) (hkm : m + k = 256)
    (hnum : (66 * Qc + 40) * 2 ^ 128 + polyP Qc N qs ℓ ≤ 2 ^ m) :
    eufI S optRand ($ᵗ (Bytes 16)) ≤ εI + ((2 : ℝ≥0∞) ^ k)⁻¹ :=
  (euf_ideal_bound' hγ_uniform hI R (h.pD.2.2.trans hQ)).trans
    (add_le_add le_rfl ((R.eps_le h).trans (nf_le_inv_pow k m hkm hnum)))

theorem euf_ideal_bound_2_65 {εI : ℝ≥0∞}
    (hI : itsrEufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : EufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 65) (2 ^ 81) (2 ^ 64) (2 ^ 20)) :
    eufI S optRand ($ᵗ (Bytes 16)) ≤ εI + ((2 : ℝ≥0∞) ^ 56)⁻¹ :=
  euf_ideal_bound_pow hI R h (by norm_num) 56 200 rfl num_2_65

theorem euf_ideal_bound_2_90 {εI : ℝ≥0∞}
    (hI : itsrEufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : EufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 90) (2 ^ 81) (2 ^ 64) (2 ^ 20)) :
    eufI S optRand ($ᵗ (Bytes 16)) ≤ εI + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  euf_ideal_bound_pow hI R h (by norm_num) 31 225 rfl num_2_90

end EufNumeric

end Ideal

#print axioms Ideal.Realizers.eps_le
#print axioms Ideal.suf_ideal_bound'
#print axioms Ideal.suf_ideal_bound_numeric
#print axioms Ideal.suf_ideal_bound_2_65
#print axioms Ideal.suf_ideal_bound_2_90
#print axioms Ideal.euf_ideal_bound_numeric
#print axioms Ideal.euf_ideal_bound_2_65
#print axioms Ideal.euf_ideal_bound_2_90
