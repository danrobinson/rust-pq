import Ideal.ComposeNumeric
import Ideal.Inst.ItsrFine128

/-!
# The composed ideal-compression bound with the repaired ITSR leg and honest caps

This file supersedes the closed corollaries `suf_closed_2_64_memo`, `suf_closed_2_64_store`,
`suf_closed_2_60_2_40`, `suf_closed_2_40_2_20` of `Ideal/ComposeNumeric.lean` (their ITSR
realiser `RealizesItsr … (2^64) …` charges every compression query of the Reduction's ITSR
adversary, which signs every query itself; and the `R.Le (2^68)`/`(2^61)`/`(2^41)` caps are not
met by the adversaries named in `SufRealizers`).

**What is proved here, and what is still assumed.**

* `RealizesItsrF B qP cP q qc Lc qs ℓ`: the twelfth realiser in the form needed by the repaired
  ITSR bound `Ideal.itsr_bound_128s_fine` — ONE program `A` with raw compression queries, chain
  queries (Merkle–Damgård from the SHA-256 initial value), target queries, such that the ITSR
  advantage of `B g` is that of `A` instantiated at `g`, with
  `qP` raw queries whose block is the constant block `cB`, `cP` chain queries whose second block
  is `cB`, `q` raw queries, `qc` chain queries of at most `Lc` blocks, `qs` target queries on
  messages of at most `ℓ` bytes.
* `suf_final`: for a uniform public seed,
  `sufI S ≤ epsItsrF qP cP q qc Lc qs ℓ + (66 Qc + 40)/2^128 + polyP Qc N qs' ℓ' / 2^256`
  from `RealizesItsrF` for `Reduction.Lazy.bItsrL` and `SufRealizers` with `R.Le Qc N qs' ℓ'`.
* closed evaluations `suf_final_2_60_2_20`, `suf_final_2_80_2_40`, `suf_final_2_90_2_64`.

**All twelve realisers remain hypotheses** (`SufRealizers`: eleven; `RealizesItsrF`: one).  None
is discharged in this development.  The obstruction found when attempting it: the Reduction's
adversaries are built over types indexed by the core bundle `(primsG (liftC g)).core`
(`PublicKeyCore`, `Signature`, `G2Log`, `Lazy.OSpec`), and that core contains the functions `PRF`
and `PRF_msg`, which depend on `g`.  The uniformity statements of `Reduction/Open` (`withTH`)
replace `Thash`/`H_msg` only and keep the core fixed; a realiser needs the open programs at
`primsG (liftC g)` and `primsG (liftC g')` identified, i.e. transports of every core-indexed type
through every reduction program, which do not exist.

**Caps.**  The caps in the closed theorems are chosen to leave room for the Reduction's own
hashing as counted in `Reduction/Open` (`status/OPEN.md` §2: at most
`269824 + qs·2007385 + 7857` hash calls per adversary, each at most 12 compression calls, plus
`H_msg`/`PRF_msg` on at most `qs + 1` messages).  That the realisers meet these caps is part of
the hypotheses, not a theorem.

**ITSR leg.**  `epsItsrF` is informative while `qP + cP + 2 (qs + 1)` stays below about
`2^69.8` (`reuseSum_63_12_14_le_of`: `n ≤ r·2^63` gives `r·∏_{i<14}(i+r)/2^105`), whatever the
total number of compression queries.  `qP` counts the forger's own compression queries with
block `cB` (the realiser forwards them); a forger may make ALL its queries of that shape, so for
`qP = Qc ≥ 2^70` the bound is vacuous.  This is a limitation of the proof (every such query is a
potential coverer), not an attack.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal KeyedHash

namespace Ideal

open Ideal.Itsr

/-! ## The twelfth realiser, fine form -/

/-- Realiser for a family of ITSR adversaries, with the fine accounting of
`Ideal.itsr_bound_128s_fine`. -/
structure RealizesItsrF
    (B : ∀ g : CF St Blk, ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g))))
    (qP cP q qc Lc qs ℓ : ℕ) where
  /-- the ideal-model adversary -/
  A : OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X128 (Bytes 16))) (Bytes 16 × X128)
  eq : ∀ g, KeyedHash.ITSRAdvantage (B g) = KeyedHash.ITSRAdvantage (instItsrF A g)
  hqP : IsQueryBoundP A (fun i => rawB (X := X128) (fun t : St × Blk => P128 t.2) i = true) qP
  hcP : IsQueryBoundP A (fun i => chB (St := St) (X := X128) (secondP P128) i = true) cP
  hq : IsQueryBoundP A (fun i => rawB (X := X128) (fun _ : St × Blk => true) i = true) q
  hqc : IsQueryBoundP A
    (fun i => chB (St := St) (X := X128) (fun _ : List Blk => true) i = true) qc
  hLc : AllQueriesSatisfy A (chOK (St := St) (X := X128) fun bs : List Blk => bs.length ≤ Lc)
  hqs : IsQueryBoundP A (fun i => isTgtF (St := St) (Blk := Blk) (X := X128) i = true) qs
  htgt : AllQueriesSatisfy A (tgtOKF (St := St) (Blk := Blk) (msgLe ℓ))
  hout : ∀ kx ∈ support A, msgLe ℓ kx

/-- The error term of `itsr_bound_128s_fine`. -/
noncomputable def epsItsrF (qP cP q qc Lc qs ℓ : ℕ) : ℝ≥0∞ :=
  reuseSum 63 12 14 (qP + cP + 2 * (qs + 1)) +
    (((q + qc * Lc + (qs + 1) * ((ℓ + 56) / 64 + 3)) ^ 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹

theorem cfAvg_itsr_le_fine
    {B : ∀ g : CF St Blk, ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g)))}
    {qP cP q qc Lc qs ℓ : ℕ} (R : RealizesItsrF B qP cP q qc Lc qs ℓ) :
    (cfAvg fun g => KeyedHash.ITSRAdvantage (B g)) ≤ epsItsrF qP cP q qc Lc qs ℓ := by
  have h1 : (cfAvg fun g => KeyedHash.ITSRAdvantage (B g)) =
      cfAvg fun g => 𝒟[ITSRExperiment (instItsrF R.A g)] {true} :=
    cfAvg_congr fun g => (R.eq g).trans (ITSRAdvantage_eq_evalDist_experiment _)
  have h2 : itsrIF R.A = cfAvg fun g => 𝒟[ITSRExperiment (instItsrF R.A g)] {true} :=
    cfAdvantage_eq_cfAvg _
  rw [h1, ← h2]
  exact itsr_bound_128s_fine R.A qP cP q qc Lc qs ℓ R.hqP R.hcP R.hq R.hqc R.hLc R.hqs R.htgt
    R.hout

/-! ## Numerics of the coverage sum beyond `7·2^63` -/

/-- `n ≤ r·2^63`: the coverage sum is at most `2^-c` whenever
`r·2^63·∏_{i<14}(i + r)·2^c ≤ 2^168`. -/
theorem reuseSum_63_12_14_le_of (n r c : ℕ) (hn : n ≤ r * 2 ^ 63)
    (hc : r * 2 ^ 63 * (∏ i ∈ Finset.range 14, (i + r)) * 2 ^ c ≤ 2 ^ 168) :
    reuseSum 63 12 14 n ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := by
  have hρ : (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 63)⁻¹ ≤ r := by
    have h1 : (n : ℝ≥0∞) ≤ r * 2 ^ 63 := by exact_mod_cast hn
    calc (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 63)⁻¹ ≤ r * 2 ^ 63 * ((2 : ℝ≥0∞) ^ 63)⁻¹ :=
          mul_le_mul h1 le_rfl zero_le zero_le
      _ = r := by rw [mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by simp), mul_one]
  have hP : ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹) ≤
      ((∏ i ∈ Finset.range 14, (i + r) : ℕ) : ℝ≥0∞) := by
    calc ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹)
        ≤ ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + r) :=
          Finset.prod_le_prod (fun i _ => add_le_add le_rfl hρ)
      _ = ((∏ i ∈ Finset.range 14, (i + r) : ℕ) : ℝ≥0∞) := by push_cast; rfl
  calc reuseSum 63 12 14 n
      ≤ n * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14 *
          ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹) := reuseSum_le_prod _ _ _ _
    _ ≤ n * ((2 : ℝ≥0∞) ^ 168)⁻¹ * ((∏ i ∈ Finset.range 14, (i + r) : ℕ) : ℝ≥0∞) := by
        rw [inv12_pow14]; exact mul_le_mul le_rfl hP zero_le zero_le
    _ = ((n * ∏ i ∈ Finset.range 14, (i + r) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
        push_cast; ring
    _ ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := natMul_inv_pow_le _ _ _ (by
        calc n * (∏ i ∈ Finset.range 14, (i + r)) * 2 ^ c
            ≤ r * 2 ^ 63 * (∏ i ∈ Finset.range 14, (i + r)) * 2 ^ c := by gcongr
          _ ≤ 2 ^ 168 := hc)

/-- `n ≤ 11·2^63`: at most `2^-44`. -/
theorem reuseSum_63_12_14_le_r11 (n : ℕ) (hn : n ≤ 11 * 2 ^ 63) :
    reuseSum 63 12 14 n ≤ ((2 : ℝ≥0∞) ^ 44)⁻¹ :=
  reuseSum_63_12_14_le_of n 11 44 hn (by norm_num [Finset.prod_range_succ])

/-- `n ≤ 2^67`: at most `2^-38`. -/
theorem reuseSum_63_12_14_le_r16 (n : ℕ) (hn : n ≤ 16 * 2 ^ 63) :
    reuseSum 63 12 14 n ≤ ((2 : ℝ≥0∞) ^ 38)⁻¹ :=
  reuseSum_63_12_14_le_of n 16 38 hn (by norm_num [Finset.prod_range_succ])

/-- `n ≤ 2^68`: at most `2^-26`. -/
theorem reuseSum_63_12_14_le_r32 (n : ℕ) (hn : n ≤ 32 * 2 ^ 63) :
    reuseSum 63 12 14 n ≤ ((2 : ℝ≥0∞) ^ 26)⁻¹ :=
  reuseSum_63_12_14_le_of n 32 26 hn (by norm_num [Finset.prod_range_succ])

/-- `n ≤ 2^69`: at most `2^-13`. -/
theorem reuseSum_63_12_14_le_r64 (n : ℕ) (hn : n ≤ 64 * 2 ^ 63) :
    reuseSum 63 12 14 n ≤ ((2 : ℝ≥0∞) ^ 13)⁻¹ :=
  reuseSum_63_12_14_le_of n 64 13 hn (by norm_num [Finset.prod_range_succ])

/-! ## The composition -/

section

variable (S : ForgerI)
  (optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
  (pkSeedDist : ProbComp (Bytes 16))

/-- `hI` of `suf_ideal_bound` from the fine twelfth realiser. -/
theorem itsrSufI_le_fine {qP cP q qc Lc qs ℓ : ℕ}
    (R : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS optRand pkSeedDist g))
      qP cP q qc Lc qs ℓ) :
    itsrSufI S optRand pkSeedDist ≤ epsItsrF qP cP q qc Lc qs ℓ :=
  cfAvg_itsr_le_fine R

end

variable {S : ForgerI}
  {optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y}

/-- **SUF-CMA of SLH-DSA-SHA2-128s (byte level) in the ideal-compression-function model, with
the repaired ITSR leg** (uniform public seed).  Hypotheses: the twelve realisers (`RI`, `R`) with
their query parameters; nothing else.

`Qc` bounds the compression queries of the eleven realisers in `R` (the forger's own queries
plus the reduction's own hashing), `N` their challenge / collection / PRF-oracle queries, `qs'`
the `PRF_msg`-oracle queries, `64 ℓ'` the message length in bytes; the ITSR realiser has the
parameters of `RealizesItsrF`. -/
theorem suf_final {qP cP q qc Lc qs ℓ : ℕ}
    (RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS optRand ($ᵗ (Bytes 16)) g))
      qP cP q qc Lc qs ℓ)
    (R : SufRealizers S optRand ($ᵗ (Bytes 16))) {Qc N qs' ℓ' : ℕ} (h : R.Le Qc N qs' ℓ')
    (hQ : Qc ≤ 2 ^ 126) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      epsItsrF qP cP q qc Lc qs ℓ + ((66 * Qc + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP Qc N qs' ℓ' : ℝ≥0∞) / 2 ^ 256 :=
  suf_ideal_bound_numeric (itsrSufI_le_fine S optRand _ RI) R h hQ

theorem num_2_60 :
    (66 * 2 ^ 60 + 40) * 2 ^ 128 + polyP (2 ^ 60) (2 ^ 81) (2 ^ 20) (2 ^ 20) ≤ 2 ^ 195 := by
  unfold polyP; norm_num

theorem num_2_80 :
    (66 * 2 ^ 80 + 40) * 2 ^ 128 + polyP (2 ^ 80) (2 ^ 81) (2 ^ 40) (2 ^ 20) ≤ 2 ^ 215 := by
  unfold polyP; norm_num

theorem num_2_90' :
    (66 * 2 ^ 90 + 40) * 2 ^ 128 + polyP (2 ^ 90) (2 ^ 82) (2 ^ 64) (2 ^ 20) ≤ 2 ^ 225 := by
  unfold polyP; norm_num

/-- **`(Qc, qs) = (2^60, 2^20)`**, messages of at most `2^26` bytes.  No restriction on the shape
of the forger's queries: all `2^60` raw queries of the ITSR realiser may have block `cB`.

`sufI S ≤ 2^-70 + 2^-128 + 2^-61`.

Realiser caps: eleven games `2^60` compression queries, `2^81` challenge / collection /
PRF-oracle queries; ITSR realiser `≤ 2^60` raw queries, `≤ 2^60` chain queries with second block
`cB`, `≤ 2^42` chain queries of `≤ 2^21` blocks. -/
theorem suf_final_2_60_2_20
    (RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 60) (2 ^ 60) (2 ^ 60) (2 ^ 42) (2 ^ 21) (2 ^ 20) (2 ^ 26))
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 60) (2 ^ 81) (2 ^ 20) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  suf_ideal_bound_pow
    ((itsrSufI_le_fine S optRand _ RI).trans
      (add_le_add
        (reuseSum_63_12_14_le_small _ 62 70 (by norm_num) (by norm_num) (by norm_num))
        (natMul_inv_pow_le _ _ _ (by norm_num))))
    R h (by norm_num) 61 195 rfl num_2_60

/-- **`(Qc, qs) = (2^80, 2^40)`**, messages of at most `2^26` bytes, **under the additional cap
`2^64` on the ITSR realiser's raw queries with block `cB`** (the forger's own queries of that
shape) and on its chain queries with second block `cB`.  Without that cap (`qP = 2^80`) the ITSR
term is vacuous.

`sufI S ≤ 2^-50 + 2^-88 + 2^-41`. -/
theorem suf_final_2_80_2_40
    (RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 64) (2 ^ 64) (2 ^ 80) (2 ^ 62) (2 ^ 21) (2 ^ 40) (2 ^ 26))
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 80) (2 ^ 81) (2 ^ 40) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ :=
  suf_ideal_bound_pow
    ((itsrSufI_le_fine S optRand _ RI).trans
      (add_le_add (reuseSum_63_12_14_le_big _ (by norm_num))
        (natMul_inv_pow_le _ _ _ (by norm_num))))
    R h (by norm_num) 41 215 rfl num_2_80

/-- **`(Qc, qs) = (2^90, 2^64)`**, messages of at most `2^26` bytes, **under the additional cap
`2^64` on the ITSR realiser's raw queries with block `cB`** and `2^65` on its chain queries with
second block `cB`.  Without that cap (`qP = 2^90`) the ITSR term is vacuous.  `N = 2^82` (the
`PRF` distinguisher makes `17920 + qs·182784 > 2^81` oracle queries at `qs = 2^64`).

`sufI S ≤ 2^-44 + 2^-43 + 2^-31`. -/
theorem suf_final_2_90_2_64
    (RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 64) (2 ^ 65) (2 ^ 90) (2 ^ 85) (2 ^ 21) (2 ^ 64) (2 ^ 26))
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 90) (2 ^ 82) (2 ^ 64) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  suf_ideal_bound_pow
    ((itsrSufI_le_fine S optRand _ RI).trans
      (add_le_add (reuseSum_63_12_14_le_r11 _ (by norm_num))
        (natMul_inv_pow_le _ _ _ (by norm_num))))
    R h (by norm_num) 31 225 rfl num_2_90'

/-! ## EUF-CMA analogues -/

/-- `hI` of `euf_ideal_bound` from the fine twelfth realiser. -/
theorem itsrEufI_le_fine (S : ForgerI)
    (optRand : ∀ g : CF St Blk,
      PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
    (pkSeedDist : ProbComp (Bytes 16)) {qP cP q qc Lc qs ℓ : ℕ}
    (R : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE optRand pkSeedDist g))
      qP cP q qc Lc qs ℓ) :
    itsrEufI S optRand pkSeedDist ≤ epsItsrF qP cP q qc Lc qs ℓ :=
  cfAvg_itsr_le_fine R

/-- EUF-CMA analogue of `suf_final` (same hypotheses for the EUF adversaries). -/
theorem euf_final {qP cP q qc Lc qs ℓ : ℕ}
    (RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE optRand ($ᵗ (Bytes 16)) g))
      qP cP q qc Lc qs ℓ)
    (R : EufRealizers S optRand ($ᵗ (Bytes 16))) {Qc N qs' ℓ' : ℕ} (h : R.Le Qc N qs' ℓ')
    (hQ : Qc ≤ 2 ^ 126) :
    eufI S optRand ($ᵗ (Bytes 16)) ≤
      epsItsrF qP cP q qc Lc qs ℓ + ((66 * Qc + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP Qc N qs' ℓ' : ℝ≥0∞) / 2 ^ 256 :=
  euf_ideal_bound_numeric (itsrEufI_le_fine S optRand _ RI) R h hQ

/-- EUF-CMA analogue of `suf_final_2_60_2_20`. -/
theorem euf_final_2_60_2_20
    (RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 60) (2 ^ 60) (2 ^ 60) (2 ^ 42) (2 ^ 21) (2 ^ 20) (2 ^ 26))
    (R : EufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 60) (2 ^ 81) (2 ^ 20) (2 ^ 20)) :
    eufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  euf_ideal_bound_pow
    ((itsrEufI_le_fine S optRand _ RI).trans
      (add_le_add
        (reuseSum_63_12_14_le_small _ 62 70 (by norm_num) (by norm_num) (by norm_num))
        (natMul_inv_pow_le _ _ _ (by norm_num))))
    R h (by norm_num) 61 195 rfl num_2_60

/-- EUF-CMA analogue of `suf_final_2_90_2_64` (same extra cap `2^64` on raw `cB` queries). -/
theorem euf_final_2_90_2_64
    (RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 64) (2 ^ 65) (2 ^ 90) (2 ^ 85) (2 ^ 21) (2 ^ 64) (2 ^ 26))
    (R : EufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 90) (2 ^ 82) (2 ^ 64) (2 ^ 20)) :
    eufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  euf_ideal_bound_pow
    ((itsrEufI_le_fine S optRand _ RI).trans
      (add_le_add (reuseSum_63_12_14_le_r11 _ (by norm_num))
        (natMul_inv_pow_le _ _ _ (by norm_num))))
    R h (by norm_num) 31 225 rfl num_2_90'

/-! ## `opt_rand` independent of the table

`optRandU oR` is the family of `opt_rand` samplers that does not depend on the compression
table: at every `g` it is `oR PK.seed PK.root`.  (The FIPS choices are `fun s _ => pure s` and
`fun _ _ => $ᵗ (Bytes 16)`.)  For a family that depends on `g` the realiser hypotheses cannot be
expected to hold; the corollary below is `suf_final` at such a family. -/

/-- A table-independent family of `opt_rand` samplers. -/
def optRandU (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (g : CF St Blk)
    (pk : PublicKeyCore (primsG (liftC g)).core) : ProbComp (primsG (liftC g)).Y :=
  oR pk.pkSeed pk.pkRoot

/-- `suf_final` for a table-independent `opt_rand`. -/
theorem suf_final_optRandU (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qP cP q qc Lc qs ℓ : ℕ}
    (RI : RealizesItsrF
      (fun g => Reduction.Lazy.bItsrL (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))
      qP cP q qc Lc qs ℓ)
    (R : SufRealizers S (optRandU oR) ($ᵗ (Bytes 16))) {Qc N qs' ℓ' : ℕ}
    (h : R.Le Qc N qs' ℓ') (hQ : Qc ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qP cP q qc Lc qs ℓ + ((66 * Qc + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP Qc N qs' ℓ' : ℝ≥0∞) / 2 ^ 256 :=
  suf_final RI R h hQ

/-! ## A sanity lemma for the chain-query accounting

Every single-input tweakable-hash evaluation (`F`, and `PRF` on the secret-key domain) is a chain
whose second block has the padding byte `0x80` at position 38, where `cB` is zero: such chain
queries are not counted in `cP`.  (The corresponding statements for `H`, `T_k`, `T_len` — padding
byte at position 54, resp. the address-type byte at position 9 — and the fact that the realising
program issues only such chains are not proved.) -/

theorem cB_get38 : cB[38] = 0 := by decide

theorem tblocks_one_ne_cB (a : Bytes 22) (k : Bytes 16) : (tblocks a [k]).1 ≠ cB := by
  intro h
  have h1 := congrArg (fun v : Blk => v[38]) h
  simp only [tblocks_one_get38, cB_get38] at h1
  exact absurd h1 (by decide)

end Ideal

#print axioms Ideal.cfAvg_itsr_le_fine
#print axioms Ideal.reuseSum_63_12_14_le_of
#print axioms Ideal.suf_final
#print axioms Ideal.suf_final_2_60_2_20
#print axioms Ideal.suf_final_2_80_2_40
#print axioms Ideal.suf_final_2_90_2_64
#print axioms Ideal.tblocks_one_ne_cB
#print axioms Ideal.euf_final
#print axioms Ideal.euf_final_2_60_2_20
#print axioms Ideal.euf_final_2_90_2_64
#print axioms Ideal.suf_final_optRandU
