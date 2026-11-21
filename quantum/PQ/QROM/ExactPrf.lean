import PQ.QROM.Distinguish
import PQ.QROM.TwoPhaseAdv

/-!
# The exact PRF game in the QROM: classical PRF oracle, quantum access to the random function

The PRF games as the SLH-DSA reduction uses them (VCVio `PRFScheme.prfAdvantage`,
`VCVio/CryptoFoundations/PRF.lean`): the adversary's PRF oracle is CLASSICAL.  Here the keyed
function is derived from a uniformly random function `F : K × Dm → Y`, to which the adversary
has QUANTUM access throughout, and the key `k : K` is uniform and hidden.

## The game

* World: `F : K × Dm → Y` uniform, `k : K` uniform (real), `R : Dm → Y` uniform (ideal).
* Adversary: `x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A` (`PQ/QROM/TwoPhaseAdv.lean`): a
  quantum query program with quantum access to `F` (the single port of `qromSpec (K × Dm) Y`),
  which sends up to `n` classical requests `d : Dm` and continues according to the classical
  responses in `Y`; the quantum state is kept across requests.  Any local instruments, any
  workspace, any initial state `ρ`.
* Real experiment `prfExactReal`: request `d` is answered by `F (k, d)`.
* Ideal experiment `prfExactIdeal`: request `d` is answered by `R d`, `R` independent of `F`.
* The event `E` is any predicate of the final leaf (final register label and classical output),
  in particular "the output bit is `true`".

`prfExactProg n x f` is the adversary run against the answer function `f`: one `QuantumComp`
program, `IAdv.flat` with the stateless challenger `prfExactCh f`.

## Results

For every adversary making at most `q` quantum queries to `F` on every path
(`IAdv.IsQueryBound n x fun _ ↦ q`), whatever the number `n` of classical requests:

* `prfExact_real_le_ideal_add`, `prfExact_ideal_le_real_add`:
  `Pr_real[E] ≤ Pr_ideal[E] + 4 q / √|K|` and conversely.
* `prfExact_abs_sub_le`: `|Pr_real[E] − Pr_ideal[E]| ≤ 4 q / √|K|` (real numbers).
* `prfExact_tight_of_program`: the tight shape `c q² / |K|`, conditional on ONE named hypothesis
  `PrfExactTightProgram I ρ q c`, the hidden-set distinguishing bound `c q² ε` for
  view-indexed programs (the statement proved in the circuit model as `tight_view`,
  `PQ/QROM/TightCore.lean`, there with `c = 8`).  `prfExact_o2hProgram` proves the same
  statement with `4 q √ε` in place of `c q² ε`: the hypothesis has the shape of a theorem of this
  development and differs from it only in the error term.
* `prfExact_tight_abs_of_programReal`: the same conclusion from the hypothesis in the
  real-valued shape of `tight_view` (`PrfExactTightProgramReal`: real weights, conditional
  hiddenness per view, `|∑ real − ∑ hybrid| ≤ c q² ε ∑ wt`), so that whichever shape the
  program-level tight theorem takes, one application closes the bound.

Proof (one-way-to-hiding level): worlds `(k, (F, R))`; view `(F, R)`.  By the row swap
`prfSwapRow` (an exact change of variables), the real experiment is: oracle `F` with row `k`
replaced by `R`, classical answers `R`.  The ideal experiment is: oracle `F`, classical answers
`R`.  The program `prfExactProg n x R` is a function of the view, the two oracles differ only on
the row of `k`, and each point lies in the row of `k` for a `1/|K|`-fraction of the keys.

## Correspondence with VCVio's `prfAdvantage`

`prfAdvantage prf B = 𝒟[prf.prfRealExperiment B].boolDist 𝒟[prfIdealExperiment B]
= |Pr[real ⇒ true] − Pr[ideal ⇒ true]|`.

* *Key generation.*  `prf.keygen` is `$ᵗ K` for both schemes below; here `k` is averaged
  uniformly.
* *Real oracle.*  `prfRealQueryImpl prf k` answers `d` by `prf.eval k d`; here by `F (k, d)`,
  i.e. `prf.eval k d := F (k, d)` with `F` uniformly random.
* *Ideal oracle.*  VCVio's ideal experiment answers by a LAZY random oracle with a cache
  (`romImpl`); here by an EAGERLY sampled uniform `R : Dm → Y`.  A consistent lazy random oracle
  and a uniform function give the same joint law of answers on every finite run (VCVio:
  "has the law of a uniform function `D → R` on every finite run"); the eager form is the one
  that makes sense next to quantum access to `F`.  This identification is the standard
  lazy/eager equivalence; it is NOT re-proved here.
* *Private coins.*  VCVio's adversary may also query `unifSpec`.  Here local randomness is a
  local instrument of the program (e.g. `SubInstrument.uniform`), which every `IAdv` may use.
* *Adversary class.*  Every classical `PRFAdversary` (an `OracleComp` that queries the function
  oracle) is the special case of an `IAdv` with no quantum query (`q = 0`): the bounds then give
  advantage `0`, as they must for a uniformly random `F` whose only access is the PRF oracle.
  The bounds here are for the strictly larger class with quantum access to `F`.
* *`skPrfC`* (`security/Reduction/PrfDomain.lean`): `PRFScheme SkSeed (PkSeed × SkAdrs vp) Y`,
  `eval k d = PRF d.1 k d.2`.  Instance: `K := SkSeed`, `Dm := PkSeed × SkAdrs vp`,
  `F (k, (pk, a)) := PRF pk k a`.  The public seed is FOLDED INTO `Dm`, exactly as `skPrfC`
  folds it into the PRF domain (the PRF adversary chooses it in each request); nothing about
  `PK.seed` being fixed or public is used, so this covers every way the reduction uses it.
  The restriction to secret-key addresses `SkAdrs` is the request type of the classical oracle;
  quantum access here is to `F` on the same domain `K × Dm`.  Quantum access to `PRF` on
  non-secret addresses concerns other, independent values of a random function and is not part
  of this game.
* *`msgPrf`* (`PRF_msg(SK.prf, opt_rand, M)`): `K := SkPrf`, `Dm := OptRand × Msg`,
  `F (k, (r, m)) := PRF_msg k r m`.
* The types must be finite (`Fintype`); for `msgPrf` this means a bounded message space.

**Honest caveats.**  (1) The O2H bound `4 q / √|K|` is not tight (Grover key search has advantage
of order `q² / |K|`).  (2) `q` counts the quantum queries to `F`; classical requests are free and
unbounded in the bound.  (3) The tight bound in THIS file is conditional on `PrfExactTightProgram(Real)`; that hypothesis is
discharged in `PQ/QROM/ExactPrfTight.lean` (`prfExactTightProgramReal`, `prfExact_tight_abs_le`:
`8 q² / |K|`, unconditional).
-/

open MeasureTheory ENNReal Finset Quantum

set_option linter.unusedSectionVars false

universe u v w

namespace PQ.QROM

section ExactPrf

variable {K Dm Y : Type} [Fintype K] [DecidableEq K] [Fintype Dm] [DecidableEq Dm] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- The classical PRF oracle as a (stateless) challenger: request `d` is answered by `f d`. -/
def prfExactCh (f : Dm → Y) : Dm → Unit → Y × Unit := fun d s ↦ (f d, s)

/-- The adversary run against the classical answer function `f`: one quantum query program. -/
def prfExactProg (n : ℕ) (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A) (f : Dm → Y) :
    QuantumComp L (qromSpec (K × Dm) Y) (fun u ↦ Out u × Unit) A :=
  IAdv.flat (prfExactCh f) (IAdv.stop (L := L) (spec := qromSpec (K × Dm) Y)) n () x

/-- The flattened program makes at most `q` quantum queries, whatever the answer function. -/
theorem prfExactProg_queryBounded {n q : ℕ} {x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A}
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (f : Dm → Y) : QueryBounded (prfExactProg n x f) q :=
  hx Unit (prfExactCh f) ()

/-- **Real PRF experiment.**  `F` and `k` uniform; quantum access to `F`; classical requests
`d` answered by `F (k, d)`. -/
noncomputable def prfExactReal (I : L.Interp) (ρ : SubState A) (n : ℕ)
    (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A) (E : (Σ u, Out u × Unit) → Prop) : ℝ≥0∞ :=
  ∑ k : K, ∑ F : K × Dm → Y,
    ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹) *
      qprob I F (prfExactProg n x fun d ↦ F (k, d)) ρ E

/-- **Ideal PRF experiment.**  `F` and `R` uniform and independent; quantum access to `F`;
classical requests `d` answered by `R d`. -/
noncomputable def prfExactIdeal (I : L.Interp) (ρ : SubState A) (n : ℕ)
    (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A) (E : (Σ u, Out u × Unit) → Prop) : ℝ≥0∞ :=
  ∑ F : K × Dm → Y, ∑ R : Dm → Y,
    ((Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Dm → Y) : ℝ≥0∞)⁻¹) *
      qprob I F (prfExactProg n x R) ρ E

/-- The row of the key `k` in the domain of `F`. -/
def prfExactMarked (k : K) : Finset (K × Dm) := univ.filter fun p ↦ p.1 = k

/-- The row of the hidden key is `1/|K|`-hidden from the view `(F, R)`. -/
theorem prfExact_hidden (κ : ℝ≥0∞) :
    Hidden (Ω := K × ((K × Dm → Y) × (Dm → Y))) (fun _ ↦ κ) (fun ω ↦ ω.2)
      (fun ω ↦ prfExactMarked (Dm := Dm) ω.1) (Fintype.card K : ℝ≥0∞)⁻¹ := by
  refine hidden_indep κ _ _ fun p ↦ ?_
  have : Nonempty K := ⟨p.1⟩
  have hm : ∀ k : K, (p ∈ prfExactMarked (Dm := Dm) k) ↔ k = p.1 := fun k ↦ by
    simp [prfExactMarked, eq_comm]
  simp only [hm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_comm, card_mul_inv_cancel]

theorem prfExact_differ (ω : K × ((K × Dm → Y) × (Dm → Y))) (p : K × Dm)
    (h : prfSwapRow ω.1 ω.2.1 ω.2.2 p ≠ ω.2.1 p) : p ∈ prfExactMarked (Dm := Dm) ω.1 := by
  by_contra hp
  have hk : ¬ p.1 = ω.1 := by simpa [prfExactMarked] using hp
  exact h (by simp [prfSwapRow, hk])

/-- The coupling.  Worlds `(k, (F, R))`, uniform.  The real experiment is the coupled experiment
"oracle `F` with row `k` replaced by `R`, classical answers `R`"; the ideal experiment is "oracle
`F`, classical answers `R`". -/
theorem prfExact_coupling [Nonempty K] [Nonempty Dm] [Nonempty Y] (I : L.Interp) (ρ : SubState A)
    (n : ℕ) (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A) (E : (Σ u, Out u × Unit) → Prop) :
    (∑ ω : K × ((K × Dm → Y) × (Dm → Y)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Dm → Y) : ℝ≥0∞)⁻¹)) *
          qprob I (prfSwapRow ω.1 ω.2.1 ω.2.2) (prfExactProg n x ω.2.2) ρ E =
      prfExactReal I ρ n x E) ∧
    (∑ ω : K × ((K × Dm → Y) × (Dm → Y)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Dm → Y) : ℝ≥0∞)⁻¹)) *
          qprob I ω.2.1 (prfExactProg n x ω.2.2) ρ E =
      prfExactIdeal I ρ n x E) ∧
    ∑ _ω : K × ((K × Dm → Y) × (Dm → Y)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Dm → Y) : ℝ≥0∞)⁻¹)) ≤ 1 := by
  have iK := card_mul_inv_cancel K
  have iF := card_mul_inv_cancel (K × Dm → Y)
  have iR := card_mul_inv_cancel (Dm → Y)
  set cK : ℝ≥0∞ := (Fintype.card K : ℝ≥0∞)
  set cF : ℝ≥0∞ := (Fintype.card (K × Dm → Y) : ℝ≥0∞)
  set cR : ℝ≥0∞ := (Fintype.card (Dm → Y) : ℝ≥0∞)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hrow : ∀ v : (K × Dm → Y) × (Dm → Y),
        (fun d ↦ prfSwapRow k v.1 v.2 (k, d)) = v.2 := fun v ↦ by
      funext d
      simp [prfSwapRow]
    have h := sum_prfSwapRow (D := Dm) k fun F ↦ (cK⁻¹ * (cF⁻¹ * cR⁻¹)) *
      qprob I F (prfExactProg n x fun d ↦ F (k, d)) ρ E
    simp only [hrow] at h
    refine h.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    calc cR * (cK⁻¹ * (cF⁻¹ * cR⁻¹) * qprob I F (prfExactProg n x fun d ↦ F (k, d)) ρ E)
        = (cR * cR⁻¹) * (cK⁻¹ * cF⁻¹ * qprob I F (prfExactProg n x fun d ↦ F (k, d)) ρ E) := by
          ring
      _ = _ := by rw [iR, one_mul]
  · rw [Fintype.sum_prod_type]
    dsimp only
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    calc cK * (cK⁻¹ * (cF⁻¹ * cR⁻¹) * qprob I F (prfExactProg n x R) ρ E)
        = (cK * cK⁻¹) * (cF⁻¹ * cR⁻¹ * qprob I F (prfExactProg n x R) ρ E) := by ring
      _ = _ := by rw [iK, one_mul]
  · refine le_of_eq ?_
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    calc cK * (cF * cR * (cK⁻¹ * (cF⁻¹ * cR⁻¹)))
        = (cK * cK⁻¹) * (cF * cF⁻¹) * (cR * cR⁻¹) := by ring
      _ = 1 := by rw [iK, iF, iR]; simp

/-- **Exact PRF game, real ≤ ideal.**  `Pr_real[E] ≤ Pr_ideal[E] + 4 q / √|K|`. -/
theorem prfExact_real_le_ideal_add [Nonempty K] [Nonempty Dm] (I : L.Interp) (ρ : SubState A)
    {n q : ℕ} (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    prfExactReal I ρ n x E ≤
      prfExactIdeal I ρ n x E + 4 * q * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  obtain ⟨e1, e2, hw⟩ := prfExact_coupling I ρ n x E
  have h := (prfExact_hidden (K := K) (Dm := Dm) (Y := Y) _).real_le_hyb_add hw
    (fun v ↦ HybridModel.ofProgram I (prfExactProg n x v.2) ρ q
      (prfExactProg_queryBounded hx v.2) E)
    (fun ω ↦ prfSwapRow ω.1 ω.2.1 ω.2.2) (fun v ↦ v.1) prfExact_differ (fun _ ↦ id)
  rw [← e1, ← e2]
  exact h

/-- **Exact PRF game, ideal ≤ real.**  `Pr_ideal[E] ≤ Pr_real[E] + 4 q / √|K|`. -/
theorem prfExact_ideal_le_real_add [Nonempty K] [Nonempty Dm] (I : L.Interp) (ρ : SubState A)
    {n q : ℕ} (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    prfExactIdeal I ρ n x E ≤
      prfExactReal I ρ n x E + 4 * q * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  obtain ⟨e1, e2, hw⟩ := prfExact_coupling I ρ n x E
  have h := (prfExact_hidden (K := K) (Dm := Dm) (Y := Y) _).hyb_le_real_add hw
    (fun v ↦ HybridModel.ofProgram I (prfExactProg n x v.2) ρ q
      (prfExactProg_queryBounded hx v.2) E)
    (fun ω ↦ prfSwapRow ω.1 ω.2.1 ω.2.2) (fun v ↦ v.1) prfExact_differ (fun _ ↦ id)
  rw [← e1, ← e2]
  exact h

/-- Without quantum queries to `F` (in particular: for every classical PRF adversary) the real
and ideal experiments have the same value: the PRF oracle of a uniformly random keyed function is
a uniformly random function. -/
theorem prfExact_real_eq_ideal_of_zero [Nonempty K] [Nonempty Dm] (I : L.Interp) (ρ : SubState A)
    {n : ℕ} (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ 0) (E : (Σ u, Out u × Unit) → Prop) :
    prfExactReal I ρ n x E = prfExactIdeal I ρ n x E :=
  le_antisymm (by simpa using prfExact_real_le_ideal_add I ρ x hx E)
    (by simpa using prfExact_ideal_le_real_add I ρ x hx E)

/-- Both experiments are probabilities. -/
theorem prfExact_le_one [Nonempty K] [Nonempty Dm] (I : L.Interp) (ρ : SubState A)
    {n q : ℕ} (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    prfExactReal I ρ n x E ≤ 1 ∧ prfExactIdeal I ρ n x E ≤ 1 := by
  obtain ⟨e1, e2, hw⟩ := prfExact_coupling I ρ n x E
  rw [← e1, ← e2]
  exact ⟨sum_mul_prob_le_one hw
      (fun ω : K × ((K × Dm → Y) × (Dm → Y)) ↦ HybridModel.ofProgram I (prfExactProg n x ω.2.2)
        ρ q (prfExactProg_queryBounded hx ω.2.2) E)
      (fun ω ↦ prfSwapRow ω.1 ω.2.1 ω.2.2) (fun _ ↦ id),
    sum_mul_prob_le_one hw
      (fun ω : K × ((K × Dm → Y) × (Dm → Y)) ↦ HybridModel.ofProgram I (prfExactProg n x ω.2.2)
        ρ q (prfExactProg_queryBounded hx ω.2.2) E)
      (fun ω ↦ ω.2.1) (fun _ ↦ id)⟩

/-- Two probabilities that are `δ`-close in both directions: absolute difference of the real
numbers. -/
theorem prfExact_abs_of_le {a b δ : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) (hδ : δ ≠ ⊤)
    (h1 : a ≤ b + δ) (h2 : b ≤ a + δ) : |a.toReal - b.toReal| ≤ δ.toReal := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top one_ne_top ha
  have hb' : b ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hb
  have e1 := ENNReal.toReal_mono (add_ne_top.2 ⟨hb', hδ⟩) h1
  have e2 := ENNReal.toReal_mono (add_ne_top.2 ⟨ha', hδ⟩) h2
  rw [ENNReal.toReal_add hb' hδ] at e1
  rw [ENNReal.toReal_add ha' hδ] at e2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The O2H error term as a real number: `4 q / √|K|`. -/
theorem prfExact_err_toReal [Nonempty K] (q : ℕ) :
    (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)).toReal =
      4 * q / Real.sqrt (Fintype.card K) := by
  have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
    Real.inv_rpow hK.le, Real.sqrt_eq_rpow, div_eq_mul_inv]
  norm_num

/-- **Exact PRF game, absolute-difference form** (the form of VCVio's `prfAdvantage`, with
`E` = "the output bit is `true`"): `|Pr_real[E] − Pr_ideal[E]| ≤ 4 q / √|K|`. -/
theorem prfExact_abs_sub_le [Nonempty K] [Nonempty Dm] (I : L.Interp) (ρ : SubState A)
    {n q : ℕ} (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    |(prfExactReal I ρ n x E).toReal - (prfExactIdeal I ρ n x E).toReal| ≤
      4 * q / Real.sqrt (Fintype.card K) := by
  obtain ⟨h1, h2⟩ := prfExact_le_one I ρ x hx E
  rw [← prfExact_err_toReal (K := K) q]
  refine prfExact_abs_of_le h1 h2 ?_ (prfExact_real_le_ideal_add I ρ x hx E)
    (prfExact_ideal_le_real_add I ρ x hx E)
  refine mul_ne_top (mul_ne_top (by simp) (by simp)) (rpow_ne_top_of_nonneg (by norm_num) ?_)
  simp [Fintype.card_ne_zero]

/-! ## The tight shape, conditional on the program-level hidden-set bound -/

/-- **The one hypothesis of the tight exact PRF bound**: the second-order hidden-set
distinguishing bound for view-indexed quantum query PROGRAMS on the oracle `X → Y`, with constant
`c`.  Worlds `ω` with weights `w ω` of total mass at most one; the program `x (view ω)` and the
hybrid function `Ghyb (view ω)` are determined by the view; the real function `Hreal ω` differs
from the hybrid one only on the marked set `S ω`, which is `ε`-hidden from the view.  Then the
real and hybrid probabilities of every view-determined event differ by at most `c q² ε`.

This is `Hidden.real_le_hyb_add` / `Hidden.hyb_le_real_add` at the level of programs
(`prfExact_o2hProgram`) with `c q² ε` in place of `4 q √ε`, and `tight_view`
(`PQ/QROM/TightCore.lean`, `c = 8`, pure-state circuits with a fixed sequence of unitaries) for
all programs. -/
def PrfExactTightProgram (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] {L : LocalSig.{u, v}} (I : L.Interp) (W : QReg → Type w) {A : QReg}
    (ρ : SubState A) (q : ℕ) (c : ℝ≥0∞) : Prop :=
  ∀ (Ω V : Type) [Fintype Ω] [Fintype V] [DecidableEq V] (wt : Ω → ℝ≥0∞) (view : Ω → V)
    (S : Ω → Finset X) (ε : ℝ≥0∞), Hidden wt view S ε → ∑ ω, wt ω ≤ 1 →
    ∀ x : V → QuantumComp L (qromSpec X Y) W A, (∀ v, QueryBounded (x v) q) →
    ∀ (Hreal : Ω → X → Y) (Ghyb : V → X → Y),
      (∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) →
    ∀ E : V → (Σ u, W u) → Prop,
      (∑ ω, wt ω * qprob I (Hreal ω) (x (view ω)) ρ (E (view ω)) ≤
        ∑ ω, wt ω * qprob I (Ghyb (view ω)) (x (view ω)) ρ (E (view ω)) + c * (q : ℝ≥0∞) ^ 2 * ε) ∧
      (∑ ω, wt ω * qprob I (Ghyb (view ω)) (x (view ω)) ρ (E (view ω)) ≤
        ∑ ω, wt ω * qprob I (Hreal ω) (x (view ω)) ρ (E (view ω)) + c * (q : ℝ≥0∞) ^ 2 * ε)

/-- The statement of `PrfExactTightProgram` with the one-way-to-hiding error `4 q √ε` in place
of `c q² ε` is a theorem: the hypothesis differs from a proved statement only in the error
term. -/
theorem prfExact_o2hProgram {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (I : L.Interp) {W : QReg → Type w} (ρ : SubState A) (q : ℕ)
    {Ω V : Type} [Fintype Ω] (wt : Ω → ℝ≥0∞) (view : Ω → V)
    (S : Ω → Finset X) (ε : ℝ≥0∞) (hH : Hidden wt view S ε) (hw : ∑ ω, wt ω ≤ 1)
    (x : V → QuantumComp L (qromSpec X Y) W A) (hx : ∀ v, QueryBounded (x v) q)
    (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (E : V → (Σ u, W u) → Prop) :
    (∑ ω, wt ω * qprob I (Hreal ω) (x (view ω)) ρ (E (view ω)) ≤
      ∑ ω, wt ω * qprob I (Ghyb (view ω)) (x (view ω)) ρ (E (view ω)) +
        4 * q * ε ^ (2⁻¹ : ℝ)) ∧
    (∑ ω, wt ω * qprob I (Ghyb (view ω)) (x (view ω)) ρ (E (view ω)) ≤
      ∑ ω, wt ω * qprob I (Hreal ω) (x (view ω)) ρ (E (view ω)) + 4 * q * ε ^ (2⁻¹ : ℝ)) :=
  ⟨hH.real_le_hyb_add hw (fun v ↦ HybridModel.ofProgram I (x v) ρ q (hx v) (E v)) Hreal Ghyb hS
      (fun _ ↦ id),
    hH.hyb_le_real_add hw (fun v ↦ HybridModel.ofProgram I (x v) ρ q (hx v) (E v)) Hreal Ghyb hS
      (fun _ ↦ id)⟩

/-- **Exact PRF game, tight shape, conditional.**  If the program-level second-order hidden-set
bound holds with constant `c` (`PrfExactTightProgram`), then for every adversary with at most
`q` quantum queries to `F`: `Pr_real[E] ≤ Pr_ideal[E] + c q² / |K|` and conversely. -/
theorem prfExact_tight_of_program [Nonempty K] [Nonempty Dm] (I : L.Interp) (ρ : SubState A)
    {n q : ℕ} {c : ℝ≥0∞}
    (hTight : PrfExactTightProgram (K × Dm) Y I (fun u ↦ Out u × Unit) ρ q c)
    (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    (prfExactReal I ρ n x E ≤
      prfExactIdeal I ρ n x E + c * (q : ℝ≥0∞) ^ 2 * (Fintype.card K : ℝ≥0∞)⁻¹) ∧
    (prfExactIdeal I ρ n x E ≤
      prfExactReal I ρ n x E + c * (q : ℝ≥0∞) ^ 2 * (Fintype.card K : ℝ≥0∞)⁻¹) := by
  classical
  obtain ⟨e1, e2, hw⟩ := prfExact_coupling I ρ n x E
  have h := hTight (K × ((K × Dm → Y) × (Dm → Y))) ((K × Dm → Y) × (Dm → Y)) _ (fun ω ↦ ω.2)
    (fun ω ↦ prfExactMarked (Dm := Dm) ω.1) _ (prfExact_hidden _) hw
    (fun v ↦ prfExactProg n x v.2) (fun v ↦ prfExactProg_queryBounded hx v.2)
    (fun ω ↦ prfSwapRow ω.1 ω.2.1 ω.2.2) (fun v ↦ v.1) prfExact_differ (fun _ ↦ E)
  rw [← e1, ← e2]
  exact h

/-- The conditional tight bound in absolute-difference form. -/
theorem prfExact_tight_abs_of_program [Nonempty K] [Nonempty Dm] (I : L.Interp) (ρ : SubState A)
    {n q : ℕ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hTight : PrfExactTightProgram (K × Dm) Y I (fun u ↦ Out u × Unit) ρ q c)
    (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    |(prfExactReal I ρ n x E).toReal - (prfExactIdeal I ρ n x E).toReal| ≤
      c.toReal * (q : ℝ) ^ 2 / Fintype.card K := by
  obtain ⟨h1, h2⟩ := prfExact_le_one I ρ x hx E
  obtain ⟨t1, t2⟩ := prfExact_tight_of_program I ρ hTight x hx E
  have hδ : c * (q : ℝ≥0∞) ^ 2 * (Fintype.card K : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    mul_ne_top (mul_ne_top hc (by simp)) (by simp [Fintype.card_ne_zero])
  have h := prfExact_abs_of_le h1 h2 hδ t1 t2
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, ← div_eq_mul_inv] at h

/-! ### The same, for a hypothesis in the real-valued shape of `tight_view` -/

/-- **The one hypothesis, real-valued shape.**  The statement of `tight_view`
(`PQ/QROM/TightCore.lean`) for view-indexed quantum query PROGRAMS: real weights `wt ω ≥ 0`,
the marked set `ε`-hidden given the view in the conditional form
`wt {ω | view ω = v, k ∈ S ω} ≤ ε · wt {ω | view ω = v}`, and the conclusion
`|∑ real − ∑ hybrid| ≤ c q² ε ∑ wt`.  Either this or `PrfExactTightProgram` gives the tight
exact PRF bound. -/
def PrfExactTightProgramReal (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] {L : LocalSig.{u, v}} (I : L.Interp) (W : QReg → Type w) {A : QReg}
    (ρ : SubState A) (q : ℕ) (c : ℝ) : Prop :=
  ∀ (Ω V : Type) [Fintype Ω] [Fintype V] [DecidableEq V] (wt : Ω → ℝ), (∀ ω, 0 ≤ wt ω) →
    ∀ (view : Ω → V) (S : Ω → Finset X) (ε : ℝ), 0 ≤ ε →
    (∀ v k, ∑ ω with view ω = v ∧ k ∈ S ω, wt ω ≤ ε * ∑ ω with view ω = v, wt ω) →
    ∀ x : V → QuantumComp L (qromSpec X Y) W A, (∀ v, QueryBounded (x v) q) →
    ∀ (Hreal : Ω → X → Y) (Ghyb : V → X → Y),
      (∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) →
    ∀ E : V → (Σ u, W u) → Prop,
      |∑ ω, wt ω * (qprob I (Hreal ω) (x (view ω)) ρ (E (view ω))).toReal -
          ∑ ω, wt ω * (qprob I (Ghyb (view ω)) (x (view ω)) ρ (E (view ω))).toReal| ≤
        c * (q : ℝ) ^ 2 * ε * ∑ ω, wt ω

/-- **Exact PRF game, tight shape, conditional (real-valued hypothesis).**
`|Pr_real[E] − Pr_ideal[E]| ≤ c q² / |K|`. -/
theorem prfExact_tight_abs_of_programReal [Nonempty K] [Nonempty Dm] (I : L.Interp)
    (ρ : SubState A) {n q : ℕ} {c : ℝ}
    (hTight : PrfExactTightProgramReal (K × Dm) Y I (fun u ↦ Out u × Unit) ρ q c)
    (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    |(prfExactReal I ρ n x E).toReal - (prfExactIdeal I ρ n x E).toReal| ≤
      c * (q : ℝ) ^ 2 / Fintype.card K := by
  classical
  obtain ⟨e1, e2, -⟩ := prfExact_coupling I ρ n x E
  have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < Fintype.card (K × Dm → Y) := by exact_mod_cast Fintype.card_pos
  have hR : (0 : ℝ) < Fintype.card (Dm → Y) := by exact_mod_cast Fintype.card_pos
  set κ : ℝ := (Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × Dm → Y) : ℝ)⁻¹ *
    (Fintype.card (Dm → Y) : ℝ)⁻¹) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκt : ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Dm → Y) : ℝ≥0∞)⁻¹)).toReal = κ := by
    simp [hκ, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hfin : ∀ (H : K × Dm → Y) (R : Dm → Y), qprob I H (prfExactProg n x R) ρ E ≠ ⊤ :=
    fun H R ↦ ne_top_of_le_ne_top one_ne_top
      ((HybridModel.ofProgram I (prfExactProg n x R) ρ q (prfExactProg_queryBounded hx R)
        E).prob_le_one H id)
  have hκfin : (Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Dm → Y) : ℝ≥0∞)⁻¹) ≠ ⊤ := by
    simp [ENNReal.mul_eq_top, Fintype.card_ne_zero]
  have r1 : (prfExactReal I ρ n x E).toReal = ∑ ω : K × ((K × Dm → Y) × (Dm → Y)),
      κ * (qprob I (prfSwapRow ω.1 ω.2.1 ω.2.2) (prfExactProg n x ω.2.2) ρ E).toReal := by
    rw [← e1, ENNReal.toReal_sum fun ω _ ↦ mul_ne_top hκfin (hfin _ _)]
    simp only [ENNReal.toReal_mul, hκt]
  have r2 : (prfExactIdeal I ρ n x E).toReal = ∑ ω : K × ((K × Dm → Y) × (Dm → Y)),
      κ * (qprob I ω.2.1 (prfExactProg n x ω.2.2) ρ E).toReal := by
    rw [← e2, ENNReal.toReal_sum fun ω _ ↦ mul_ne_top hκfin (hfin _ _)]
    simp only [ENNReal.toReal_mul, hκt]
  have hm : ∀ (p : K × Dm) (k : K), (p ∈ prfExactMarked (Dm := Dm) k) ↔ k = p.1 := fun p k ↦ by
    simp [prfExactMarked, eq_comm]
  have hH : ∀ (v : (K × Dm → Y) × (Dm → Y)) (p : K × Dm),
      ∑ ω : K × ((K × Dm → Y) × (Dm → Y)) with ω.2 = v ∧ p ∈ prfExactMarked (Dm := Dm) ω.1, κ ≤
        (Fintype.card K : ℝ)⁻¹ * ∑ ω : K × ((K × Dm → Y) × (Dm → Y)) with ω.2 = v, κ := by
    intro v p
    rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [hm, ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]
  have h := hTight (K × ((K × Dm → Y) × (Dm → Y))) ((K × Dm → Y) × (Dm → Y)) (fun _ ↦ κ)
    (fun _ ↦ hκ0) (fun ω ↦ ω.2) (fun ω ↦ prfExactMarked (Dm := Dm) ω.1) (Fintype.card K : ℝ)⁻¹
    (by positivity) hH (fun v ↦ prfExactProg n x v.2) (fun v ↦ prfExactProg_queryBounded hx v.2)
    (fun ω ↦ prfSwapRow ω.1 ω.2.1 ω.2.2) (fun v ↦ v.1) prfExact_differ (fun _ ↦ E)
  have hsum : ∑ _ω : K × ((K × Dm → Y) × (Dm → Y)), κ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul,
      hκ]
    field_simp
  rw [r1, r2]
  rw [hsum, mul_one] at h
  rwa [div_eq_mul_inv]

end ExactPrf

end PQ.QROM

#print axioms PQ.QROM.prfExact_coupling
#print axioms PQ.QROM.prfExact_real_le_ideal_add
#print axioms PQ.QROM.prfExact_ideal_le_real_add
#print axioms PQ.QROM.prfExact_real_eq_ideal_of_zero
#print axioms PQ.QROM.prfExact_le_one
#print axioms PQ.QROM.prfExact_abs_sub_le
#print axioms PQ.QROM.prfExact_o2hProgram
#print axioms PQ.QROM.prfExact_tight_of_program
#print axioms PQ.QROM.prfExact_tight_abs_of_program
#print axioms PQ.QROM.prfExact_tight_abs_of_programReal
