import PQ.QROM.MultiPhaseGame
import PQ.QROM.ItsrFors

/-!
# Interleaved target subset resilience of a random function, ADAPTIVE targets (QROM)

`H : K × Xm → D` is a uniformly random function (`K` randomizers, `Xm` target inputs, `D`
digests) and `Cov : Finset D → D → Prop` an abstract, decidable, MONOTONE cover relation (as in
`PQ/QROM/Itsr.lean`; for SLH-DSA the FORS relation `forsCov` of `PQ/QROM/ItsrFors.lean`).

## The game (`itsrAdaptiveExp`)

* The adversary is an interactive adversary
  `x : IAdv L (qromSpec (K × Xm) D) Xm K (fun _ ↦ K × Xm) s A` (`PQ/QROM/TwoPhaseAdv.lean`):
  quantum segments with quantum access to `H`, separated by at most `s` CLASSICAL target requests
  `x_i : Xm`, chosen adaptively (they may depend on measurement outcomes of earlier segments);
  the quantum register is kept across requests.  At most `q` quantum queries to `H` in total on
  every path (`IAdv.IsQueryBound s x fun _ ↦ q`), distributed over the phases in any adaptive
  way.  Its final output is a classical pair `(R*, x*) : K × Xm`.
* The target oracle is `rndCh Rs` (`PQ/QROM/MultiPhaseGame.lean`): the `i`-th request `x_i` is
  answered with the randomizer `R_i = Rs i`, `Rs : Fin s → K` uniform, and the challenger records
  the request.  Pre-sampling `Rs` is the same as sampling `R_i` freshly when the `i`-th request
  arrives (the challenger uses `Rs i` only then, and the adversary is not a function of `Rs`).
* Win (`itsrAWin`): with `t` the final transcript of requests and targets
  `T = {(R_j, t_j) : j < |t|}` (`itsrATargets`), the output `(R*, x*)` is not in `T` and
  `Cov (H '' T) (H (R*, x*))`.
* `itsrAdaptiveExp = mpExp …`: the uniform average over `Rs` and `H` of the Born probability
  (`qprob`) of the winning leaves of the run of the single-port program
  `IAdv.flat (rndCh Rs) …` against the oracle unitary of `H`.

## Results

* `itsr_adaptive_sqrt_le`:
  `√itsrAdaptiveExp ≤ √((2q+1)² · coverProb (Fin s) Cov + s²/|K|) + 2 q √(s/|K|)`.
* `itsr_adaptive_le`: the same, squared.
* `itsr_adaptive_fors_le`: with the FORS relation and the closed form `coverProb_fors`.

`coverProb (Fin s) Cov` is the probability that a fresh uniform digest is covered by `s`
independent uniform digests; `s²/|K|` bounds the probability that two randomizers collide; the
term `2 q √(s/|K|)` is the reprogramming loss of `mp_reprogram`.

## Proof

1. `mp_reprogram` (`PQ/QROM/MultiPhaseGame.lean`): up to `2 q √(s/|K|)` in square root, the
   segment after `i` requests sees a function (`mpFn Rs Φ i`) in which the rows of the
   randomizers not issued yet are independent of the final function.
2. `itsrA_eq_B` (lazy sampling of the target digests, for injective `Rs`): leaf by leaf, the
   values of the hybrid function at the target points of the leaf's transcript can be replaced
   by pre-sampled independent digests `d : Fin s → D` (an involution swapping these values with
   `d`, `owTgt`/`rdTgt`; the post-state of a leaf only depends on the ports of the prefixes of
   its transcript, `pflat_branch_congr`).  Afterwards the covered set
   `covered Cov (univ.image d)` is static.
3. `itsrB_le` (search): with the digests `d` fixed, replace every value of `Φ` lying in the
   covered set by a fresh uncovered value (`resU`); given the replaced function, every point is
   marked independently with probability `|covered| / |D|` (`hidden_itsr`); the square-root
   hybrid bound over transcript ports and `Hidden.sum_le` give `(2q+1)² |covered| / |D|`
   (`Hidden.search_le'`).  Monotonicity of `Cov` is used here: the digests of the actual targets
   are among `d`.
4. Non-injective `Rs` are charged `s²/|K|` (`avg_not_injective_le`).

## Correspondence with VCVio's `KeyedHash.ITSRAdvantage` and deviations

VCVio (`VCVio/CryptoFoundations/HardnessAssumptions/KeyedHash/ITSR.lean`): the adversary is an
`OracleComp (unifSpec + (X →ₒ K))`; a target query on `x` samples `k ← keygen`, appends `(k, x)`
to the transcript and returns `k`; `Wins targets candidate` iff `candidate ∉ targets` and every
semantic index of `hash candidate` occurs among the indices of the hashes of the targets.

* Target oracle, transcript, freshness (`candidate ∉ targets`, pair freshness): the same; here
  the transcript records the requests and the pairs are `(Rs j, t_j)`.  Duplicated targets are
  irrelevant in both (set semantics).
* `Wins` is the instance `Cov S u := ∀ i ∈ indices u, ∃ d ∈ S, i ∈ indices d` of the abstract
  relation (monotone).  The FORS corollary uses `forsCov` on digests already split into
  (instance, `k` leaf indices), not the byte-level `forsIndices ∘ splitDigest` of
  `security/Reduction/Basic.lean`.
* DEVIATION (model): the hash is a uniformly random function to which the adversary has QUANTUM
  access; VCVio's game is about a fixed keyed hash family, without hash oracle.  `keygen` is the
  uniform distribution on `K`.
* DEVIATION (cap): the number of target requests is at most `s` by the type of the adversary
  (`IAdv … s`); VCVio's game has no cap in the definition (caps are properties of adversaries).
* DEVIATION (randomness): no `unifSpec`; private coins are local instruments of the program.
* DEVIATION (output): the candidate is the classical leaf value of the program.
* `Cov` must be monotone (`hmono`); the bound uses `coverProb` for `s` digests even if the
  adversary makes fewer requests.

## The reprogramming term

The bound is `(√((2q+1)² p_cov + s²/|K|) + 2 q √(s/|K|))²`, so it contains the additive term
`4 q² s/|K|` (and cross terms).  This term is weak for a large number of targets: at
`|K| = 2^128` it is vacuous for `s = 2^64`, `q ≥ 2^32`, and about `2^-26` for `s = 2^20`,
`q = 2^40`.  It comes from hiding the rows of all not-yet-issued randomizers from every query
by the hybrid (one-way-to-hiding type) argument; no claim is made that it is tight, nor that it
is an artefact.
-/

open MeasureTheory ENNReal Quantum Matrix Finset
open scoped Kronecker ComplexOrder

universe u v w

namespace PQ.QROM

/-! ## Auxiliary: averages, selection masses, the abstract search bound -/

section Aux

/-- Averaging against an involution of the product of two finite types. -/
theorem avg_involutive {T T' : Type} [Fintype T] [Fintype T'] [Nonempty T']
    (sw : T × T' → T × T') (hsw : Function.Involutive sw) (f : T → ℝ≥0∞) :
    avg (fun a ↦ avg fun b ↦ f (sw (a, b)).1) = avg f := by
  have e := Equiv.sum_comp hsw.toPerm (fun v : T × T' ↦ f v.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at e
  simp only [Function.Involutive.coe_toPerm] at e
  have h0 : (Fintype.card T' : ℝ≥0∞) ≠ 0 := by simp
  unfold avg
  calc ∑ a, (Fintype.card T : ℝ≥0∞)⁻¹ * ∑ b, (Fintype.card T' : ℝ≥0∞)⁻¹ * f (sw (a, b)).1
      = (Fintype.card T : ℝ≥0∞)⁻¹ * ((Fintype.card T' : ℝ≥0∞)⁻¹ *
          ∑ a, ∑ b, f (sw (a, b)).1) := by
        simp only [Finset.mul_sum]
    _ = (Fintype.card T : ℝ≥0∞)⁻¹ * ((Fintype.card T' : ℝ≥0∞)⁻¹ * ∑ a, ∑ _b : T', f a) := by
        rw [e]
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← mul_assoc _ (Fintype.card T' : ℝ≥0∞),
          ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _), one_mul, Finset.mul_sum]

/-- The probability that a uniform `s`-tuple of randomizers is not injective is at most
`s² / |K|`. -/
theorem avg_not_injective_le {K : Type} [Fintype K] [DecidableEq K] (s : ℕ) :
    avg (fun Rs : Fin s → K ↦ if Function.Injective Rs then (0 : ℝ≥0∞) else 1) ≤
      (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞) := by
  classical
  have hle : ∀ Rs : Fin s → K, (if Function.Injective Rs then (0 : ℝ≥0∞) else 1) ≤
      ∑ i : Fin s, ∑ j : Fin s, if i ≠ j ∧ Rs i = Rs j then (1 : ℝ≥0∞) else 0 := by
    intro Rs
    split_ifs with hinj
    · exact zero_le
    · obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.1 hinj
      calc (1 : ℝ≥0∞) = (if i ≠ j ∧ Rs i = Rs j then (1 : ℝ≥0∞) else 0) := by simp [hne, heq]
        _ ≤ ∑ j' : Fin s, (if i ≠ j' ∧ Rs i = Rs j' then (1 : ℝ≥0∞) else 0) :=
            Finset.single_le_sum
              (f := fun j' ↦ if i ≠ j' ∧ Rs i = Rs j' then (1 : ℝ≥0∞) else 0)
              (fun _ _ ↦ zero_le) (Finset.mem_univ j)
        _ ≤ _ :=
            Finset.single_le_sum
              (f := fun i' ↦ ∑ j' : Fin s, if i' ≠ j' ∧ Rs i' = Rs j' then (1 : ℝ≥0∞) else 0)
              (fun _ _ ↦ zero_le) (Finset.mem_univ i)
  have hpair : ∀ i j : Fin s,
      (avg fun Rs : Fin s → K ↦ if i ≠ j ∧ Rs i = Rs j then (1 : ℝ≥0∞) else 0) ≤
        (Fintype.card K : ℝ≥0∞)⁻¹ := by
    intro i j
    by_cases hij : i = j
    · simp [hij, avg]
    · unfold avg
      simp only [ne_eq, hij, not_false_eq_true, true_and]
      rw [← Finset.mul_sum, sum_collide i j hij, mul_left_comm]
      exact (mul_le_mul' le_rfl (by
        rw [mul_comm]; exact natCast_mul_inv_le_one _)).trans (mul_one _).le
  refine (avg_mono hle).trans ?_
  rw [avg_finset_sum]
  simp only [avg_finset_sum]
  refine (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpair i j).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_eq_mul_inv, sq, mul_assoc]

/-- The mass on the pairs `(z, b)`: the masses `μ ⟨t, z⟩` of the ports `t` whose selector at `z`
is `b`. -/
noncomputable def selMass {P Z : Type} (bs : P → Z → Bool) (μ : (Σ _ : P, Z) → ℝ≥0∞)
    (y : Z × Bool) : ℝ≥0∞ :=
  ∑' t : P, if bs t y.1 = y.2 then μ ⟨t, y.1⟩ else 0

theorem sum_selMass {P Z : Type} [Fintype Z] [DecidableEq Z] (bs : P → Z → Bool)
    (μ : (Σ _ : P, Z) → ℝ≥0∞) (S : Finset (Z × Bool)) :
    ∑ k ∈ S, selMass bs μ k =
      ∑' c : Σ _ : P, Z, if (c.2, bs c.1 c.2) ∈ S then μ c else 0 := by
  unfold selMass
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  have hsig : (∑' c : Σ _ : P, Z, if (c.2, bs c.1 c.2) ∈ S then μ c else 0) =
      ∑' t : P, ∑ z : Z, if (z, bs t z) ∈ S then μ ⟨t, z⟩ else 0 :=
    (tsum_sigma (β := fun _ : P ↦ Z)
      fun t z ↦ if (z, bs t z) ∈ S then μ ⟨t, z⟩ else 0).trans
      (tsum_congr fun t ↦ tsum_fintype _)
  rw [hsig]
  refine tsum_congr fun t ↦ ?_
  calc ∑ k ∈ S, (if bs t k.1 = k.2 then μ ⟨t, k.1⟩ else 0)
      = ∑ k : Z × Bool, if k ∈ S then (if bs t k.1 = k.2 then μ ⟨t, k.1⟩ else 0) else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ z : Z, ∑ b : Bool,
          if (z, b) ∈ S then (if bs t z = b then μ ⟨t, z⟩ else 0) else 0 :=
        Fintype.sum_prod_type _
    _ = _ := by
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [Fintype.sum_bool]
        cases h : bs t z <;> simp

variable {Ω V X : Type} [Fintype Ω] [Fintype X] [DecidableEq X]
  {w : Ω → ℝ≥0∞} {view : Ω → V} {S : Ω → Finset X} {ε : ℝ≥0∞}

/-- **Search, abstract form.**  Worlds `ω` of total weight at most one; a quantity `a ω`
(the winning probability in the real world) such that `√(a ω)` is at most the square root of
the view-determined weight `pr (view ω)` of the marked set plus the square root of `4 q` times
the view-determined mass `mm (view ω)` of the marked set.  If the marked set is `ε`-hidden from
the view, the average of `a` is at most `(2q+1)² ε`. -/
theorem Hidden.search_le' (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1) (q : ℕ)
    (a : Ω → ℝ≥0∞) (pr mm : V → X → ℝ≥0∞) (hpr : ∀ v, ∑ k, pr v k ≤ 1)
    (hmm : ∀ v, ∑ k, mm v k ≤ q)
    (h : ∀ ω, a ω ^ (2⁻¹ : ℝ) ≤ (∑ k ∈ S ω, pr (view ω) k) ^ (2⁻¹ : ℝ) +
      (4 * q * ∑ k ∈ S ω, mm (view ω) k) ^ (2⁻¹ : ℝ)) :
    ∑ ω, w ω * a ω ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 * ε := by
  have h1 := sqrt_sum_le w a (fun ω ↦ ∑ k ∈ S ω, pr (view ω) k)
    (fun ω ↦ 4 * q * ∑ k ∈ S ω, mm (view ω) k) h
  have hb : ∑ ω, w ω * ∑ k ∈ S ω, pr (view ω) k ≤ ε :=
    (hH.sum_le hw pr 1 hpr).trans (mul_one _).le
  have hm : (∑ ω, w ω * (4 * q * ∑ k ∈ S ω, mm (view ω) k)) ^ (2⁻¹ : ℝ) ≤
      2 * q * ε ^ (2⁻¹ : ℝ) := by
    rw [← sqrt_four_mul]
    refine sqrt_le_sqrt ?_
    have h' := hH.sum_le hw mm q hmm
    calc ∑ ω, w ω * (4 * q * ∑ k ∈ S ω, mm (view ω) k)
        = 4 * q * ∑ ω, w ω * ∑ k ∈ S ω, mm (view ω) k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ ↦ mul_left_comm _ _ _
      _ ≤ 4 * q * (ε * q) := by gcongr
  have h2 : (∑ ω, w ω * a ω) ^ (2⁻¹ : ℝ) ≤ (2 * (q : ℝ≥0∞) + 1) * ε ^ (2⁻¹ : ℝ) :=
    calc _ ≤ _ := h1
      _ ≤ ε ^ (2⁻¹ : ℝ) + 2 * q * ε ^ (2⁻¹ : ℝ) := add_le_add (sqrt_le_sqrt hb) hm
      _ = (2 * (q : ℝ≥0∞) + 1) * ε ^ (2⁻¹ : ℝ) := by ring
  calc ∑ ω, w ω * a ω = ((∑ ω, w ω * a ω) ^ (2⁻¹ : ℝ)) ^ 2 := (sq_sqrt _).symm
    _ ≤ ((2 * (q : ℝ≥0∞) + 1) * ε ^ (2⁻¹ : ℝ)) ^ 2 := by gcongr
    _ = (2 * (q : ℝ≥0∞) + 1) ^ 2 * ε := by rw [mul_pow, sq_sqrt]

end Aux

/-! ## Targets, the winning condition, lazy sampling of the target digests -/

section Defs

variable {K Xm D : Type} {s : ℕ}

/-- `z` is one of the recorded targets `(Rs j, t_j)`, `j < |t|`, `j < s`. -/
def isTgt (Rs : Fin s → K) (t : List Xm) (z : K × Xm) : Prop :=
  ∃ j : Fin s, Rs j = z.1 ∧ t[j.1]? = some z.2

instance [DecidableEq K] [DecidableEq Xm] (Rs : Fin s → K) (t : List Xm) (z : K × Xm) :
    Decidable (isTgt Rs t z) := by
  unfold isTgt; infer_instance

/-- The targets recorded by the challenger after the requests `t`. -/
def itsrATargets [Fintype K] [Fintype Xm] [DecidableEq K] [DecidableEq Xm] (Rs : Fin s → K)
    (t : List Xm) : Finset (K × Xm) :=
  univ.filter (isTgt Rs t)

/-- **The winning condition of adaptive ITSR** on a leaf carrying the output `(R*, x*)` and the
transcript `t` of target requests: `(R*, x*)` is not a recorded target and its digest is covered
by the digests of the recorded targets. -/
def itsrAWin [Fintype K] [Fintype Xm] [DecidableEq K] [DecidableEq Xm] [DecidableEq D]
    (Cov : Finset D → D → Prop) (Rs : Fin s → K) (H : K × Xm → D)
    (p : Σ _ : QReg, (K × Xm) × List Xm) : Prop :=
  p.2.1 ∉ itsrATargets Rs p.2.2 ∧ Cov ((itsrATargets Rs p.2.2).image H) (H p.2.1)

open Classical in
/-- `Φ` with its values `Φ (z, true)` at the targets `z = (Rs j, t_j)` overwritten by the
digests `d j`. -/
noncomputable def owTgt (Rs : Fin s → K) (t : List Xm) (d : Fin s → D)
    (Φ : (K × Xm) × Bool → D) : (K × Xm) × Bool → D :=
  fun y ↦ if h : y.2 = true ∧ isTgt Rs t y.1 then d (Classical.choose h.2) else Φ y

/-- The digests `d` with `d j` overwritten by the value `Φ ((Rs j, t_j), true)` for `j < |t|`. -/
def rdTgt (Rs : Fin s → K) (t : List Xm) (d : Fin s → D) (Φ : (K × Xm) × Bool → D) :
    Fin s → D :=
  fun j ↦ (t[j.1]?).elim (d j) fun x ↦ Φ ((Rs j, x), true)

theorem owTgt_of_tgt (Rs : Fin s → K) (t : List Xm) (d : Fin s → D)
    (Φ : (K × Xm) × Bool → D) {z : K × Xm} (h : isTgt Rs t z) :
    owTgt Rs t d Φ (z, true) = d (Classical.choose h) :=
  dite_eq_left (⟨rfl, h⟩ : ((z, true) : (K × Xm) × Bool).2 = true ∧ isTgt Rs t (z, true).1)

theorem owTgt_of_not (Rs : Fin s → K) (t : List Xm) (d : Fin s → D)
    (Φ : (K × Xm) × Bool → D) {y : (K × Xm) × Bool} (h : ¬ (y.2 = true ∧ isTgt Rs t y.1)) :
    owTgt Rs t d Φ y = Φ y :=
  dite_eq_right h

/-- Swapping the values at the targets with the pre-sampled digests is an involution. -/
theorem swap_involutive (Rs : Fin s → K) (hinj : Function.Injective Rs) (t : List Xm) :
    Function.Involutive (fun v : ((K × Xm) × Bool → D) × (Fin s → D) ↦
      (owTgt Rs t v.2 v.1, rdTgt Rs t v.2 v.1)) := by
  rintro ⟨Φ, d⟩
  refine Prod.ext (funext fun y ↦ ?_) (funext fun j ↦ ?_)
  · by_cases h : y.2 = true ∧ isTgt Rs t y.1
    · obtain ⟨z, b⟩ := y
      obtain ⟨hb, ht⟩ := h
      simp only at hb ht
      subst hb
      have hc := Classical.choose_spec ht
      show owTgt Rs t (rdTgt Rs t d Φ) (owTgt Rs t d Φ) (z, true) = Φ (z, true)
      rw [owTgt_of_tgt _ _ _ _ ht]
      unfold rdTgt
      rw [hc.2, Option.elim_some, hc.1]
    · show owTgt Rs t (rdTgt Rs t d Φ) (owTgt Rs t d Φ) y = Φ y
      rw [owTgt_of_not _ _ _ _ h, owTgt_of_not _ _ _ _ h]
  · show rdTgt Rs t (rdTgt Rs t d Φ) (owTgt Rs t d Φ) j = d j
    unfold rdTgt
    cases hx : t[j.1]? with
    | none => simp
    | some x =>
      have ht : isTgt Rs t (Rs j, x) := ⟨j, rfl, hx⟩
      simp only [Option.elim_some]
      rw [owTgt_of_tgt _ _ _ _ ht]
      exact congrArg d (hinj (Classical.choose_spec ht).1)

variable [DecidableEq K]

/-- The function of the lazily-sampled hybrid world at the transcript port `t`: the function
`mpFn Rs Φ |t|` of the reprogramming hybrid with the values at the targets of `t` replaced by
the pre-sampled digests. -/
noncomputable def itsrBFn (Rs : Fin s → K) (d : Fin s → D) (Φ : (K × Xm) × Bool → D)
    (t : List Xm) : K × Xm → D :=
  mpFn Rs (owTgt Rs t d Φ) t.length

/-- For injective randomizers, overwriting at the targets of a transcript `t` agrees, on the
port of a prefix `t'` of `t`, with overwriting at the targets of `t'`. -/
theorem mpFn_owTgt_prefix {Rs : Fin s → K} (hinj : Function.Injective Rs) (d : Fin s → D)
    (Φ : (K × Xm) × Bool → D) {t' t : List Xm} (h : t' <+: t) :
    mpFn Rs (owTgt Rs t d Φ) t'.length = itsrBFn Rs d Φ t' := by
  obtain ⟨r, rfl⟩ := h
  funext z
  unfold itsrBFn mpFn
  by_cases hi : issued Rs t'.length z.1
  · simp only [hi, decide_true]
    obtain ⟨i, hil, hiR⟩ := hi
    have key : isTgt Rs (t' ++ r) z ↔ isTgt Rs t' z := by
      constructor
      · rintro ⟨j, hjR, hjt⟩
        have hji : j = i := hinj (hjR.trans hiR.symm)
        subst hji
        exact ⟨j, hjR, by rw [← hjt, List.getElem?_append_left hil]⟩
      · rintro ⟨j, hjR, hjt⟩
        have hlt : j.1 < t'.length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hjt
          cases hjt
        exact ⟨j, hjR, by rw [← hjt, List.getElem?_append_left hlt]⟩
    by_cases h1 : isTgt Rs (t' ++ r) z
    · have h2 := key.1 h1
      rw [owTgt_of_tgt _ _ _ _ h1, owTgt_of_tgt _ _ _ _ h2]
      exact congrArg d (hinj ((Classical.choose_spec h1).1.trans (Classical.choose_spec h2).1.symm))
    · have h2 : ¬ isTgt Rs t' z := fun h ↦ h1 (key.2 h)
      rw [owTgt_of_not _ _ _ _ (fun h ↦ h1 h.2), owTgt_of_not _ _ _ _ (fun h ↦ h2 h.2)]
  · simp only [hi, decide_false]
    rw [owTgt_of_not _ _ _ _ (fun h ↦ by simp at h), owTgt_of_not _ _ _ _ (fun h ↦ by simp at h)]

/-- Where the port functions built from `Φ` and `Φ'` differ, `Φ` and `Φ'` differ at the selected
point. -/
theorem itsrBFn_ne {Rs : Fin s → K} {d : Fin s → D} {Φ Φ' : (K × Xm) × Bool → D}
    {t : List Xm} {z : K × Xm} (h : itsrBFn Rs d Φ t z ≠ itsrBFn Rs d Φ' t z) :
    Φ (z, decide (issued Rs t.length z.1)) ≠ Φ' (z, decide (issued Rs t.length z.1)) := by
  intro heq
  refine h ?_
  unfold itsrBFn mpFn
  by_cases hc : ((z, decide (issued Rs t.length z.1)) : (K × Xm) × Bool).2 = true ∧
      isTgt Rs t ((z, decide (issued Rs t.length z.1)) : (K × Xm) × Bool).1
  · unfold owTgt
    rw [dite_eq_left hc, dite_eq_left hc]
  · rw [owTgt_of_not _ _ _ _ hc, owTgt_of_not _ _ _ _ hc]
    exact heq

variable [Fintype K] [Fintype Xm] [DecidableEq Xm] [Fintype D] [DecidableEq D]

/-- A winning leaf of the lazily-sampled world: the selected value of `Φ` at the output lies in
the set covered by the pre-sampled digests. -/
theorem itsrAWin_owTgt (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (Rs : Fin s → K) (d : Fin s → D) (Φ : (K × Xm) × Bool → D)
    (p : Σ _ : QReg, (K × Xm) × List Xm)
    (h : itsrAWin Cov Rs (mpFn Rs (owTgt Rs p.2.2 d Φ) s) p) :
    Φ (p.2.1, decide (issued Rs s p.2.1.1)) ∈ covered Cov (univ.image d) := by
  obtain ⟨hnt, hcov⟩ := h
  have hnt' : ¬ isTgt Rs p.2.2 p.2.1 := fun ht ↦
    hnt (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)
  have hval : mpFn Rs (owTgt Rs p.2.2 d Φ) s p.2.1 =
      Φ (p.2.1, decide (issued Rs s p.2.1.1)) :=
    owTgt_of_not _ _ _ _ fun hh ↦ hnt' hh.2
  rw [hval] at hcov
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hmono _ _ _ (fun v hv ↦ ?_) hcov⟩
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
  have ht : isTgt Rs p.2.2 z := (Finset.mem_filter.1 hz).2
  have hiss : issued Rs s z.1 := by
    obtain ⟨j, hj, _⟩ := ht
    exact ⟨j, j.2, hj⟩
  have : mpFn Rs (owTgt Rs p.2.2 d Φ) s z = d (Classical.choose ht) := by
    unfold mpFn
    simp only [hiss, decide_true]
    exact owTgt_of_tgt _ _ _ _ ht
  rw [this]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

end Defs

/-! ## The game and the bound -/

section Game

variable {K Xm D : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm] [DecidableEq Xm]
  [Fintype D] [DecidableEq D] [AddCommGroup D]
  {L : LocalSig.{u, v}} {A : QReg}

variable (I : L.Interp) (ρ : SubState A) (s : ℕ)
  (x : IAdv L (qromSpec (K × Xm) D) Xm K (fun _ ↦ K × Xm) s A)
  (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]

/-- **The adaptive ITSR experiment for a random function in the QROM.**  `Rs : Fin s → K` and
`H : K × Xm → D` uniform; the interactive adversary `x` has quantum access to `H` and makes at
most `s` classical target requests; the `i`-th request `x_i` is answered with `Rs i`; the
adversary outputs `(R*, x*)` and wins iff `(R*, x*)` is not a recorded target `(Rs j, x_j)` and
`Cov {H (Rs j, x_j)} (H (R*, x*))`. -/
noncomputable def itsrAdaptiveExp : ℝ≥0∞ :=
  mpExp I ρ s x (itsrAWin Cov)

variable {I ρ s x Cov} {q : ℕ}

omit [∀ S, DecidablePred (Cov S)] in
/-- **Lazy sampling of the target digests** (injective randomizers): the hybrid world of
`mp_reprogram` is the world in which the values at the target points are pre-sampled digests
`d`. -/
theorem itsrA_eq_B [Nonempty D] {Rs : Fin s → K} (hinj : Function.Injective Rs) :
    (avg fun Φ : (K × Xm) × Bool → D ↦
      leafProb (nRuntime fun t : List Xm ↦ mpFn Rs Φ t.length) I (mpComp s x Rs) (joint ρ)
        (itsrAWin Cov Rs (mpFn Rs Φ s))) =
      avg fun Φ : (K × Xm) × Bool → D ↦ avg fun d : Fin s → D ↦
        leafProb (nRuntime (itsrBFn Rs d Φ)) I (mpComp s x Rs) (joint ρ)
          (fun p ↦ itsrAWin Cov Rs (mpFn Rs (owTgt Rs p.2.2 d Φ) s) p) := by
  unfold leafProb
  simp only [avg_tsum]
  refine tsum_congr fun p ↦ ?_
  obtain ⟨u, o, t⟩ := p
  refine (avg_involutive _ (swap_involutive Rs hinj t)
    (fun Φ : (K × Xm) × Bool → D ↦
      ENNReal.ofReal ((((nRuntime fun t : List Xm ↦ mpFn Rs Φ t.length).run I
        (mpComp s x Rs)).branch ⟨u, (o, t)⟩) (joint ρ)).trace.re *
        ind (itsrAWin Cov Rs (mpFn Rs Φ s) ⟨u, (o, t)⟩))).symm.trans ?_
  refine avg_congr fun Φ ↦ avg_congr fun d ↦ ?_
  have hbr : ((nRuntime fun t' : List Xm ↦ mpFn Rs (owTgt Rs t d Φ) t'.length).run I
      (mpComp s x Rs)).branch ⟨u, (o, t)⟩ =
      ((nRuntime (itsrBFn Rs d Φ)).run I (mpComp s x Rs)).branch ⟨u, (o, t)⟩ :=
    pflat_branch_congr I (D := QReg.of Unit) (σ₁ := SubState.basis ())
      (σ₂ := SubState.basis ())
      (s₁ := fun t' : List Xm ↦ (oracleQuery (mpFn Rs (owTgt Rs t d Φ) t'.length)).frame Unit)
      (s₂ := fun t' : List Xm ↦ (oracleQuery (itsrBFn Rs d Φ t')).frame Unit)
      (rndCh Rs) (fun p t ↦ p <+: t) (fun _ ↦ List.prefix_refl _)
      (fun req t t' ↦ rndCh_step _ req t t') t
      (fun t' ht' ↦ by rw [mpFn_owTgt_prefix hinj d Φ ht']) s [] x u o
  show ENNReal.ofReal ((((nRuntime fun t' : List Xm ↦ mpFn Rs (owTgt Rs t d Φ) t'.length).run I
      (mpComp s x Rs)).branch ⟨u, (o, t)⟩) (joint ρ)).trace.re *
      ind (itsrAWin Cov Rs (mpFn Rs (owTgt Rs t d Φ) s) ⟨u, (o, t)⟩) = _
  rw [hbr]

/-- **Search in the lazily-sampled world**, for fixed randomizers and fixed pre-sampled
digests: at most `(2q+1)²` times the fraction of digests covered by the pre-sampled ones. -/
theorem itsrB_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) (Rs : Fin s → K) (d : Fin s → D) :
    (avg fun Φ : (K × Xm) × Bool → D ↦
      leafProb (nRuntime (itsrBFn Rs d Φ)) I (mpComp s x Rs) (joint ρ)
        (fun p ↦ itsrAWin Cov Rs (mpFn Rs (owTgt Rs p.2.2 d Φ) s) p)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        (((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
  classical
  set C : Finset D := covered Cov (univ.image d) with hC
  set F : ((K × Xm) × Bool → D) → ℝ≥0∞ := fun Φ ↦
    leafProb (nRuntime (itsrBFn Rs d Φ)) I (mpComp s x Rs) (joint ρ)
      (fun p ↦ itsrAWin Cov Rs (mpFn Rs (owTgt Rs p.2.2 d Φ) s) p) with hF
  have hF1 : ∀ Φ, F Φ ≤ 1 := fun Φ ↦
    (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)
  by_cases hU : Cᶜ.Nonempty
  · set U : {U : Finset D // U.Nonempty} := ⟨Cᶜ, hU⟩ with hUdef
    set cXD : ℝ≥0∞ := (Fintype.card ((K × Xm) × Bool → D) : ℝ≥0∞) with hcXD
    set cXR : ℝ≥0∞ := (Fintype.card ((K × Xm) × Bool → Res D) : ℝ≥0∞) with hcXR
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel Fintype.card_ne_zero
    have iXR : cXR * cXR⁻¹ = 1 := natCast_mul_inv_cancel Fintype.card_ne_zero
    set κ : ℝ≥0∞ := cXD⁻¹ * cXR⁻¹ with hκ
    have hw : ∑ _τ : (K × Xm) × Bool → D × Res D, κ ≤ 1 := by
      have := sum_fst_comp (X := (K × Xm) × Bool) (A := D) (B := Res D) (fun _ ↦ κ)
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc cXR * (cXD * κ) = (cXD * cXD⁻¹) * (cXR * cXR⁻¹) := by rw [hκ]; ring
        _ ≤ 1 := by rw [iXD, iXR, mul_one]
    -- the marked set is hidden from the resampled function
    have hH : Hidden (Ω := (K × Xm) × Bool → D × Res D) (fun _ ↦ κ)
        (fun τ k ↦ resU U (τ k)) (fun τ ↦ univ.filter fun k ↦ (τ k).1 ∉ U.1) (pMark U) := by
      intro k φ
      have h := hidden_itsr (X := (K × Xm) × Bool) (∅ : Finset ((K × Xm) × Bool))
        (fun _ ↦ Classical.arbitrary D) U κ k φ
      simpa using h
    let outB : (Σ _ : QReg, (K × Xm) × List Xm) → (K × Xm) × Bool := fun p ↦
      (p.2.1, decide (issued Rs s p.2.1.1))
    let bs : List Xm → K × Xm → Bool := fun t z ↦ decide (issued Rs t.length z.1)
    let pr : ((K × Xm) × Bool → D) → (K × Xm) × Bool → ℝ≥0∞ := fun v y ↦
      leafProb (nRuntime (itsrBFn Rs d v)) I (mpComp s x Rs) (joint ρ) (fun p ↦ outB p = y)
    let mm : ((K × Xm) × Bool → D) → (K × Xm) × Bool → ℝ≥0∞ := fun v ↦
      selMass bs (massN I (itsrBFn Rs d v) (mpComp s x Rs) (joint ρ))
    have hpr : ∀ v, ∑ k, pr v k ≤ 1 := fun v ↦
      (sum_leafProb_eq_le (R := nRuntime (itsrBFn Rs d v)) (I := I) (mpComp s x Rs)
        (joint_posSemidef ρ) outB).trans (ofReal_trace_joint_le_one ρ)
    have hmm : ∀ v, ∑ k, mm v k ≤ q := fun v ↦ by
      have h := sum_selMass bs (massN I (itsrBFn Rs d v) (mpComp s x Rs) (joint ρ)) univ
      simp only [Finset.mem_univ, ite_true] at h
      rw [h]
      exact (tsum_massN_le I _ (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs)).trans
        ((mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans (mul_one _).le)
    have hs := hH.search_le' hw q (fun τ ↦ F fun k ↦ (τ k).1) pr mm hpr hmm (by
      intro τ
      set Φ : (K × Xm) × Bool → D := fun k ↦ (τ k).1 with hΦ
      set Φh : (K × Xm) × Bool → D := fun k ↦ resU U (τ k) with hΦh
      set Sτ : Finset ((K × Xm) × Bool) := univ.filter fun k ↦ (τ k).1 ∉ U.1 with hSτ
      have h1 : F Φ ≤ leafProb (nRuntime (itsrBFn Rs d Φ)) I (mpComp s x Rs) (joint ρ)
          (fun p ↦ outB p ∈ Sτ) :=
        leafProb_mono _ _ fun p hp ↦ by
          have hc := itsrAWin_owTgt Cov hmono Rs d Φ p hp
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hin ↦ ?_⟩
          exact (Finset.mem_compl.1 hin) hc
      have h2 := (nRuntime_sqrt_le I (itsrBFn Rs d Φ) (itsrBFn Rs d Φh)
        (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs) (fun p ↦ outB p ∈ Sτ)).1
      have h3 : leafProb (nRuntime (itsrBFn Rs d Φh)) I (mpComp s x Rs) (joint ρ)
          (fun p ↦ outB p ∈ Sτ) ≤ ∑ k ∈ Sτ, pr Φh k :=
        leafProb_mem_le_sum _ _ outB Sτ
      have h4 : diffMass I (itsrBFn Rs d Φ) (itsrBFn Rs d Φh) (mpComp s x Rs) (joint ρ) ≤
          ∑ k ∈ Sτ, mm Φh k := by
        rw [sum_selMass]
        unfold diffMass
        refine tsum_le_tsum fun c ↦ ?_
        by_cases hne : itsrBFn Rs d Φ c.1 c.2 ≠ itsrBFn Rs d Φh c.1 c.2
        · have hin : (c.2, bs c.1 c.2) ∈ Sτ := by
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hin ↦ itsrBFn_ne hne ?_⟩
            simp only [hΦ, hΦh, resU]
            rw [ite_eq_left hin]
          rw [ite_eq_left hne, ite_eq_left hin]
        · rw [ite_eq_right hne]
          exact zero_le
      exact (sqrt_le_sqrt h1).trans (h2.trans (add_le_add (sqrt_le_sqrt h3)
        (sqrt_le_sqrt (mul_le_mul' le_rfl h4)))))
    have hp : pMark U = (C.card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ := by
      simp [pMark, hUdef]
    rw [hp] at hs
    refine le_trans (le_of_eq ?_) hs
    have e' := sum_fst_comp (X := (K × Xm) × Bool) (A := D) (B := Res D) (fun Φ ↦ κ * F Φ)
    refine Eq.trans ?_ e'.symm
    unfold avg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Φ _ ↦ ?_
    calc cXD⁻¹ * F Φ = (cXR * cXR⁻¹) * (cXD⁻¹ * F Φ) := by rw [iXR, one_mul]
      _ = _ := by rw [hκ]; ring
  · have hCu : C = univ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hU
      exact (Finset.compl_eq_empty_iff _).1 hU
    have h1 : (1 : ℝ≥0∞) ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((C.card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
      rw [hCu, Finset.card_univ, natCast_mul_inv_cancel Fintype.card_ne_zero, mul_one]
      exact one_le_two_mul_add_one_sq q
    exact (avg_le hF1).trans h1

/-- The hybrid experiment of `mp_reprogram` for the ITSR winning condition. -/
theorem itsr_hyb_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    mpHybExp I ρ s x (itsrAWin Cov) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
        (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞) := by
  classical
  have hB : ∀ Rs : Fin s → K,
      (avg fun Φ : (K × Xm) × Bool → D ↦ avg fun d : Fin s → D ↦
        leafProb (nRuntime (itsrBFn Rs d Φ)) I (mpComp s x Rs) (joint ρ)
          (fun p ↦ itsrAWin Cov Rs (mpFn Rs (owTgt Rs p.2.2 d Φ) s) p)) ≤
        (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov := by
    intro Rs
    rw [avg_comm]
    refine (avg_mono fun d ↦ itsrB_le hmono hx Rs d).trans ?_
    rw [avg_mul_left]
    rfl
  have hRs : ∀ Rs : Fin s → K,
      (avg fun Φ : (K × Xm) × Bool → D ↦
        leafProb (nRuntime fun t : List Xm ↦ mpFn Rs Φ t.length) I (mpComp s x Rs) (joint ρ)
          (itsrAWin Cov Rs (mpFn Rs Φ s))) ≤
        (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
          (if Function.Injective Rs then (0 : ℝ≥0∞) else 1) := by
    intro Rs
    by_cases hinj : Function.Injective Rs
    · rw [itsrA_eq_B hinj, ite_eq_left hinj, add_zero]
      exact hB Rs
    · rw [ite_eq_right hinj]
      refine le_trans ?_ le_add_self
      exact avg_le fun Φ ↦
        (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)
  unfold mpHybExp
  refine (avg_mono hRs).trans ?_
  rw [avg_add, avg_const]
  exact add_le_add le_rfl (avg_not_injective_le s)

/-- **Adaptive ITSR for a random function in the QROM, square-root form.**
`√Pr[win] ≤ √((2q+1)² · coverProb + s²/|K|) + 2 q √(s/|K|)`. -/
theorem itsr_adaptive_sqrt_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ s x Cov ^ (2⁻¹ : ℝ) ≤
      ((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
          (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  (mp_reprogram hx).trans (add_le_add (sqrt_le_sqrt (itsr_hyb_le hmono hx)) le_rfl)

/-- **Adaptive ITSR for a random function in the QROM.**  For every interactive adversary
making at most `q` quantum queries to `H` in total and at most `s` adaptive classical target
requests, and every monotone cover relation:
`Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov + s²/|K|) + 2 q √(s/|K|))²`. -/
theorem itsr_adaptive_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ s x Cov ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
          (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 :=
  calc itsrAdaptiveExp I ρ s x Cov = (itsrAdaptiveExp I ρ s x Cov ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' (itsr_adaptive_sqrt_le hmono hx) 2

omit [∀ S, DecidablePred (Cov S)] in
/-- The experiment is a probability. -/
theorem itsrAdaptiveExp_le_one : itsrAdaptiveExp I ρ s x Cov ≤ 1 := by
  unfold itsrAdaptiveExp
  rw [mpExp_eq]
  exact avg_le fun _ ↦ avg_le fun _ ↦
    (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)

end Game

/-! ## The FORS cover relation -/

section Fors

variable {K Xm Ix Lx : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm]
  [DecidableEq Xm] [Fintype Ix] [DecidableEq Ix] [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx]
  [AddCommGroup Lx] {k : ℕ}
  {L : LocalSig.{u, v}} {A : QReg}

omit [Fintype Ix] [DecidableEq Ix] [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx]
  [AddCommGroup Lx] in
theorem forsCov_mono (S S' : Finset (Ix × (Fin k → Lx))) (u : Ix × (Fin k → Lx)) (h : S ⊆ S')
    (hc : forsCov S u) : forsCov S' u := fun j ↦ by
  obtain ⟨d, hd, h1, h2⟩ := hc j
  exact ⟨d, h hd, h1, h2⟩

/-- **Adaptive ITSR for a random `H_msg` with the FORS index structure.**  Digests
`D = Ix × (Fin k → Lx)` (hypertree leaf, `k` FORS leaf indices in trees of `|Lx| = t` leaves);
at most `q` quantum queries and at most `s` adaptive target requests:
`Pr[win] ≤ (√((2q+1)² ∑_γ C(s,γ) (1/|Ix|)^γ (1 − 1/|Ix|)^(s−γ) (1 − (1 − 1/t)^γ)^k + s²/|K|)
  + 2 q √(s/|K|))²`. -/
theorem itsr_adaptive_fors_le (I : L.Interp) (ρ : SubState A) (s : ℕ)
    (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin k → Lx))) Xm K (fun _ ↦ K × Xm) s A) (q : ℕ)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ s x (forsCov (I := Ix) (L := Lx) (k := k)) ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (∑ γ ∈ range (s + 1),
            (s.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (s - γ) *
              (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k) +
          (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := itsr_adaptive_le (I := I) (ρ := ρ) (Cov := forsCov (I := Ix) (L := Lx) (k := k))
    forsCov_mono hx
  rw [coverProb_fors] at h
  simpa only [Fintype.card_fin] using h

end Fors

end PQ.QROM

#print axioms PQ.QROM.itsrA_eq_B
#print axioms PQ.QROM.itsrB_le
#print axioms PQ.QROM.itsr_hyb_le
#print axioms PQ.QROM.itsr_adaptive_sqrt_le
#print axioms PQ.QROM.itsr_adaptive_le
#print axioms PQ.QROM.itsr_adaptive_fors_le
