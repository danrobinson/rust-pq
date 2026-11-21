import PQ.QROM.ExactItsr
import PQ.QROM.MultiPhase2

/-!
# Adaptive ITSR in the QROM: phase-weighted bound, and an assessment of the reprogramming term

## Results

* `itsr_adaptive_weighted_sqrt_le`, `itsr_adaptive_weighted_le`: if on every path of the game
  the sum over the quantum queries of `s − (number of target requests made before the query)`
  is at most `Wt` (`IsWeightedBound (mpComp s x Rs) (fun t ↦ s - t.length) Wt`), then
  `Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov + s²/|K|) + √(4 q Wt / |K|))²`.
  For at most `qᵢ` queries after exactly `i` requests on every path, `Wt = ∑ᵢ qᵢ (s − i)`.
  `Wt = s q` always holds (`mpComp_isWeightedBound`) and gives back `itsr_adaptive_le`.
* `itsr_adaptive_noloss_le`: `Wt = 0` (all quantum queries after the `s`-th request):
  `Pr[win] ≤ (2q+1)² · coverProb (Fin s) Cov + s²/|K|`, no reprogramming term.
* `itsr_adaptive_fors_qs_le`: `itsr_adaptive_fors_le` with the number of targets named `qs`
  (the number of signing queries of the forger in the SLH-DSA reduction).

## Assessment of the reprogramming term (`|K| = 2^128`)

The step `mp_reprogram` costs `δ = 2 q √(s/|K|)` in the square-root domain
(`√real ≤ √hybrid + δ`), i.e. `≤ 2δ = 4 q √(s/|K|)` additively for an arbitrary event and
`δ² + 2δ√hybrid = 4 q² s/|K| + …` for a small-probability (search) event.

Comparison with Grilo–Hövelmanns–Hülsing–Majenz, "Tight adaptive reprogramming in the QROM"
(distinguishing advantage `≤ (3R/2) √(q · p_max)` for `R` reprogrammings; here `R = s`,
`p_max = 1/|K|`; NOT formalised here, quoted for comparison):

| `s`, `q` | GHHM `(3s/2)√(q/|K|)` | here: `δ = 2q√(s/|K|)` | here, search event: `δ²` | second order `8q²s/|K|` |
|---|---|---|---|---|
| `2^64`, `2^60` | `≈ 2^30.6` (vacuous) | `2^29` (vacuous) | vacuous | `2^59` (vacuous) |
| `2^20`, `2^40` | `≈ 2^-23.4` | `2^-13` (additive form `2^-12`) | `2^-26` (+ cross term `2^-12·√hybrid`) | `2^-25` |

* The two bounds are incomparable: GHHM is linear in the number of reprogrammings and has
  `√q`; the hybrid bound here has `√s` and is linear in `q`.  As additive distinguishing
  bounds (`2δ` against GHHM), the one here is smaller iff `q < (9/64)·s`; for a search event
  the squared form here (`δ² + 2δ√hybrid`) is smaller than GHHM's additive term in the second
  row as long as `hybrid ≲ 2^-23`.
* At `s = 2^64`: GHHM's bound is `≥ 1` for every `q ≥ 1` (`(3/2)·2^64·2^-64 > 1`); the bound
  here is informative only for `q < 2^31` (`δ < 1`), the second-order form only for
  `q < 2^30.5`.  To our knowledge no published technique gives an informative bound for
  adaptive reprogramming at `s = 2^64` fresh points of min-entropy `128` bits and
  `q ≥ 2^32` quantum queries.  This is a statement about known proofs, not about the game: no
  attack on adaptive ITSR exploiting the randomizers is known either.
* Second-order (tight-engine) variant: applying `Purify.qprob_tight_avg`
  (`PQ/QROM/PurifyTight.lean`, `8 q² ε`) to the reprogramming step as a distinguishing step
  would give `|real − hybrid| ≤ 8 q² s/|K|` additively on probabilities, the same order as
  `δ²` here; it needs the N-port version of that engine (it is stated for one function) and
  does not give a cleaner final expression (the search step is in square-root form anyway), so
  it is not proved.

## Why this technique stops at `q² s/|K|`

The first-order (BBBV) hybrid bounds the distance of the final states by the SUM over the
queries of the amplitude on the changed inputs, `∑_j √(mass_j)`, and then Cauchy–Schwarz gives
`√(q ∑_j mass_j)`; the masses on the rows of the unissued randomizers average to
`(s − i)/|K|` per query.  A program whose every query is the uniform superposition over all
randomizers, made before the first request, has exactly `mass_j = s/|K|` for each of its `q`
queries, so the quantity bounded by the technique is `q √(s/|K|)` and cannot be improved
without using more than the masses (it is an example for the estimate, not a distinguisher).
The second-order engine replaces `(∑_j √mass_j)²` by `q²·max mass`, the same order.
GHHM instead use that each reprogrammed point is classical randomness independent of the
state at reprogramming time (per-reprogramming error `√(q/|K|)`), but add the `s` errors
linearly.  A bound adding in quadrature over both queries and reprogrammings
(`√(q s/|K|)`-type, informative while `q s < |K|`, e.g. `2^-2` at `s = 2^64`, `q = 2^60`) is
what a compressed-oracle argument ("the database contains no entry in the row of `R_i` when
`R_i` is issued", probability `≤ q/|K|` per target) suggests; it is NOT proved here and we do
not know a proof in the literature.

## The reduction machine (`Lazy.bItsrL`, `qbItsrL`)

Read from `security/Reduction/Lazy/ItsrLazy.lean` and `quantum/Integration/SlhDsaQuantum.lean`:
the ITSR adversary is the forger run against a lazily simulated signer; each signing query
makes one target request (`bItsrL_queryBound`: at most `qs` target requests), and the
randomizer is handed to the forger in the clear as part of the signature; the forger's hash
queries are interleaved with the signing queries in any adaptive way.  We found no structural
restriction that improves the bound beyond `s := qs` — except the phase weighting above: hash
queries made after `i` signing queries only pay for the `qs − i` randomizers not issued yet
(`Wt = ∑ᵢ qᵢ (qs − i) ≤ q · qs`).  (The games are not composed: `qbItsrL` lives in the
standard-model `QOC` layer, without quantum hash oracle.)
-/

open MeasureTheory ENNReal Quantum Matrix Finset
open scoped Kronecker ComplexOrder

universe u v w

namespace PQ.QROM

section Game

variable {K Xm D : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm] [DecidableEq Xm]
  [Fintype D] [DecidableEq D] [AddCommGroup D]
  {L : LocalSig.{u, v}} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {s : ℕ}
  {x : IAdv L (qromSpec (K × Xm) D) Xm K (fun _ ↦ K × Xm) s A}
  {Cov : Finset D → D → Prop} [∀ S, DecidablePred (Cov S)] {q Wt : ℕ}

/-- **Adaptive ITSR, phase-weighted, square-root form.** -/
theorem itsr_adaptive_weighted_sqrt_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) Wt) :
    itsrAdaptiveExp I ρ s x Cov ^ (2⁻¹ : ℝ) ≤
      ((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
          (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ) :=
  (mp_reprogram_weighted hx hW).trans
    (add_le_add (sqrt_le_sqrt (itsr_hyb_le hmono hx)) le_rfl)

/-- **Adaptive ITSR, phase-weighted.**  If on every path the sum over the quantum queries of
`s − (number of target requests made before the query)` is at most `Wt`:
`Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov + s²/|K|) + √(4 q Wt / |K|))²`. -/
theorem itsr_adaptive_weighted_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) Wt) :
    itsrAdaptiveExp I ρ s x Cov ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
          (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ)) ^ 2 :=
  calc itsrAdaptiveExp I ρ s x Cov = (itsrAdaptiveExp I ρ s x Cov ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' (itsr_adaptive_weighted_sqrt_le hmono hx hW) 2

/-- **Adaptive ITSR without reprogramming loss**: an adversary all of whose quantum queries come
after its `s`-th target request (phase-weighted budget `0`) wins with probability at most
`(2q+1)² · coverProb (Fin s) Cov + s²/|K|`. -/
theorem itsr_adaptive_noloss_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) 0) :
    itsrAdaptiveExp I ρ s x Cov ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
        (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞) :=
  (mp_reprogram_zero hx hW).trans (itsr_hyb_le hmono hx)

end Game

section Fors

variable {K Xm Ix Lx : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm]
  [DecidableEq Xm] [Fintype Ix] [DecidableEq Ix] [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx]
  [AddCommGroup Lx] {k : ℕ}
  {L : LocalSig.{u, v}} {A : QReg}

/-- **Adaptive ITSR for a random `H_msg` with the FORS index structure, `qs` targets**
(`qs` = number of signing queries of the forger in the SLH-DSA reduction; `q` = number of
quantum hash queries). -/
theorem itsr_adaptive_fors_qs_le (I : L.Interp) (ρ : SubState A) (qs : ℕ)
    (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin k → Lx))) Xm K (fun _ ↦ K × Xm) qs A) (q : ℕ)
    (hx : IAdv.IsQueryBound qs x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ qs x (forsCov (I := Ix) (L := Lx) (k := k)) ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (∑ γ ∈ range (qs + 1),
            (qs.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (qs - γ) *
              (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k) +
          (qs : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q * ((qs : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 :=
  itsr_adaptive_fors_le I ρ qs x q hx

/-- The same, phase-weighted: `Wt` bounds, on every path, the sum over the hash queries of
`qs − (number of signing queries made before the hash query)`. -/
theorem itsr_adaptive_fors_qs_weighted_le (I : L.Interp) (ρ : SubState A) (qs : ℕ)
    (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin k → Lx))) Xm K (fun _ ↦ K × Xm) qs A) (q Wt : ℕ)
    (hx : IAdv.IsQueryBound qs x (fun _ ↦ q))
    (hW : ∀ Rs : Fin qs → K,
      IsWeightedBound (mpComp qs x Rs) (fun t : List Xm ↦ qs - t.length) Wt) :
    itsrAdaptiveExp I ρ qs x (forsCov (I := Ix) (L := Lx) (k := k)) ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (∑ γ ∈ range (qs + 1),
            (qs.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (qs - γ) *
              (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k) +
          (qs : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := itsr_adaptive_weighted_le (I := I) (ρ := ρ)
    (Cov := forsCov (I := Ix) (L := Lx) (k := k)) forsCov_mono hx hW
  rw [coverProb_fors] at h
  simpa only [Fintype.card_fin] using h

end Fors

end PQ.QROM

#print axioms PQ.QROM.itsr_adaptive_weighted_le
#print axioms PQ.QROM.itsr_adaptive_noloss_le
#print axioms PQ.QROM.itsr_adaptive_fors_qs_le
#print axioms PQ.QROM.itsr_adaptive_fors_qs_weighted_le
