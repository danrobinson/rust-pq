import PQ.QROM.ExactItsr3

/-!
# Adaptive ITSR in the QROM without a randomizer-collision term

`itsr_adaptive_le` (`ExactItsr.lean`) and `itsr_adaptive_choose_le` (`ExactItsr3.lean`) charge
the event that two randomizers coincide (`s²/|K|`, `C(s,2)/|K|`).  This file removes the term
altogether, by changing the HYBRID, not by excluding repeats.

## Idea

In the hybrid of `mp_reprogram` a row is fresh only at its FIRST issuance; if `R_j = R_i`
(`i < j`) the row of `R_j` is already visible when `x_j` is chosen, the digest of the `j`-th
target is not fresh, and the lazy-sampling step needs injective randomizers.

Here the hybrid re-randomizes the row of `R_j` at EVERY issuance, repeated or not: with
`Ψ : (K × Xm) × Option (Fin s) → D` uniform (one independent function per label), the segment
after `i` requests sees `nFn Rs Ψ i = fun z ↦ Ψ (z, lastIdx Rs i z.1)`, where `lastIdx Rs i r`
is the last index `j < i` with `Rs j = r` (`none` if the row has not been issued).  The final
function `nFn Rs Ψ s` is uniform (`mpExp_eq_N`), so the real game is the world in which every
segment sees the final function.

* The reprogramming loss is the same as before: at the port of a transcript `t` the two
  functions differ only on the rows of the randomizers `R_j`, `j ≥ |t|` (`lastIdx_ne`), and
  `R_j` is uniform and independent of the masses of that port whether or not it repeats an
  earlier randomizer (`mpg_sqrt_le`, the reprogramming step for an arbitrary family of port
  functions with these two properties; phase-weighted).
* In this hybrid the digest of EVERY target point is fresh: the final value at `(R_j, x_j)` has
  the label of the last issuance of the row, which is revealed only after all target inputs of
  that row have been chosen.  Lazy sampling (`itsrN_eq_B`) therefore needs no injectivity:
  distinct target points get distinct pre-sampled digests `d j` (`j` the first index of the
  point), repeated target points share one.  The digests of the targets are among `d`, and
  monotonicity of `Cov` gives the covering probability of `s` independent digests.

The counterexample of `ExactItsr3.lean` (per-tuple domination fails for the first-issuance
hybrid) is not contradicted: for a fixed non-injective tuple the hybrid of this file is far
from the real game; on average over the randomizers the distance is the reprogramming term.

## Results (`Cov` monotone; no collision term)

* `itsr4_adaptive_weighted_le`:
  `Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov) + √(4 q Wt / |K|))²`,
  `Wt` = phase-weighted budget (`IsWeightedBound (mpComp s x Rs) (fun t ↦ s - t.length) Wt`).
* `itsr4_adaptive_le` (general regime, `Wt = s q`):
  `Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov) + 2 q √(s/|K|))²`.
* `itsr4_adaptive_noloss_le` (all quantum queries after the `s`-th request, `Wt = 0`):
  `Pr[win] ≤ (2q+1)² · coverProb (Fin s) Cov`.
* `itsr4_adaptive_fors_le`, `itsr4_adaptive_fors_weighted_le`, `itsr4_adaptive_fors_noloss_le`:
  the FORS relation with the closed form `coverProb_fors`.

## Numbers at `s = 2^64`, `|K| = 2^128` (128s: `k = 14`, `t = 2^12`, `2^63` instances)

With the value `p_cov ≈ 2^-133.7` of `coverProb_fors` at these parameters (computed by the
auditor, not machine-checked here):

* no-reprogramming-loss regime (hash queries after the last target request):
  `(2q+1)² p_cov ≈ 2^-51.7` at `q = 2^40`, `≈ 2^-11.7` at `q = 2^60`;
* phase-weighted regime: add `√(4 q Wt/|K|)` in the square-root domain; small iff
  `q · Wt ≪ 2^126`;
* general regime: the reprogramming term `2 q √(s/|K|) = 2^-23` at `q = 2^8`, `≥ 1` for
  `q ≥ 2^31`: vacuous at `q = 2^40` and `q = 2^60` (unchanged; see `ExactItsr2.lean`).
-/

open MeasureTheory ENNReal Quantum Matrix Finset
open scoped Kronecker ComplexOrder

universe u v w

namespace PQ.QROM

/-! ## The reprogramming step for an arbitrary family of port functions -/

section Generic

variable {K M Y Req Par : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype M]
  [DecidableEq M] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Par]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- Mass of the run against the port functions `fam Rs Φ |t|` on the pair `c`. -/
noncomputable def mpgMass (I : L.Interp) (ρ : SubState A) {s : ℕ}
    (x : IAdv L (qromSpec (K × M) Y) Req K Out s A)
    (fam : (Fin s → K) → Par → ℕ → K × M → Y) (Rs : Fin s → K) (Φ : Par)
    (c : Σ _ : List Req, K × M) : ℝ≥0∞ :=
  massN I (fun t : List Req ↦ fam Rs Φ t.length) (mpComp s x Rs) (joint ρ) c

variable {I : L.Interp} {ρ : SubState A} {s : ℕ} {x : IAdv L (qromSpec (K × M) Y) Req K Out s A}
  {q Wt : ℕ} {fam : (Fin s → K) → Par → ℕ → K × M → Y}

omit [Fintype Par] in
theorem mpgMass_update
    (hupd : ∀ (Rs : Fin s → K) (Φ : Par) (j : Fin s) (r : K) (m : ℕ), m ≤ j.1 →
      fam (Function.update Rs j r) Φ m = fam Rs Φ m)
    (Rs : Fin s → K) (Φ : Par) (j : Fin s) (r : K)
    (c : Σ _ : List Req, K × M) (hc : c.1.length ≤ j.1) :
    mpgMass I ρ x fam (Function.update Rs j r) Φ c = mpgMass I ρ x fam Rs Φ c := by
  classical
  unfold mpgMass massN QuantumRuntime.indexMass QuantumRuntime.indexMassAt mpComp
  refine tsum_congr fun i ↦ ?_
  refine pflat_queryWeight_congr I (D := QReg.of Unit) (σ₁ := SubState.basis ())
    (σ₂ := SubState.basis ())
    (s₁ := fun t : List Req ↦ (oracleQuery (fam (Function.update Rs j r) Φ t.length)).frame Unit)
    (s₂ := fun t : List Req ↦ (oracleQuery (fam Rs Φ t.length)).frame Unit)
    (rndCh (Function.update Rs j r)) (rndCh Rs) (fun p t ↦ p <+: t)
    (fun req t t' ↦ rndCh_step _ req t t') (fun req t t' ↦ rndCh_step _ req t t') c.1
    (fun req t ↦ ?_) (fun p hp ↦ ?_) (fun p hp σ ↦ ?_) s [] x _ i
  · by_cases ht : t.length = j.1
    · right
      have hlen : ¬ (t ++ [req]) <+: c.1 := fun h ↦ by
        have := h.length_le
        simp at this
        omega
      exact ⟨hlen, hlen⟩
    · left
      unfold rndCh
      rw [rndAt_update Rs j r ht]
  · have hle : p.length ≤ j.1 := hp.length_le.trans hc
    simp only [hupd Rs Φ j r _ hle]
  · have hne : p ≠ c.1 := fun h ↦ hp (h ▸ List.prefix_refl _)
    have : ∀ k : K × M, (⟨p, k⟩ : Σ _ : List Req, K × M) ≠ c := fun k h ↦ hne (by rw [← h])
    simp [this]

omit [Fintype Par] in
theorem mpg_diffMass_le
    (hne : ∀ (Rs : Fin s → K) (Φ : Par) (m : ℕ) (z : K × M),
      fam Rs Φ s z ≠ fam Rs Φ m z → ∃ j : Fin s, m ≤ j.1 ∧ Rs j = z.1)
    (Rs : Fin s → K) (Φ : Par) :
    diffMass I (fun _ ↦ fam Rs Φ s) (fun t : List Req ↦ fam Rs Φ t.length) (mpComp s x Rs)
        (joint ρ) ≤
      ∑ j : Fin s, ∑' c : Σ _ : List Req, K × M,
        if c.1.length ≤ j.1 then (if Rs j = c.2.1 then mpgMass I ρ x fam Rs Φ c else 0)
        else 0 := by
  unfold diffMass
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine tsum_le_tsum fun c ↦ ?_
  split_ifs with h
  · obtain ⟨j, hj, hR⟩ := hne Rs Φ _ _ h
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ j))
    simp only [hj, hR, ↓reduceIte]
    rfl
  · exact zero_le

theorem avg_mpg_diffMass_le
    (hupd : ∀ (Rs : Fin s → K) (Φ : Par) (j : Fin s) (r : K) (m : ℕ), m ≤ j.1 →
      fam (Function.update Rs j r) Φ m = fam Rs Φ m)
    (hne : ∀ (Rs : Fin s → K) (Φ : Par) (m : ℕ) (z : K × M),
      fam Rs Φ s z ≠ fam Rs Φ m z → ∃ j : Fin s, m ≤ j.1 ∧ Rs j = z.1)
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Req ↦ s - t.length) Wt) :
    (avg fun Rs : Fin s → K ↦ avg fun Φ : Par ↦
      diffMass I (fun _ ↦ fam Rs Φ s) (fun t : List Req ↦ fam Rs Φ t.length) (mpComp s x Rs)
        (joint ρ)) ≤ (Fintype.card K : ℝ≥0∞)⁻¹ * Wt := by
  refine (avg_mono fun Rs ↦ avg_mono fun Φ ↦ mpg_diffMass_le hne Rs Φ).trans ?_
  rw [avg_comm]
  refine avg_le fun Φ ↦ ?_
  rw [avg_finset_sum]
  have hj : ∀ j : Fin s, (avg fun Rs : Fin s → K ↦ ∑' c : Σ _ : List Req, K × M,
      if c.1.length ≤ j.1 then (if Rs j = c.2.1 then mpgMass I ρ x fam Rs Φ c else 0) else 0) ≤
      (Fintype.card K : ℝ≥0∞)⁻¹ * avg fun Rs : Fin s → K ↦ ∑' c : Σ _ : List Req, K × M,
        if c.1.length ≤ j.1 then mpgMass I ρ x fam Rs Φ c else 0 := by
    intro j
    rw [avg_tsum, avg_tsum, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun c ↦ ?_
    by_cases hlen : c.1.length ≤ j.1
    · simp only [hlen, ↓reduceIte]
      exact (avg_coord_eq j c.2.1 (fun Rs ↦ mpgMass I ρ x fam Rs Φ c)
        fun Rs r ↦ mpgMass_update hupd Rs Φ j r c hlen).le
    · simp only [hlen, ↓reduceIte]
      exact (avg_le (c := 0) fun _ ↦ le_rfl).trans zero_le
  refine (Finset.sum_le_sum fun j _ ↦ hj j).trans ?_
  rw [← Finset.mul_sum, ← avg_finset_sum]
  refine mul_le_mul' le_rfl (avg_le fun Rs ↦ ?_)
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  simp only [sum_fin_ite_le]
  exact (tsum_weighted_massN_le I _ (joint_posSemidef ρ) _ (hW Rs)).trans
    ((mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans (mul_one _).le)

/-- **Reprogramming step for an arbitrary family of port functions.**  `fam Rs Φ m` is the
function seen after `m` requests.  If it does not depend on the randomizers `R_j`, `j ≥ m`, and
differs from the final function `fam Rs Φ s` only on rows of randomizers `R_j`, `j ≥ m`, then
the world where every segment sees the final function and the world where the segment after
`m` requests sees `fam Rs Φ m` are `√(4 q Wt/|K|)`-close in square root, for every event. -/
theorem mpg_sqrt_le
    (hupd : ∀ (Rs : Fin s → K) (Φ : Par) (j : Fin s) (r : K) (m : ℕ), m ≤ j.1 →
      fam (Function.update Rs j r) Φ m = fam Rs Φ m)
    (hne : ∀ (Rs : Fin s → K) (Φ : Par) (m : ℕ) (z : K × M),
      fam Rs Φ s z ≠ fam Rs Φ m z → ∃ j : Fin s, m ≤ j.1 ∧ Rs j = z.1)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Req ↦ s - t.length) Wt)
    (win : (Fin s → K) → Par → (Σ u, Out u × List Req) → Prop) :
    (avg fun Rs : Fin s → K ↦ avg fun Φ : Par ↦
        leafProb (nRuntime fun _ ↦ fam Rs Φ s) I (mpComp s x Rs) (joint ρ) (win Rs Φ)) ^
          (2⁻¹ : ℝ) ≤
      (avg fun Rs : Fin s → K ↦ avg fun Φ : Par ↦
        leafProb (nRuntime fun t : List Req ↦ fam Rs Φ t.length) I (mpComp s x Rs) (joint ρ)
          (win Rs Φ)) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ) := by
  refine (sqrt_avg_le _ _ _ fun Rs ↦ sqrt_avg_le _ _ _ fun Φ ↦
    (nRuntime_sqrt_le I (fun _ ↦ fam Rs Φ s) (fun t : List Req ↦ fam Rs Φ t.length)
      (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs) (win Rs Φ)).1).trans
    (add_le_add le_rfl (sqrt_le_sqrt ?_))
  simp only [avg_mul_left]
  exact mul_le_mul' le_rfl (avg_mpg_diffMass_le hupd hne hW)

end Generic

/-! ## Selection masses with an arbitrary label type -/

section SelG

/-- The mass on the pairs `(z, b)`: the masses `μ ⟨t, z⟩` of the ports `t` whose label at `z`
is `b`. -/
noncomputable def selMassG {P Z B : Type} [DecidableEq B] (bs : P → Z → B)
    (μ : (Σ _ : P, Z) → ℝ≥0∞) (y : Z × B) : ℝ≥0∞ :=
  ∑' t : P, if bs t y.1 = y.2 then μ ⟨t, y.1⟩ else 0

theorem sum_selMassG {P Z B : Type} [Fintype Z] [DecidableEq Z] [Fintype B] [DecidableEq B]
    (bs : P → Z → B) (μ : (Σ _ : P, Z) → ℝ≥0∞) (S : Finset (Z × B)) :
    ∑ k ∈ S, selMassG bs μ k =
      ∑' c : Σ _ : P, Z, if (c.2, bs c.1 c.2) ∈ S then μ c else 0 := by
  unfold selMassG
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  have hsig : (∑' c : Σ _ : P, Z, if (c.2, bs c.1 c.2) ∈ S then μ c else 0) =
      ∑' t : P, ∑ z : Z, if (z, bs t z) ∈ S then μ ⟨t, z⟩ else 0 :=
    (tsum_sigma (β := fun _ : P ↦ Z)
      fun t z ↦ if (z, bs t z) ∈ S then μ ⟨t, z⟩ else 0).trans
      (tsum_congr fun t ↦ tsum_fintype _)
  rw [hsig]
  refine tsum_congr fun t ↦ ?_
  calc ∑ k ∈ S, (if bs t k.1 = k.2 then μ ⟨t, k.1⟩ else 0)
      = ∑ k : Z × B, if k ∈ S then (if bs t k.1 = k.2 then μ ⟨t, k.1⟩ else 0) else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ z : Z, ∑ b : B,
          if (z, b) ∈ S then (if bs t z = b then μ ⟨t, z⟩ else 0) else 0 :=
        Fintype.sum_prod_type _
    _ = _ := by
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [Finset.sum_eq_single (bs t z)]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · intro h
          exact absurd (Finset.mem_univ _) h

end SelG

/-! ## Labels, first indices, the re-randomizing hybrid -/

section DefsN

variable {K Xm D : Type} {s : ℕ} [DecidableEq K]

/-- The indices `j < m` at which the randomizer `r` is issued. -/
def lastSet (Rs : Fin s → K) (m : ℕ) (r : K) : Finset (Fin s) :=
  univ.filter fun j ↦ j.1 < m ∧ Rs j = r

/-- The last index `j < m` with `Rs j = r`, if any: the label of the row of `r` after `m`
requests. -/
def lastIdx (Rs : Fin s → K) (m : ℕ) (r : K) : Option (Fin s) :=
  if h : (lastSet Rs m r).Nonempty then some ((lastSet Rs m r).max' h) else none

theorem lastIdx_update (Rs : Fin s → K) (j : Fin s) (r r' : K) {m : ℕ} (hm : m ≤ j.1) :
    lastIdx (Function.update Rs j r') m r = lastIdx Rs m r := by
  have h : lastSet (Function.update Rs j r') m r = lastSet Rs m r := by
    ext i
    simp only [lastSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_right fun hi ↦ ?_
    have : i ≠ j := fun h ↦ by rw [h] at hi; omega
    rw [Function.update_of_ne this]
  unfold lastIdx
  rw [h]

theorem lastIdx_ne {Rs : Fin s → K} {m : ℕ} {r : K} (h : lastIdx Rs s r ≠ lastIdx Rs m r) :
    ∃ j : Fin s, m ≤ j.1 ∧ Rs j = r := by
  by_contra hne
  push Not at hne
  refine h ?_
  have hs : lastSet Rs s r = lastSet Rs m r := by
    ext i
    simp only [lastSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hi⟩
      refine ⟨?_, hi⟩
      by_contra hlt
      exact hne i (by omega) hi
    · rintro ⟨_, hi⟩
      exact ⟨i.2, hi⟩
  unfold lastIdx
  rw [hs]

theorem lastIdx_lt {Rs : Fin s → K} {m : ℕ} {r : K} {l : Fin s} (h : lastIdx Rs m r = some l) :
    l.1 < m := by
  unfold lastIdx at h
  split_ifs at h with hn
  have hmem := Finset.max'_mem _ hn
  rw [Option.some.inj h] at hmem
  exact (Finset.mem_filter.1 hmem).2.1

theorem lastIdx_ge (Rs : Fin s → K) (j : Fin s) :
    ∃ l : Fin s, lastIdx Rs s (Rs j) = some l ∧ j ≤ l := by
  have hj : j ∈ lastSet Rs s (Rs j) := Finset.mem_filter.2 ⟨Finset.mem_univ _, j.2, rfl⟩
  have hn : (lastSet Rs s (Rs j)).Nonempty := ⟨j, hj⟩
  refine ⟨(lastSet Rs s (Rs j)).max' hn, ?_, Finset.le_max' _ _ hj⟩
  unfold lastIdx
  simp [hn]

variable [DecidableEq Xm]

/-- The indices of the target point `z` in the transcript `t`. -/
def tgtSet (Rs : Fin s → K) (t : List Xm) (z : K × Xm) : Finset (Fin s) :=
  univ.filter fun j ↦ Rs j = z.1 ∧ t[j.1]? = some z.2

/-- The first index of the target point `z` in the transcript `t`, if `z` is a target. -/
def firstIdx (Rs : Fin s → K) (t : List Xm) (z : K × Xm) : Option (Fin s) :=
  if h : (tgtSet Rs t z).Nonempty then some ((tgtSet Rs t z).min' h) else none

theorem firstIdx_some {Rs : Fin s → K} {t : List Xm} {z : K × Xm} {j : Fin s}
    (h : firstIdx Rs t z = some j) : Rs j = z.1 ∧ t[j.1]? = some z.2 := by
  unfold firstIdx at h
  split_ifs at h with hn
  have hmem := Finset.min'_mem _ hn
  rw [Option.some.inj h] at hmem
  exact (Finset.mem_filter.1 hmem).2

theorem firstIdx_of_isTgt {Rs : Fin s → K} {t : List Xm} {z : K × Xm} (h : isTgt Rs t z) :
    ∃ j, firstIdx Rs t z = some j := by
  obtain ⟨j, hj⟩ := h
  have hn : (tgtSet Rs t z).Nonempty := ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
  refine ⟨(tgtSet Rs t z).min' hn, ?_⟩
  unfold firstIdx
  simp [hn]

theorem firstIdx_of_not {Rs : Fin s → K} {t : List Xm} {z : K × Xm} (h : ¬ isTgt Rs t z) :
    firstIdx Rs t z = none := by
  have hn : ¬ (tgtSet Rs t z).Nonempty := by
    rintro ⟨j, hj⟩
    exact h ⟨j, (Finset.mem_filter.1 hj).2⟩
  unfold firstIdx
  simp [hn]

/-- The function after `m` requests in the re-randomizing hybrid: the row of `r` carries the
label of its last issuance before `m`. -/
def nFn (Rs : Fin s → K) (Ψ : (K × Xm) × Option (Fin s) → D) (m : ℕ) : K × Xm → D :=
  fun z ↦ Ψ (z, lastIdx Rs m z.1)

/-- `Ψ` with its value at every target point `z` of `t`, at the final label of the row of `z`,
overwritten by the digest `d j`, `j` the first index of `z`. -/
def owN (Rs : Fin s → K) (t : List Xm) (d : Fin s → D) (Ψ : (K × Xm) × Option (Fin s) → D) :
    (K × Xm) × Option (Fin s) → D :=
  fun y ↦ (firstIdx Rs t y.1).elim (Ψ y)
    fun j ↦ if y.2 = lastIdx Rs s y.1.1 then d j else Ψ y

/-- The digests `d` with `d j` overwritten, for the first index `j` of a target point, by the
value of `Ψ` at that point and the final label of its row. -/
def rdN (Rs : Fin s → K) (t : List Xm) (d : Fin s → D) (Ψ : (K × Xm) × Option (Fin s) → D) :
    Fin s → D :=
  fun j ↦ (t[j.1]?).elim (d j)
    fun x ↦ if firstIdx Rs t (Rs j, x) = some j then Ψ ((Rs j, x), lastIdx Rs s (Rs j)) else d j

/-- Swapping the final values at the target points with the pre-sampled digests is an
involution, for every tuple of randomizers. -/
theorem swapN_involutive (Rs : Fin s → K) (t : List Xm) :
    Function.Involutive (fun v : ((K × Xm) × Option (Fin s) → D) × (Fin s → D) ↦
      (owN Rs t v.2 v.1, rdN Rs t v.2 v.1)) := by
  rintro ⟨Ψ, d⟩
  refine Prod.ext (funext fun y ↦ ?_) (funext fun j ↦ ?_)
  · obtain ⟨z, b⟩ := y
    show (firstIdx Rs t z).elim (owN Rs t d Ψ (z, b))
      (fun j ↦ if b = lastIdx Rs s z.1 then rdN Rs t d Ψ j else owN Rs t d Ψ (z, b)) = Ψ (z, b)
    have hΨ : owN Rs t d Ψ (z, b) = (firstIdx Rs t z).elim (Ψ (z, b))
        (fun j ↦ if b = lastIdx Rs s z.1 then d j else Ψ (z, b)) := rfl
    cases hf : firstIdx Rs t z with
    | none => rw [hΨ, hf]; rfl
    | some m =>
      rw [Option.elim_some]
      by_cases hb : b = lastIdx Rs s z.1
      · rw [ite_eq_left hb]
        obtain ⟨hR, ht⟩ := firstIdx_some hf
        have hz : (Rs m, z.2) = z := Prod.ext hR rfl
        show (t[m.1]?).elim (d m) (fun x ↦ if firstIdx Rs t (Rs m, x) = some m then
          Ψ ((Rs m, x), lastIdx Rs s (Rs m)) else d m) = Ψ (z, b)
        rw [ht, Option.elim_some, hz, ite_eq_left hf, hR, hb]
      · rw [ite_eq_right hb, hΨ, hf, Option.elim_some, ite_eq_right hb]
  · show (t[j.1]?).elim (rdN Rs t d Ψ j) (fun x ↦ if firstIdx Rs t (Rs j, x) = some j then
      owN Rs t d Ψ ((Rs j, x), lastIdx Rs s (Rs j)) else rdN Rs t d Ψ j) = d j
    have hd : rdN Rs t d Ψ j = (t[j.1]?).elim (d j) (fun x ↦
        if firstIdx Rs t (Rs j, x) = some j then Ψ ((Rs j, x), lastIdx Rs s (Rs j))
        else d j) := rfl
    cases hx : t[j.1]? with
    | none => rw [hd, hx]; rfl
    | some x =>
      rw [Option.elim_some]
      by_cases hc : firstIdx Rs t (Rs j, x) = some j
      · rw [ite_eq_left hc]
        show (firstIdx Rs t (Rs j, x)).elim _ _ = d j
        rw [hc, Option.elim_some, ite_eq_left rfl]
      · rw [ite_eq_right hc, hd, hx, Option.elim_some, ite_eq_right hc]

/-- The function of the lazily-sampled world at the transcript port `t`. -/
def nBFn (Rs : Fin s → K) (d : Fin s → D) (Ψ : (K × Xm) × Option (Fin s) → D)
    (t : List Xm) : K × Xm → D :=
  nFn Rs (owN Rs t d Ψ) t.length

/-- Overwriting at the targets of a transcript `t` agrees, on the port of a prefix `t'` of `t`,
with overwriting at the targets of `t'` (no injectivity needed). -/
theorem nFn_owN_prefix (Rs : Fin s → K) (d : Fin s → D)
    (Ψ : (K × Xm) × Option (Fin s) → D) {t' t : List Xm} (h : t' <+: t) :
    nFn Rs (owN Rs t d Ψ) t'.length = nBFn Rs d Ψ t' := by
  obtain ⟨r, rfl⟩ := h
  funext z
  show (firstIdx Rs (t' ++ r) z).elim (Ψ (z, lastIdx Rs t'.length z.1))
      (fun j ↦ if lastIdx Rs t'.length z.1 = lastIdx Rs s z.1 then d j
        else Ψ (z, lastIdx Rs t'.length z.1)) =
    (firstIdx Rs t' z).elim (Ψ (z, lastIdx Rs t'.length z.1))
      (fun j ↦ if lastIdx Rs t'.length z.1 = lastIdx Rs s z.1 then d j
        else Ψ (z, lastIdx Rs t'.length z.1))
  by_cases hl : lastIdx Rs t'.length z.1 = lastIdx Rs s z.1
  · have hset : tgtSet Rs (t' ++ r) z = tgtSet Rs t' z := by
      ext j
      simp only [tgtSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hR, ht⟩
        have hlt : j.1 < t'.length := by
          obtain ⟨l, hl', hjl⟩ := lastIdx_ge Rs j
          rw [hR, ← hl] at hl'
          have h1 := lastIdx_lt hl'
          have h2 : j.1 ≤ l.1 := hjl
          omega
        exact ⟨hR, by rw [← ht, List.getElem?_append_left hlt]⟩
      · rintro ⟨hR, ht⟩
        have hlt : j.1 < t'.length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at ht
          cases ht
        exact ⟨hR, by rw [← ht, List.getElem?_append_left hlt]⟩
    have hf : firstIdx Rs (t' ++ r) z = firstIdx Rs t' z := by
      unfold firstIdx
      rw [hset]
    rw [hf]
  · cases firstIdx Rs (t' ++ r) z <;> cases firstIdx Rs t' z <;> simp [hl]

/-- Where the port functions built from `Ψ` and `Ψ'` differ, `Ψ` and `Ψ'` differ at the
labelled point. -/
theorem nBFn_ne {Rs : Fin s → K} {d : Fin s → D} {Ψ Ψ' : (K × Xm) × Option (Fin s) → D}
    {t : List Xm} {z : K × Xm} (h : nBFn Rs d Ψ t z ≠ nBFn Rs d Ψ' t z) :
    Ψ (z, lastIdx Rs t.length z.1) ≠ Ψ' (z, lastIdx Rs t.length z.1) := by
  intro heq
  refine h ?_
  show (firstIdx Rs t z).elim (Ψ (z, lastIdx Rs t.length z.1))
      (fun j ↦ if lastIdx Rs t.length z.1 = lastIdx Rs s z.1 then d j
        else Ψ (z, lastIdx Rs t.length z.1)) =
    (firstIdx Rs t z).elim (Ψ' (z, lastIdx Rs t.length z.1))
      (fun j ↦ if lastIdx Rs t.length z.1 = lastIdx Rs s z.1 then d j
        else Ψ' (z, lastIdx Rs t.length z.1))
  rw [heq]

variable [Fintype K] [Fintype Xm] [Fintype D] [DecidableEq D]

/-- A winning leaf of the lazily-sampled world: the labelled value of `Ψ` at the output lies in
the set covered by the pre-sampled digests. -/
theorem itsrAWin_owN (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (Rs : Fin s → K) (d : Fin s → D) (Ψ : (K × Xm) × Option (Fin s) → D)
    (p : Σ _ : QReg, (K × Xm) × List Xm)
    (h : itsrAWin Cov Rs (nFn Rs (owN Rs p.2.2 d Ψ) s) p) :
    Ψ (p.2.1, lastIdx Rs s p.2.1.1) ∈ covered Cov (univ.image d) := by
  obtain ⟨hnt, hcov⟩ := h
  have hnt' : ¬ isTgt Rs p.2.2 p.2.1 := fun ht ↦
    hnt (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)
  have hval : nFn Rs (owN Rs p.2.2 d Ψ) s p.2.1 = Ψ (p.2.1, lastIdx Rs s p.2.1.1) := by
    show (firstIdx Rs p.2.2 p.2.1).elim _ _ = _
    rw [firstIdx_of_not hnt']
    rfl
  rw [hval] at hcov
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hmono _ _ _ (fun v hv ↦ ?_) hcov⟩
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
  have ht : isTgt Rs p.2.2 z := (Finset.mem_filter.1 hz).2
  obtain ⟨j, hj⟩ := firstIdx_of_isTgt ht
  have : nFn Rs (owN Rs p.2.2 d Ψ) s z = d j := by
    show (firstIdx Rs p.2.2 z).elim _ (fun j ↦ if lastIdx Rs s z.1 = lastIdx Rs s z.1 then d j
      else _) = _
    rw [hj, Option.elim_some, ite_eq_left rfl]
  rw [this]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

end DefsN

/-! ## The bound -/

section GameN

variable {K Xm D : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm] [DecidableEq Xm]
  [Fintype D] [DecidableEq D] [AddCommGroup D]
  {L : LocalSig.{u, v}} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {s : ℕ}
  {x : IAdv L (qromSpec (K × Xm) D) Xm K (fun _ ↦ K × Xm) s A}
  {Cov : Finset D → D → Prop} [∀ S, DecidablePred (Cov S)] {q Wt : ℕ}

omit [∀ S, DecidablePred (Cov S)] in
/-- The real experiment, with the uniform function written as the final function of the
re-randomizing hybrid. -/
theorem mpExp_eq_N [Nonempty D]
    (win : (Fin s → K) → (K × Xm → D) → (Σ _ : QReg, (K × Xm) × List Xm) → Prop) :
    mpExp I ρ s x win =
      avg fun Rs : Fin s → K ↦ avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦
        leafProb (nRuntime fun _ ↦ nFn Rs Ψ s) I (mpComp s x Rs) (joint ρ)
          (win Rs (nFn Rs Ψ s)) := by
  rw [mpExp_eq]
  refine avg_congr fun Rs ↦ ?_
  have hinj : Function.Injective
      (fun z : K × Xm ↦ ((z, lastIdx Rs s z.1) : (K × Xm) × Option (Fin s))) :=
    fun a b h ↦ congrArg Prod.fst h
  exact (sum_comp_injective' _ hinj
    (fun H : K × Xm → D ↦ leafProb (nRuntime fun _ ↦ H) I (mpComp s x Rs) (joint ρ)
      (win Rs H))).symm

omit [∀ S, DecidablePred (Cov S)] in
/-- **Lazy sampling of the target digests, for every tuple of randomizers.** -/
theorem itsrN_eq_B [Nonempty D] (Rs : Fin s → K) :
    (avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦
      leafProb (nRuntime fun t : List Xm ↦ nFn Rs Ψ t.length) I (mpComp s x Rs) (joint ρ)
        (itsrAWin Cov Rs (nFn Rs Ψ s))) =
      avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦ avg fun d : Fin s → D ↦
        leafProb (nRuntime (nBFn Rs d Ψ)) I (mpComp s x Rs) (joint ρ)
          (fun p ↦ itsrAWin Cov Rs (nFn Rs (owN Rs p.2.2 d Ψ) s) p) := by
  unfold leafProb
  simp only [avg_tsum]
  refine tsum_congr fun p ↦ ?_
  obtain ⟨u, o, t⟩ := p
  refine (avg_involutive _ (swapN_involutive Rs t)
    (fun Ψ : (K × Xm) × Option (Fin s) → D ↦
      ENNReal.ofReal ((((nRuntime fun t : List Xm ↦ nFn Rs Ψ t.length).run I
        (mpComp s x Rs)).branch ⟨u, (o, t)⟩) (joint ρ)).trace.re *
        ind (itsrAWin Cov Rs (nFn Rs Ψ s) ⟨u, (o, t)⟩))).symm.trans ?_
  refine avg_congr fun Ψ ↦ avg_congr fun d ↦ ?_
  have hbr : ((nRuntime fun t' : List Xm ↦ nFn Rs (owN Rs t d Ψ) t'.length).run I
      (mpComp s x Rs)).branch ⟨u, (o, t)⟩ =
      ((nRuntime (nBFn Rs d Ψ)).run I (mpComp s x Rs)).branch ⟨u, (o, t)⟩ :=
    pflat_branch_congr I (D := QReg.of Unit) (σ₁ := SubState.basis ())
      (σ₂ := SubState.basis ())
      (s₁ := fun t' : List Xm ↦ (oracleQuery (nFn Rs (owN Rs t d Ψ) t'.length)).frame Unit)
      (s₂ := fun t' : List Xm ↦ (oracleQuery (nBFn Rs d Ψ t')).frame Unit)
      (rndCh Rs) (fun p t ↦ p <+: t) (fun _ ↦ List.prefix_refl _)
      (fun req t t' ↦ rndCh_step _ req t t') t
      (fun t' ht' ↦ by rw [nFn_owN_prefix Rs d Ψ ht']) s [] x u o
  show ENNReal.ofReal ((((nRuntime fun t' : List Xm ↦ nFn Rs (owN Rs t d Ψ) t'.length).run I
      (mpComp s x Rs)).branch ⟨u, (o, t)⟩) (joint ρ)).trace.re *
      ind (itsrAWin Cov Rs (nFn Rs (owN Rs t d Ψ) s) ⟨u, (o, t)⟩) = _
  rw [hbr]

/-- **Search in the lazily-sampled world**, for fixed randomizers (any tuple) and fixed
pre-sampled digests. -/
theorem itsrNB_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) (Rs : Fin s → K) (d : Fin s → D) :
    (avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦
      leafProb (nRuntime (nBFn Rs d Ψ)) I (mpComp s x Rs) (joint ρ)
        (fun p ↦ itsrAWin Cov Rs (nFn Rs (owN Rs p.2.2 d Ψ) s) p)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        (((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
  classical
  set C : Finset D := covered Cov (univ.image d) with hC
  set F : ((K × Xm) × Option (Fin s) → D) → ℝ≥0∞ := fun Ψ ↦
    leafProb (nRuntime (nBFn Rs d Ψ)) I (mpComp s x Rs) (joint ρ)
      (fun p ↦ itsrAWin Cov Rs (nFn Rs (owN Rs p.2.2 d Ψ) s) p) with hF
  have hF1 : ∀ Ψ, F Ψ ≤ 1 := fun Ψ ↦
    (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)
  by_cases hU : Cᶜ.Nonempty
  · set U : {U : Finset D // U.Nonempty} := ⟨Cᶜ, hU⟩ with hUdef
    set cXD : ℝ≥0∞ := (Fintype.card ((K × Xm) × Option (Fin s) → D) : ℝ≥0∞) with hcXD
    set cXR : ℝ≥0∞ := (Fintype.card ((K × Xm) × Option (Fin s) → Res D) : ℝ≥0∞) with hcXR
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel Fintype.card_ne_zero
    have iXR : cXR * cXR⁻¹ = 1 := natCast_mul_inv_cancel Fintype.card_ne_zero
    set κ : ℝ≥0∞ := cXD⁻¹ * cXR⁻¹ with hκ
    have hw : ∑ _τ : (K × Xm) × Option (Fin s) → D × Res D, κ ≤ 1 := by
      have := sum_fst_comp (X := (K × Xm) × Option (Fin s)) (A := D) (B := Res D) (fun _ ↦ κ)
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc cXR * (cXD * κ) = (cXD * cXD⁻¹) * (cXR * cXR⁻¹) := by rw [hκ]; ring
        _ ≤ 1 := by rw [iXD, iXR, mul_one]
    have hH : Hidden (Ω := (K × Xm) × Option (Fin s) → D × Res D) (fun _ ↦ κ)
        (fun τ k ↦ resU U (τ k)) (fun τ ↦ univ.filter fun k ↦ (τ k).1 ∉ U.1) (pMark U) := by
      intro k φ
      have h := hidden_itsr (X := (K × Xm) × Option (Fin s))
        (∅ : Finset ((K × Xm) × Option (Fin s)))
        (fun _ ↦ Classical.arbitrary D) U κ k φ
      simpa using h
    let outB : (Σ _ : QReg, (K × Xm) × List Xm) → (K × Xm) × Option (Fin s) := fun p ↦
      (p.2.1, lastIdx Rs s p.2.1.1)
    let bs : List Xm → K × Xm → Option (Fin s) := fun t z ↦ lastIdx Rs t.length z.1
    let pr : ((K × Xm) × Option (Fin s) → D) → (K × Xm) × Option (Fin s) → ℝ≥0∞ := fun v y ↦
      leafProb (nRuntime (nBFn Rs d v)) I (mpComp s x Rs) (joint ρ) (fun p ↦ outB p = y)
    let mm : ((K × Xm) × Option (Fin s) → D) → (K × Xm) × Option (Fin s) → ℝ≥0∞ := fun v ↦
      selMassG bs (massN I (nBFn Rs d v) (mpComp s x Rs) (joint ρ))
    have hpr : ∀ v, ∑ k, pr v k ≤ 1 := fun v ↦
      (sum_leafProb_eq_le (R := nRuntime (nBFn Rs d v)) (I := I) (mpComp s x Rs)
        (joint_posSemidef ρ) outB).trans (ofReal_trace_joint_le_one ρ)
    have hmm : ∀ v, ∑ k, mm v k ≤ q := fun v ↦ by
      have h := sum_selMassG bs (massN I (nBFn Rs d v) (mpComp s x Rs) (joint ρ)) univ
      simp only [Finset.mem_univ, ite_true] at h
      rw [h]
      exact (tsum_massN_le I _ (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs)).trans
        ((mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans (mul_one _).le)
    have hs := hH.search_le' hw q (fun τ ↦ F fun k ↦ (τ k).1) pr mm hpr hmm (by
      intro τ
      set Φ : (K × Xm) × Option (Fin s) → D := fun k ↦ (τ k).1 with hΦ
      set Φh : (K × Xm) × Option (Fin s) → D := fun k ↦ resU U (τ k) with hΦh
      set Sτ : Finset ((K × Xm) × Option (Fin s)) :=
        univ.filter fun k ↦ (τ k).1 ∉ U.1 with hSτ
      have h1 : F Φ ≤ leafProb (nRuntime (nBFn Rs d Φ)) I (mpComp s x Rs) (joint ρ)
          (fun p ↦ outB p ∈ Sτ) :=
        leafProb_mono _ _ fun p hp ↦ by
          have hc := itsrAWin_owN Cov hmono Rs d Φ p hp
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hin ↦ ?_⟩
          exact (Finset.mem_compl.1 hin) hc
      have h2 := (nRuntime_sqrt_le I (nBFn Rs d Φ) (nBFn Rs d Φh)
        (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs) (fun p ↦ outB p ∈ Sτ)).1
      have h3 : leafProb (nRuntime (nBFn Rs d Φh)) I (mpComp s x Rs) (joint ρ)
          (fun p ↦ outB p ∈ Sτ) ≤ ∑ k ∈ Sτ, pr Φh k :=
        leafProb_mem_le_sum _ _ outB Sτ
      have h4 : diffMass I (nBFn Rs d Φ) (nBFn Rs d Φh) (mpComp s x Rs) (joint ρ) ≤
          ∑ k ∈ Sτ, mm Φh k := by
        rw [sum_selMassG]
        unfold diffMass
        refine tsum_le_tsum fun c ↦ ?_
        by_cases hne : nBFn Rs d Φ c.1 c.2 ≠ nBFn Rs d Φh c.1 c.2
        · have hin : (c.2, bs c.1 c.2) ∈ Sτ := by
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hin ↦ nBFn_ne hne ?_⟩
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
    have e' := sum_fst_comp (X := (K × Xm) × Option (Fin s)) (A := D) (B := Res D)
      (fun Φ ↦ κ * F Φ)
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

/-- The re-randomizing hybrid experiment is won with probability at most
`(2q+1)² · coverProb (Fin s) Cov`: no collision term. -/
theorem itsrN_hyb_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    (avg fun Rs : Fin s → K ↦ avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦
      leafProb (nRuntime fun t : List Xm ↦ nFn Rs Ψ t.length) I (mpComp s x Rs) (joint ρ)
        (itsrAWin Cov Rs (nFn Rs Ψ s))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov := by
  refine avg_le fun Rs ↦ ?_
  rw [itsrN_eq_B Rs, avg_comm]
  refine (avg_mono fun d ↦ itsrNB_le hmono hx Rs d).trans ?_
  rw [avg_mul_left]
  rfl

/-- **Adaptive ITSR, phase-weighted, square-root form, no collision term.** -/
theorem itsr4_adaptive_weighted_sqrt_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) Wt) :
    itsrAdaptiveExp I ρ s x Cov ^ (2⁻¹ : ℝ) ≤
      ((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ) := by
  unfold itsrAdaptiveExp
  rw [mpExp_eq_N]
  refine (mpg_sqrt_le (fam := fun Rs (Ψ : (K × Xm) × Option (Fin s) → D) m ↦ nFn Rs Ψ m)
    (fun Rs Ψ j r m hm ↦ ?_) (fun Rs Ψ m z h ↦ ?_) hx hW
    (fun Rs Ψ ↦ itsrAWin Cov Rs (nFn Rs Ψ s))).trans
    (add_le_add (sqrt_le_sqrt (itsrN_hyb_le hmono hx)) le_rfl)
  · funext z
    show Ψ (z, lastIdx (Function.update Rs j r) m z.1) = Ψ (z, lastIdx Rs m z.1)
    rw [lastIdx_update Rs j z.1 r hm]
  · refine lastIdx_ne (Rs := Rs) (m := m) (r := z.1) fun heq ↦ h ?_
    show Ψ (z, lastIdx Rs s z.1) = Ψ (z, lastIdx Rs m z.1)
    rw [heq]

/-- **Adaptive ITSR, phase-weighted, no collision term.**  If on every path the sum over the
quantum queries of `s − (number of target requests made before the query)` is at most `Wt`:
`Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov) + √(4 q Wt / |K|))²`. -/
theorem itsr4_adaptive_weighted_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) Wt) :
    itsrAdaptiveExp I ρ s x Cov ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ)) ^ 2 :=
  calc itsrAdaptiveExp I ρ s x Cov = (itsrAdaptiveExp I ρ s x Cov ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' (itsr4_adaptive_weighted_sqrt_le hmono hx hW) 2

/-- **Adaptive ITSR, general regime, no collision term.**
`Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov) + 2 q √(s/|K|))²`. -/
theorem itsr4_adaptive_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ s x Cov ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := itsr4_adaptive_weighted_le (I := I) (ρ := ρ) hmono hx
    (fun Rs ↦ mpComp_isWeightedBound hx Rs)
  have e : 4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * ((s * q : ℕ) : ℝ≥0∞)) =
      4 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ * q) := by
    push_cast
    ring
  rwa [e, sqrt_four_mul] at h

/-- **Adaptive ITSR without reprogramming loss and without collision term**: an adversary all
of whose quantum queries come after its `s`-th target request wins with probability at most
`(2q+1)² · coverProb (Fin s) Cov`. -/
theorem itsr4_adaptive_noloss_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) 0) :
    itsrAdaptiveExp I ρ s x Cov ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov := by
  have h := itsr4_adaptive_weighted_le (I := I) (ρ := ρ) hmono hx hW
  simp only [Nat.cast_zero, mul_zero] at h
  rwa [ENNReal.zero_rpow_of_pos (by norm_num), add_zero, sq_sqrt] at h

end GameN

section Fors

variable {K Xm Ix Lx : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm]
  [DecidableEq Xm] [Fintype Ix] [DecidableEq Ix] [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx]
  [AddCommGroup Lx] {k : ℕ}
  {L : LocalSig.{u, v}} {A : QReg}

/-- **Adaptive ITSR, FORS relation, general regime, no collision term.** -/
theorem itsr4_adaptive_fors_le (I : L.Interp) (ρ : SubState A) (s : ℕ)
    (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin k → Lx))) Xm K (fun _ ↦ K × Xm) s A) (q : ℕ)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ s x (forsCov (I := Ix) (L := Lx) (k := k)) ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (∑ γ ∈ range (s + 1),
            (s.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (s - γ) *
              (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k)) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := itsr4_adaptive_le (I := I) (ρ := ρ)
    (Cov := forsCov (I := Ix) (L := Lx) (k := k)) forsCov_mono hx
  rw [coverProb_fors] at h
  simpa only [Fintype.card_fin] using h

/-- **Adaptive ITSR, FORS relation, phase-weighted, no collision term.** -/
theorem itsr4_adaptive_fors_weighted_le (I : L.Interp) (ρ : SubState A) (s : ℕ)
    (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin k → Lx))) Xm K (fun _ ↦ K × Xm) s A) (q Wt : ℕ)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) Wt) :
    itsrAdaptiveExp I ρ s x (forsCov (I := Ix) (L := Lx) (k := k)) ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (∑ γ ∈ range (s + 1),
            (s.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (s - γ) *
              (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k)) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := itsr4_adaptive_weighted_le (I := I) (ρ := ρ)
    (Cov := forsCov (I := Ix) (L := Lx) (k := k)) forsCov_mono hx hW
  rw [coverProb_fors] at h
  simpa only [Fintype.card_fin] using h

/-- **Adaptive ITSR, FORS relation, no reprogramming loss, no collision term**: all quantum
hash queries after the `s`-th target request. -/
theorem itsr4_adaptive_fors_noloss_le (I : L.Interp) (ρ : SubState A) (s : ℕ)
    (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin k → Lx))) Xm K (fun _ ↦ K × Xm) s A) (q : ℕ)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) 0) :
    itsrAdaptiveExp I ρ s x (forsCov (I := Ix) (L := Lx) (k := k)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        (∑ γ ∈ range (s + 1),
          (s.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
            (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (s - γ) *
            (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k) := by
  have h := itsr4_adaptive_noloss_le (I := I) (ρ := ρ)
    (Cov := forsCov (I := Ix) (L := Lx) (k := k)) forsCov_mono hx hW
  rw [coverProb_fors] at h
  simpa only [Fintype.card_fin] using h

end Fors

end PQ.QROM

#print axioms PQ.QROM.mpg_sqrt_le
#print axioms PQ.QROM.itsrN_eq_B
#print axioms PQ.QROM.itsrNB_le
#print axioms PQ.QROM.itsr4_adaptive_weighted_le
#print axioms PQ.QROM.itsr4_adaptive_le
#print axioms PQ.QROM.itsr4_adaptive_noloss_le
#print axioms PQ.QROM.itsr4_adaptive_fors_le
#print axioms PQ.QROM.itsr4_adaptive_fors_weighted_le
#print axioms PQ.QROM.itsr4_adaptive_fors_noloss_le
