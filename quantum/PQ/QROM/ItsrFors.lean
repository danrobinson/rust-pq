import PQ.QROM.Itsr
import PQ.QROM.Hybrid

/-!
# The covering probability for the FORS index structure

Digests `D = I × (Fin k → L)`: a hypertree-leaf (FORS instance) index in `I` (`|I| = 2^h` for
SLH-DSA) and `k` FORS leaf indices in `L` (`|L| = t`).  A digest `u` is covered by a set `S` of
digests iff each of its `k` indices is selected by some digest of `S` in the same instance:
`forsCov S u := ∀ j, ∃ d ∈ S, d.1 = u.1 ∧ d.2 j = u.2 j`.

* `forsCount`: the number of `s`-tuples of digests (`s = |ι|`) that cover a given digest is
  `∑_γ C(s,γ) (|I|−1)^(s−γ) (t^s − (t−1)^γ t^(s−γ))^k` (independent of the digest): `γ` of the
  tuple entries fall in the instance of the digest, and each of the `k` columns of those `γ`
  entries must hit the corresponding index.
* `coverProb_fors_count`: `coverProb ι forsCov = forsCoverCount / |D|^s` (exact).
* `coverProb_fors`: the SPHINCS+ expression
  `coverProb ι forsCov = ∑_γ C(s,γ) (1/|I|)^γ (1 − 1/|I|)^(s−γ) (1 − (1 − 1/t)^γ)^k` (exact).
* `itsr_fors_le`, `itsr_fors_program_le`: `itsr_nonadaptive_le'` with this expression.
-/

open ENNReal Finset

universe u v w

namespace PQ.QROM

section Fors

variable {I L ι : Type} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] [Fintype ι]
  [DecidableEq ι] {k : ℕ}

/-- The FORS cover relation. -/
def forsCov (S : Finset (I × (Fin k → L))) (u : I × (Fin k → L)) : Prop :=
  ∀ j, ∃ d ∈ S, d.1 = u.1 ∧ d.2 j = u.2 j

instance forsCov.decidablePred (S : Finset (I × (Fin k → L))) : DecidablePred (forsCov S) :=
  fun u ↦ by unfold forsCov; infer_instance

/-- Columns (one FORS tree, all `s` tuple entries) in which some entry of `G` hits the index
`b`. -/
theorem colCount (G : Finset ι) (b : L) :
    #(univ.filter fun col : ι → L ↦ ∃ i ∈ G, col i = b) =
      Fintype.card L ^ Fintype.card ι -
        (Fintype.card L - 1) ^ #G * Fintype.card L ^ (Fintype.card ι - #G) := by
  have hcompl : (univ.filter fun col : ι → L ↦ ¬ ∃ i ∈ G, col i = b) =
      Fintype.piFinset (fun i ↦ if i ∈ G then univ.erase b else univ) := by
    ext col
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, not_exists,
      not_and]
    constructor
    · intro h i
      by_cases hi : i ∈ G
      · simp [hi, h i hi]
      · simp [hi]
    · intro h i hi
      have := h i
      simpa [hi] using this
  have hc : #(univ.filter fun col : ι → L ↦ ¬ ∃ i ∈ G, col i = b) =
      (Fintype.card L - 1) ^ #G * Fintype.card L ^ (Fintype.card ι - #G) := by
    rw [hcompl, Fintype.card_piFinset, ← Finset.prod_mul_prod_compl G]
    have a1 : ∀ i ∈ G, #(if i ∈ G then univ.erase b else (univ : Finset L)) =
        Fintype.card L - 1 := by
      intro i hi
      simp [hi, Finset.card_erase_of_mem]
    have a2 : ∀ i ∈ Gᶜ, #(if i ∈ G then univ.erase b else (univ : Finset L)) =
        Fintype.card L := by
      intro i hi
      simp [Finset.mem_compl.1 hi]
    rw [Finset.prod_congr rfl a1, Finset.prod_congr rfl a2, Finset.prod_const, Finset.prod_const,
      Finset.card_compl]
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ι → L)))
    (fun col : ι → L ↦ ∃ i ∈ G, col i = b)
  rw [hc, Finset.card_univ, Fintype.card_fun] at htot
  exact Nat.eq_sub_of_add_eq htot

/-- Instance assignments of the `s` tuple entries with exactly the entries of `G` in the instance
`a`. -/
theorem rowCount (G : Finset ι) (a : I) :
    #(univ.filter fun α : ι → I ↦ ∀ i, (α i = a ↔ i ∈ G)) =
      (Fintype.card I - 1) ^ (Fintype.card ι - #G) := by
  have hset : (univ.filter fun α : ι → I ↦ ∀ i, (α i = a ↔ i ∈ G)) =
      Fintype.piFinset (fun i ↦ if i ∈ G then {a} else univ.erase a) := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun i ↦ ?_
    by_cases hi : i ∈ G <;> simp [hi]
  rw [hset, Fintype.card_piFinset, ← Finset.prod_mul_prod_compl G]
  have a1 : ∀ i ∈ G, #(if i ∈ G then ({a} : Finset I) else univ.erase a) = 1 := by
    intro i hi
    simp [hi]
  have a2 : ∀ i ∈ Gᶜ, #(if i ∈ G then ({a} : Finset I) else univ.erase a) =
      Fintype.card I - 1 := by
    intro i hi
    simp [Finset.mem_compl.1 hi, Finset.card_erase_of_mem]
  rw [Finset.prod_congr rfl a1, Finset.prod_congr rfl a2, Finset.prod_const, Finset.prod_const,
    Finset.card_compl, one_pow, one_mul]

/-- The number of `s`-tuples of digests covering a fixed digest, for `|I| = nI`, `|L| = nt`. -/
def forsCoverCount (nI nt k s : ℕ) : ℕ :=
  ∑ γ ∈ range (s + 1), s.choose γ *
    ((nI - 1) ^ (s - γ) * (nt ^ s - (nt - 1) ^ γ * nt ^ (s - γ)) ^ k)

/-- The splitting of a tuple of digests into instance indices and columns. -/
def forsSplit : (ι → I × (Fin k → L)) ≃ (ι → I) × (Fin k → ι → L) where
  toFun d := (fun i ↦ (d i).1, fun j i ↦ (d i).2 j)
  invFun p := fun i ↦ (p.1 i, fun j ↦ p.2 j i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Counting covering tuples.** -/
theorem forsCount (a : I) (v : Fin k → L) :
    #(univ.filter fun d : ι → I × (Fin k → L) ↦ ∀ j, ∃ i, (d i).1 = a ∧ (d i).2 j = v j) =
      forsCoverCount (Fintype.card I) (Fintype.card L) k (Fintype.card ι) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun d : ι → I × (Fin k → L) ↦
    univ.filter fun i ↦ (d i).1 = a) (t := univ) (fun _ _ ↦ Finset.mem_univ _)]
  have hG : ∀ G : Finset ι,
      #((univ.filter fun d : ι → I × (Fin k → L) ↦
          ∀ j, ∃ i, (d i).1 = a ∧ (d i).2 j = v j).filter
        fun d ↦ (univ.filter fun i ↦ (d i).1 = a) = G) =
      (Fintype.card I - 1) ^ (Fintype.card ι - #G) *
        (Fintype.card L ^ Fintype.card ι -
          (Fintype.card L - 1) ^ #G * Fintype.card L ^ (Fintype.card ι - #G)) ^ k := by
    intro G
    rw [Finset.card_equiv (forsSplit (I := I) (L := L) (ι := ι) (k := k))
      (t := (univ.filter fun α : ι → I ↦ ∀ i, (α i = a ↔ i ∈ G)) ×ˢ
        Fintype.piFinset (fun j : Fin k ↦ univ.filter fun col : ι → L ↦ ∃ i ∈ G, col i = v j))]
    · rw [Finset.card_product, rowCount, Fintype.card_piFinset]
      simp only [colCount, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · intro d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Fintype.mem_piFinset, forsSplit, Equiv.coe_fn_mk]
      have hext : (univ.filter fun i ↦ (d i).1 = a) = G ↔ ∀ i, ((d i).1 = a ↔ i ∈ G) := by
        rw [Finset.ext_iff]
        simp
      rw [hext]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2, fun j ↦ ?_⟩
        obtain ⟨i, hi, hv⟩ := h1 j
        exact ⟨i, (h2 i).1 hi, hv⟩
      · rintro ⟨h2, h1⟩
        refine ⟨fun j ↦ ?_, h2⟩
        obtain ⟨i, hi, hv⟩ := h1 j
        exact ⟨i, (h2 i).2 hi, hv⟩
  rw [Finset.sum_congr rfl fun G _ ↦ hG G, ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun γ ↦ (Fintype.card I - 1) ^ (Fintype.card ι - γ) *
      (Fintype.card L ^ Fintype.card ι -
        (Fintype.card L - 1) ^ γ * Fintype.card L ^ (Fintype.card ι - γ)) ^ k)]
  simp only [Finset.card_univ, smul_eq_mul, forsCoverCount]

/-- **The FORS covering probability, counting form.** -/
theorem coverProb_fors_count [Nonempty I] [Nonempty L] :
    coverProb ι (forsCov (I := I) (L := L) (k := k)) =
      (forsCoverCount (Fintype.card I) (Fintype.card L) k (Fintype.card ι) : ℝ≥0∞) /
        (Fintype.card (ι → I × (Fin k → L)) : ℝ≥0∞) := by
  have hcnt : ∑ d : ι → I × (Fin k → L), #(covered forsCov (univ.image d)) =
      Fintype.card (I × (Fin k → L)) *
        forsCoverCount (Fintype.card I) (Fintype.card L) k (Fintype.card ι) := by
    simp only [covered, Finset.card_filter]
    rw [Finset.sum_comm]
    have : ∀ u : I × (Fin k → L), ∑ d : ι → I × (Fin k → L),
        (if forsCov (univ.image d) u then 1 else 0) =
        forsCoverCount (Fintype.card I) (Fintype.card L) k (Fintype.card ι) := by
      intro u
      rw [← Finset.card_filter, ← forsCount (ι := ι) u.1 u.2]
      congr 1
      refine Finset.filter_congr fun d _ ↦ ?_
      simp [forsCov]
    simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  unfold coverProb
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hcast : ∑ d : ι → I × (Fin k → L), (#(covered forsCov (univ.image d)) : ℝ≥0∞) =
      ((Fintype.card (I × (Fin k → L)) *
        forsCoverCount (Fintype.card I) (Fintype.card L) k (Fintype.card ι) : ℕ) : ℝ≥0∞) := by
    rw [← hcnt]; push_cast; rfl
  rw [hcast, Nat.cast_mul, div_eq_mul_inv]
  have iD := natCast_mul_inv_cancel (Fintype.card_ne_zero (α := I × (Fin k → L)))
  calc (Fintype.card (ι → I × (Fin k → L)) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (I × (Fin k → L)) : ℝ≥0∞) *
          (forsCoverCount (Fintype.card I) (Fintype.card L) k (Fintype.card ι) : ℝ≥0∞) *
          (Fintype.card (I × (Fin k → L)) : ℝ≥0∞)⁻¹)
      = ((Fintype.card (I × (Fin k → L)) : ℝ≥0∞) *
          (Fintype.card (I × (Fin k → L)) : ℝ≥0∞)⁻¹) *
          ((forsCoverCount (Fintype.card I) (Fintype.card L) k (Fintype.card ι) : ℝ≥0∞) *
            (Fintype.card (ι → I × (Fin k → L)) : ℝ≥0∞)⁻¹) := by ring
    _ = _ := by rw [iD, one_mul]

/-- `1 - 1/n = (n - 1)/n`. -/
theorem one_sub_natCast_inv (n : ℕ) (hn : n ≠ 0) :
    (1 : ℝ≥0∞) - (n : ℝ≥0∞)⁻¹ = ((n : ℝ≥0∞) - 1) * (n : ℝ≥0∞)⁻¹ := by
  have hx0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  have hinvtop : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hx0
  rw [ENNReal.sub_mul (fun _ _ ↦ hinvtop), one_mul,
    ENNReal.mul_inv_cancel hx0 (ENNReal.natCast_ne_top n)]

/-- One term of the count, normalised, is one term of the SPHINCS+ expression. -/
theorem fors_term (a t k s γ : ℕ) (ha : a ≠ 0) (ht : t ≠ 0) (hγ : γ ≤ s) :
    (((a - 1) ^ (s - γ) * (t ^ s - (t - 1) ^ γ * t ^ (s - γ)) ^ k : ℕ) : ℝ≥0∞) /
        ((a : ℝ≥0∞) * (t : ℝ≥0∞) ^ k) ^ s =
      ((a : ℝ≥0∞)⁻¹) ^ γ * (1 - (a : ℝ≥0∞)⁻¹) ^ (s - γ) *
        (1 - (1 - (t : ℝ≥0∞)⁻¹) ^ γ) ^ k := by
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have ht0 : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht
  have hatop : (a : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top a
  have httop : (t : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top t
  have iT : (t : ℝ≥0∞) * (t : ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel ht0 httop
  have hTtop : ((t : ℝ≥0∞)⁻¹) ^ s ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 ht0)
  have hinv : (((a : ℝ≥0∞) * (t : ℝ≥0∞) ^ k) ^ s)⁻¹ =
      ((a : ℝ≥0∞)⁻¹) ^ s * (((t : ℝ≥0∞)⁻¹) ^ s) ^ k := by
    rw [ENNReal.inv_pow, ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop), ENNReal.inv_pow]
    ring
  have hsplit : ∀ x : ℝ≥0∞, x ^ s = x ^ γ * x ^ (s - γ) := by
    intro x
    rw [← pow_add, Nat.add_sub_cancel' hγ]
  have F2 : ((t : ℝ≥0∞) ^ s - ((t : ℝ≥0∞) - 1) ^ γ * (t : ℝ≥0∞) ^ (s - γ)) *
      ((t : ℝ≥0∞)⁻¹) ^ s = 1 - (1 - (t : ℝ≥0∞)⁻¹) ^ γ := by
    rw [ENNReal.sub_mul (fun _ _ ↦ hTtop)]
    have e1 : (t : ℝ≥0∞) ^ s * ((t : ℝ≥0∞)⁻¹) ^ s = 1 := by rw [← mul_pow, iT, one_pow]
    have e2 : ((t : ℝ≥0∞) - 1) ^ γ * (t : ℝ≥0∞) ^ (s - γ) * ((t : ℝ≥0∞)⁻¹) ^ s =
        (1 - (t : ℝ≥0∞)⁻¹) ^ γ := by
      rw [hsplit ((t : ℝ≥0∞)⁻¹), one_sub_natCast_inv t ht]
      calc ((t : ℝ≥0∞) - 1) ^ γ * (t : ℝ≥0∞) ^ (s - γ) *
            (((t : ℝ≥0∞)⁻¹) ^ γ * ((t : ℝ≥0∞)⁻¹) ^ (s - γ))
          = (((t : ℝ≥0∞) - 1) * (t : ℝ≥0∞)⁻¹) ^ γ *
              ((t : ℝ≥0∞) * (t : ℝ≥0∞)⁻¹) ^ (s - γ) := by ring
        _ = _ := by rw [iT, one_pow, mul_one]
    rw [e1, e2]
  rw [div_eq_mul_inv, hinv]
  simp only [Nat.cast_mul, Nat.cast_pow, ENNReal.natCast_sub, Nat.cast_one]
  rw [← F2, one_sub_natCast_inv a ha, hsplit ((a : ℝ≥0∞)⁻¹)]
  ring

/-- **The FORS covering probability (SPHINCS+ expression).**  With `s = |ι|` target digests,
`|I|` FORS instances and `k` trees of `|L| = t` leaves, the probability that a fresh uniform
digest is covered by `s` independent uniform digests is exactly
`∑_γ C(s,γ) (1/|I|)^γ (1 − 1/|I|)^(s−γ) (1 − (1 − 1/t)^γ)^k`. -/
theorem coverProb_fors [Nonempty I] [Nonempty L] :
    coverProb ι (forsCov (I := I) (L := L) (k := k)) =
      ∑ γ ∈ range (Fintype.card ι + 1),
        ((Fintype.card ι).choose γ : ℝ≥0∞) * ((Fintype.card I : ℝ≥0∞)⁻¹) ^ γ *
          (1 - (Fintype.card I : ℝ≥0∞)⁻¹) ^ (Fintype.card ι - γ) *
          (1 - (1 - (Fintype.card L : ℝ≥0∞)⁻¹) ^ γ) ^ k := by
  have hcard : (Fintype.card (ι → I × (Fin k → L)) : ℝ≥0∞) =
      ((Fintype.card I : ℝ≥0∞) * (Fintype.card L : ℝ≥0∞) ^ k) ^ Fintype.card ι := by
    simp
  rw [coverProb_fors_count, hcard]
  unfold forsCoverCount
  rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  rw [Nat.cast_mul, mul_assoc, ← div_eq_mul_inv,
    fors_term _ _ _ _ _ Fintype.card_ne_zero Fintype.card_ne_zero
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hγ))]
  ring

variable {K Xm : Type} [Fintype K] [DecidableEq K] [Fintype Xm] [DecidableEq Xm]
variable {Leaf : Type} {q : ℕ}

/-- **Non-adaptive ITSR for a random `H_msg` with the FORS index structure (HybridModel level).**
`itsr_nonadaptive_le'` with the covering probability evaluated: the winning probability is at
most `(2q+1)² (∑_γ C(s,γ) (1/|I|)^γ (1 − 1/|I|)^(s−γ) (1 − (1 − 1/t)^γ)^k + s²/|K|)`. -/
theorem itsr_fors_le [Nonempty I] [Nonempty L] (xs : ι → Xm)
    (M : (ι → K) → HybridModel (K × Xm) (I × (Fin k → L)) Leaf q)
    (out : (ι → K) → Leaf → K × Xm) :
    ∑ H : K × Xm → I × (Fin k → L), ∑ Rs : ι → K,
        ((Fintype.card (K × Xm → I × (Fin k → L)) : ℝ≥0∞)⁻¹ *
            (Fintype.card (ι → K) : ℝ≥0∞)⁻¹) *
          (M Rs).prob H (fun l ↦ out Rs l ∉ itsrTargets xs Rs ∧
            forsCov (itsrDigests xs Rs H) (H (out Rs l))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        (∑ γ ∈ range (Fintype.card ι + 1),
            ((Fintype.card ι).choose γ : ℝ≥0∞) * ((Fintype.card I : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card I : ℝ≥0∞)⁻¹) ^ (Fintype.card ι - γ) *
              (1 - (1 - (Fintype.card L : ℝ≥0∞)⁻¹) ^ γ) ^ k +
          (Fintype.card ι : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) := by
  have h := itsr_nonadaptive_le' (forsCov (I := I) (L := L) (k := k)) xs M out
  rwa [coverProb_fors] at h

end Fors

section Programs

open Quantum

variable {I L ι K Xm : Type} [Fintype I] [DecidableEq I] [AddCommGroup I] [Fintype L]
  [DecidableEq L] [AddCommGroup L] [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
  [Fintype Xm] [DecidableEq Xm] {k : ℕ}
variable {Ls : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Non-adaptive ITSR for a random `H_msg` with the FORS index structure, for quantum query
programs.** -/
theorem itsr_fors_program_le (xs : ι → Xm) (Ip : Ls.Interp)
    (x : (ι → K) → QuantumComp Ls (qromSpec (K × Xm) (I × (Fin k → L))) W A)
    (ρ : (ι → K) → SubState A) (q : ℕ) (hx : ∀ Rs, QueryBounded (x Rs) q)
    (out : (ι → K) → (Σ u, W u) → K × Xm) :
    ∑ H : K × Xm → I × (Fin k → L), ∑ Rs : ι → K,
        ((Fintype.card (K × Xm → I × (Fin k → L)) : ℝ≥0∞)⁻¹ *
            (Fintype.card (ι → K) : ℝ≥0∞)⁻¹) *
          qprob Ip H (x Rs) (ρ Rs) (fun p ↦ out Rs p ∉ itsrTargets xs Rs ∧
            forsCov (itsrDigests xs Rs H) (H (out Rs p))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        (∑ γ ∈ range (Fintype.card ι + 1),
            ((Fintype.card ι).choose γ : ℝ≥0∞) * ((Fintype.card I : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card I : ℝ≥0∞)⁻¹) ^ (Fintype.card ι - γ) *
              (1 - (1 - (Fintype.card L : ℝ≥0∞)⁻¹) ^ γ) ^ k +
          (Fintype.card ι : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) :=
  itsr_fors_le xs
    (fun Rs ↦ HybridModel.ofProgram Ip (x Rs) (ρ Rs) q (hx Rs) (out Rs)) (fun _ ↦ id)

end Programs

end PQ.QROM

#print axioms PQ.QROM.forsCount
#print axioms PQ.QROM.coverProb_fors_count
#print axioms PQ.QROM.coverProb_fors
#print axioms PQ.QROM.itsr_fors_le
#print axioms PQ.QROM.itsr_fors_program_le
