import PQ.QROM.Interface
import Mathlib.Analysis.MeanInequalities

/-!
# Averaging the square-root hybrid bound over a finite world space (engine E2)

* `sqrt_sum_le` (E2a): Minkowski's inequality over a finite weighted world space, in the form
  "a pointwise square-root triangle inequality averages to one".
* `Hidden w view S ε` (E2b): the marked set `S ω` is `ε`-hidden from the view `view ω`.
* `Hidden.sum_le`: a view-measurable family of sub-distributions on `X` puts at most `ε` of its
  mass on the marked set.
* `Hidden.search_le`: a `q`-query algorithm that only sees the view outputs a marked point with
  probability at most `(2q+1)² ε`.
* `Hidden.sqrt_real_le_sqrt_hyb`, `Hidden.sqrt_hyb_le_sqrt_real`, `Hidden.real_le_hyb_add`,
  `Hidden.hyb_le_real_add`: real and hybrid worlds are `2 q √ε`-close in square root, hence
  `4 q √ε`-close.

Everything is a finite sum in `ℝ≥0∞`; the quantum algorithm enters only through
`PQ.QROM.HybridModel`.
-/

open ENNReal Finset

namespace PQ.QROM

/-! ### Square roots in `ℝ≥0∞` -/

theorem sq_sqrt (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem sqrt_sq (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem sqrt_le_sqrt {x y : ℝ≥0∞} (h : x ≤ y) : x ^ (2⁻¹ : ℝ) ≤ y ^ (2⁻¹ : ℝ) :=
  ENNReal.rpow_le_rpow h (by norm_num)

theorem sqrt_mul (x y : ℝ≥0∞) : (x * y) ^ (2⁻¹ : ℝ) = x ^ (2⁻¹ : ℝ) * y ^ (2⁻¹ : ℝ) :=
  ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)

theorem sqrt_le_one {x : ℝ≥0∞} (h : x ≤ 1) : x ^ (2⁻¹ : ℝ) ≤ 1 := by
  simpa using sqrt_le_sqrt h

/-- `√(4 q (ε q)) = 2 q √ε`. -/
theorem sqrt_four_mul (q ε : ℝ≥0∞) :
    (4 * q * (ε * q)) ^ (2⁻¹ : ℝ) = 2 * q * ε ^ (2⁻¹ : ℝ) := by
  have h : 4 * q * (ε * q) = (2 * q * ε ^ (2⁻¹ : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, sq_sqrt]; ring
  rw [h, sqrt_sq]

/-- If `√A ≤ √B + δ` and both are at most one then `A ≤ B + 2 δ`. -/
theorem le_add_two_mul_of_sqrt_le {A B δ : ℝ≥0∞} (hA : A ≤ 1) (hB : B ≤ 1)
    (h : A ^ (2⁻¹ : ℝ) ≤ B ^ (2⁻¹ : ℝ) + δ) : A ≤ B + 2 * δ := by
  have hA' := sqrt_le_one hA
  have hB' := sqrt_le_one hB
  calc A = A ^ (2⁻¹ : ℝ) * A ^ (2⁻¹ : ℝ) := by rw [← sq, sq_sqrt]
    _ ≤ A ^ (2⁻¹ : ℝ) * (B ^ (2⁻¹ : ℝ) + δ) := by gcongr
    _ = A ^ (2⁻¹ : ℝ) * B ^ (2⁻¹ : ℝ) + A ^ (2⁻¹ : ℝ) * δ := mul_add _ _ _
    _ ≤ (B ^ (2⁻¹ : ℝ) + δ) * B ^ (2⁻¹ : ℝ) + 1 * δ := by gcongr
    _ = B ^ (2⁻¹ : ℝ) * B ^ (2⁻¹ : ℝ) + δ * B ^ (2⁻¹ : ℝ) + δ := by rw [add_mul, one_mul]
    _ ≤ B ^ (2⁻¹ : ℝ) * B ^ (2⁻¹ : ℝ) + δ * 1 + δ := by gcongr
    _ = B + 2 * δ := by rw [← sq, sq_sqrt, mul_one, two_mul, add_assoc]

/-! ### E2a: Minkowski over worlds -/

section Minkowski

variable {Ω : Type} [Fintype Ω]

/-- **E2a.** A pointwise square-root triangle inequality averages to one (L² triangle
inequality over a finite weighted world space). -/
theorem sqrt_sum_le (w a b c : Ω → ℝ≥0∞)
    (h : ∀ ω, a ω ^ (2⁻¹ : ℝ) ≤ b ω ^ (2⁻¹ : ℝ) + c ω ^ (2⁻¹ : ℝ)) :
    (∑ ω, w ω * a ω) ^ (2⁻¹ : ℝ) ≤
      (∑ ω, w ω * b ω) ^ (2⁻¹ : ℝ) + (∑ ω, w ω * c ω) ^ (2⁻¹ : ℝ) := by
  have e : ∀ x : ℝ≥0∞, (x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = x := fun x ↦ by
    rw [← ENNReal.rpow_mul]; norm_num
  have key := ENNReal.Lp_add_le (univ : Finset Ω) (fun ω ↦ (w ω * b ω) ^ (2⁻¹ : ℝ))
    (fun ω ↦ (w ω * c ω) ^ (2⁻¹ : ℝ)) (p := 2) (by norm_num)
  simp only [e, one_div] at key
  refine le_trans (sqrt_le_sqrt (Finset.sum_le_sum fun ω _ ↦ ?_)) key
  calc w ω * a ω = ((w ω * a ω) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) := (e _).symm
    _ ≤ _ := ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [sqrt_mul, sqrt_mul, sqrt_mul, ← mul_add]
  gcongr
  exact h ω

end Minkowski

/-! ### E2b: the hidden-set lemma -/

section HiddenSet

variable {Ω V X : Type} [Fintype Ω] [Fintype X] [DecidableEq X]

/-- The marked set `S ω` is `ε`-hidden from the view: for every point `k` and every nonnegative
test function `φ` of the view, the `w`-weight of `φ(view)` on the worlds where `k` is marked is at
most `ε` times its total weight.  (For a probability weight: `Pr[k ∈ S | view] ≤ ε`.) -/
def Hidden (w : Ω → ℝ≥0∞) (view : Ω → V) (S : Ω → Finset X) (ε : ℝ≥0∞) : Prop :=
  ∀ (k : X) (φ : V → ℝ≥0∞),
    ∑ ω, w ω * (if k ∈ S ω then φ (view ω) else 0) ≤ ε * ∑ ω, w ω * φ (view ω)

variable {w : Ω → ℝ≥0∞} {view : Ω → V} {S : Ω → Finset X} {ε : ℝ≥0∞}

/-- **E2b (i).** A view-measurable family `m` of weights on `X` of total mass at most `c` puts
average mass at most `ε c` on the marked set. -/
theorem Hidden.sum_le (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1) (m : V → X → ℝ≥0∞)
    (c : ℝ≥0∞) (hm : ∀ v, ∑ k, m v k ≤ c) :
    ∑ ω, w ω * ∑ k ∈ S ω, m (view ω) k ≤ ε * c := by
  calc ∑ ω, w ω * ∑ k ∈ S ω, m (view ω) k
      = ∑ k, ∑ ω, w ω * (if k ∈ S ω then m (view ω) k else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
    _ ≤ ∑ k, ε * ∑ ω, w ω * m (view ω) k :=
        Finset.sum_le_sum fun k _ ↦ hH k fun v ↦ m v k
    _ = ε * ∑ ω, w ω * ∑ k, m (view ω) k := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ ε * ∑ ω, w ω * c := by
        gcongr with ω _
        exact hm _
    _ ≤ ε * c := by
        rw [← Finset.sum_mul]
        calc ε * ((∑ ω, w ω) * c) ≤ ε * (1 * c) := by gcongr
          _ = ε * c := by rw [one_mul]

variable {Y Leaf : Type} [DecidableEq Y] {q : ℕ}

omit [Fintype Ω] [DecidableEq X] in
/-- Per-world hybrid bound with the differing set enlarged to the marked set. -/
private theorem hybrid_marked (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y)
    (Ghyb : V → X → Y) (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (ω : Ω)
    (E : Leaf → Prop) :
    (M (view ω)).prob (Hreal ω) E ^ (2⁻¹ : ℝ) ≤
        (M (view ω)).prob (Ghyb (view ω)) E ^ (2⁻¹ : ℝ) +
          (4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k) ^ (2⁻¹ : ℝ) ∧
    (M (view ω)).prob (Ghyb (view ω)) E ^ (2⁻¹ : ℝ) ≤
        (M (view ω)).prob (Hreal ω) E ^ (2⁻¹ : ℝ) +
          (4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k) ^ (2⁻¹ : ℝ) := by
  classical
  have hsub : ∑ k ∈ univ.filter (fun k ↦ Hreal ω k ≠ Ghyb (view ω) k),
      (M (view ω)).mass (Ghyb (view ω)) k ≤ ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k :=
    Finset.sum_le_sum_of_subset fun k hk ↦ hS ω k (Finset.mem_filter.1 hk).2
  exact ⟨((M (view ω)).hybrid (Hreal ω) (Ghyb (view ω)) E).trans (by gcongr),
    ((M (view ω)).hybrid' (Hreal ω) (Ghyb (view ω)) E).trans (by gcongr)⟩

/-- The averaged mass term is at most `(2 q √ε)²`. -/
private theorem Hidden.sqrt_mass_le (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Ghyb : V → X → Y) :
    (∑ ω, w ω * (4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k)) ^ (2⁻¹ : ℝ) ≤
      2 * q * ε ^ (2⁻¹ : ℝ) := by
  rw [← sqrt_four_mul]
  refine sqrt_le_sqrt ?_
  have h := hH.sum_le hw (fun v k ↦ (M v).mass (Ghyb v) k) q fun v ↦ (M v).mass_sum_le _
  calc ∑ ω, w ω * (4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k)
      = 4 * q * ∑ ω, w ω * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ ↦ mul_left_comm _ _ _
    _ ≤ 4 * q * (ε * q) := by gcongr

/-- **E2b (ii), search.** Worlds `ω` with weights `w` of total mass at most one; the algorithm
`M (view ω)` (at most `q` queries) depends only on the view, runs against the real function
`Hreal ω`, and wins if its output `out (view ω) p` lies in the marked set `S ω`.  If the real
function agrees with a view-determined function `Ghyb (view ω)` outside the marked set and the
marked set is `ε`-hidden from the view, the winning probability is at most `(2q+1)² ε`. -/
theorem Hidden.search_le (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (out : V → Leaf → X) :
    ∑ ω, w ω * (M (view ω)).prob (Hreal ω) (fun p ↦ out (view ω) p ∈ S ω) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * ε := by
  have h1 := sqrt_sum_le w
    (fun ω ↦ (M (view ω)).prob (Hreal ω) (fun p ↦ out (view ω) p ∈ S ω))
    (fun ω ↦ (M (view ω)).prob (Ghyb (view ω)) (fun p ↦ out (view ω) p ∈ S ω))
    (fun ω ↦ 4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k)
    (fun ω ↦ (hybrid_marked M Hreal Ghyb hS ω _).1)
  have hb : ∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (fun p ↦ out (view ω) p ∈ S ω) ≤ ε :=
    calc ∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (fun p ↦ out (view ω) p ∈ S ω)
        ≤ ∑ ω, w ω * ∑ k ∈ S ω, (M (view ω)).prob (Ghyb (view ω)) (fun p ↦ out (view ω) p = k) := by
          gcongr with ω _
          exact (M _).prob_sub _ _ _
      _ ≤ ε * 1 :=
          hH.sum_le hw (fun v k ↦ (M v).prob (Ghyb v) (fun p ↦ out v p = k)) 1
            fun v ↦ (M v).prob_sum_le _ _
      _ = ε := mul_one _
  have h2 : (∑ ω, w ω * (M (view ω)).prob (Hreal ω) (fun p ↦ out (view ω) p ∈ S ω)) ^ (2⁻¹ : ℝ) ≤
      (2 * (q : ℝ≥0∞) + 1) * ε ^ (2⁻¹ : ℝ) :=
    calc _ ≤ _ := h1
      _ ≤ ε ^ (2⁻¹ : ℝ) + 2 * q * ε ^ (2⁻¹ : ℝ) :=
          add_le_add (sqrt_le_sqrt hb) (hH.sqrt_mass_le hw M Ghyb)
      _ = (2 * (q : ℝ≥0∞) + 1) * ε ^ (2⁻¹ : ℝ) := by ring
  calc ∑ ω, w ω * (M (view ω)).prob (Hreal ω) (fun p ↦ out (view ω) p ∈ S ω)
      = ((∑ ω, w ω * (M (view ω)).prob (Hreal ω) (fun p ↦ out (view ω) p ∈ S ω)) ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ ((2 * (q : ℝ≥0∞) + 1) * ε ^ (2⁻¹ : ℝ)) ^ 2 := by gcongr
    _ = (2 * (q : ℝ≥0∞) + 1) ^ 2 * ε := by rw [mul_pow, sq_sqrt]

/-- **E2b (iii), distinguishing, square-root form.** For an event depending only on the view,
`√P_real ≤ √P_hyb + 2 q √ε`. -/
theorem Hidden.sqrt_real_le_sqrt_hyb (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (E : V → Leaf → Prop) :
    (∑ ω, w ω * (M (view ω)).prob (Hreal ω) (E (view ω))) ^ (2⁻¹ : ℝ) ≤
      (∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (E (view ω))) ^ (2⁻¹ : ℝ) +
        2 * q * ε ^ (2⁻¹ : ℝ) :=
  (sqrt_sum_le w _ _ _ fun ω ↦ (hybrid_marked M Hreal Ghyb hS ω _).1).trans
    (add_le_add le_rfl (hH.sqrt_mass_le hw M Ghyb))

/-- **E2b (iii), distinguishing, square-root form, converse.**
`√P_hyb ≤ √P_real + 2 q √ε`. -/
theorem Hidden.sqrt_hyb_le_sqrt_real (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (E : V → Leaf → Prop) :
    (∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (E (view ω))) ^ (2⁻¹ : ℝ) ≤
      (∑ ω, w ω * (M (view ω)).prob (Hreal ω) (E (view ω))) ^ (2⁻¹ : ℝ) +
        2 * q * ε ^ (2⁻¹ : ℝ) :=
  (sqrt_sum_le w _ _ _ fun ω ↦ (hybrid_marked M Hreal Ghyb hS ω _).2).trans
    (add_le_add le_rfl (hH.sqrt_mass_le hw M Ghyb))

omit [DecidableEq X] in
/-- A weighted average of probabilities is at most one. -/
theorem sum_mul_prob_le_one [Nonempty X] (hw : ∑ ω, w ω ≤ 1) (M : Ω → HybridModel X Y Leaf q)
    (H : Ω → X → Y) (E : Ω → Leaf → Prop) : ∑ ω, w ω * (M ω).prob (H ω) (E ω) ≤ 1 :=
  calc ∑ ω, w ω * (M ω).prob (H ω) (E ω) ≤ ∑ ω, w ω * 1 := by
        gcongr with ω _
        exact (M ω).prob_le_one _ _
    _ ≤ 1 := by simpa using hw

/-- **E2b (iii), distinguishing.** `P_real ≤ P_hyb + 4 q √ε`. -/
theorem Hidden.real_le_hyb_add [Nonempty X] (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (E : V → Leaf → Prop) :
    ∑ ω, w ω * (M (view ω)).prob (Hreal ω) (E (view ω)) ≤
      ∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (E (view ω)) + 4 * q * ε ^ (2⁻¹ : ℝ) := by
  have h := le_add_two_mul_of_sqrt_le
    (sum_mul_prob_le_one hw (fun ω ↦ M (view ω)) Hreal fun ω ↦ E (view ω))
    (sum_mul_prob_le_one hw (fun ω ↦ M (view ω)) (fun ω ↦ Ghyb (view ω)) fun ω ↦ E (view ω))
    (hH.sqrt_real_le_sqrt_hyb hw M Hreal Ghyb hS E)
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **E2b (iii), distinguishing, converse.** `P_hyb ≤ P_real + 4 q √ε`. -/
theorem Hidden.hyb_le_real_add [Nonempty X] (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (E : V → Leaf → Prop) :
    ∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (E (view ω)) ≤
      ∑ ω, w ω * (M (view ω)).prob (Hreal ω) (E (view ω)) + 4 * q * ε ^ (2⁻¹ : ℝ) := by
  have h := le_add_two_mul_of_sqrt_le
    (sum_mul_prob_le_one hw (fun ω ↦ M (view ω)) (fun ω ↦ Ghyb (view ω)) fun ω ↦ E (view ω))
    (sum_mul_prob_le_one hw (fun ω ↦ M (view ω)) Hreal fun ω ↦ E (view ω))
    (hH.sqrt_hyb_le_sqrt_real hw M Hreal Ghyb hS E)
  calc _ ≤ _ := h
    _ = _ := by ring

end HiddenSet

end PQ.QROM

#print axioms PQ.QROM.sqrt_sum_le
#print axioms PQ.QROM.Hidden.sum_le
#print axioms PQ.QROM.Hidden.search_le
#print axioms PQ.QROM.Hidden.sqrt_real_le_sqrt_hyb
#print axioms PQ.QROM.Hidden.sqrt_hyb_le_sqrt_real
#print axioms PQ.QROM.Hidden.real_le_hyb_add
#print axioms PQ.QROM.Hidden.hyb_le_real_add
