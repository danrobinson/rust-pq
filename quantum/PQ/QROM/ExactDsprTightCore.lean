import PQ.QROM.ExactDsprTightEngine

/-!
# A target-count-free second-order bound for decisional games over independent rows

The abstract core of the tight multi-target DSPR bound, proved directly for VCVio programs in
the second-port model (`twoRuntime (ports F H)`, unnormalised input; no separate circuit-level
file: circuits are programs).

## Setting

* **Independent point marks.** A world is a mark pattern `s : X → Bool`; point `k` is marked
  with probability `p k ≤ r²`, independently (`bw p s`).  The function of a world is
  `Hw G h s`: the value `h k` at marked points, `G k` elsewhere.
* **Rows.** `row : X → J` partitions the points; `rowClean row j s`: the row `j` carries no
  mark; `gam p row j` its probability; `clean row j s`: the pattern with the row `j` cleaned.
* **Outputs.** Pairwise disjoint leaf events `Ev j` ("the output names the row `j`").

## Result

`rows_adv_le`: for every program `x` with `x.IsQueryBound bud`, every positive semidefinite `σ`
and every `g ≥ 0` with `2 γ_j − 1 ≤ g` for all rows,

`∑_s w_s ∑_j (±1)·Pr_s[Ev j] ≤ (g + 168 (bud true)² r²) · tr σ`,

sign `+` iff the row `j` is clean in `s` — independently of the number of rows.  (This is
"success minus baseline" of a decisional second-preimage game: the row named by the output is
clean / not clean.)  Constant `C = 168`; `r² = ε` is the per-point mark probability.

## Proof

`sum_bw_rowClean` (independence) reduces the claim to `Lam`, the difference between the run with
the row of the output index cleaned and the real run, summed over the output index.  `Lam_le`
bounds `|Lam|` by induction over the program, for families `ψ s` (real), `φ s j` (row `j`
cleaned, not depending on the row `j` of `s`), with the three scalars

`m² ≥ ∑_s w_s ‖ψ s‖²`, `x² ≥ ∑_s w_s ∑_j ‖ψ s − φ s j‖²`,
`e² ≥ ∑_s w_s ∑_j ‖etaT (ψ − φ) s j‖²` (`etaT`: mean over a resampled row `j`),

and the potential `Pot r n m x e`: the leaf form `2 (m + x) e + x²` composed with `n` oracle
steps `x ↦ x + 3 r (m + x)`, `e ↦ e + 3 r² (m + x) + 2 r x` (`rows_query_step`; this is the
Gronwall-type step, linear with factor `1 + 3 r`).  `Pot` is subadditive under Kraus splittings
(`Pot_sum_le`) and `Pot r q m 0 0 ≤ 84 q² r² m²` when `6 r q ≤ 1` (`Pot_le`); otherwise the
claim is trivial.  The row masses `∑_j ∑_{k ∈ row j} ‖P_k φ_{s,j}‖²` of the cleaned vectors are
controlled by the real vector and the deviations (`row_mass_le`), which is what makes the bound
independent of the number of rows.

## Literature (not verified against the papers here)

A single-target quantum bound for DSPR of random functions is in the literature
(Bernstein–Hülsing, ePrint 2019/492).  Whether a target-count-free bound for the multi-target
tweaked setting is established there or elsewhere is unverified; no novelty is claimed.
-/

open Quantum Matrix Finset MeasureTheory ENNReal
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM.Rows

open PQ.QROM.Tight PQ.QROM.Purify

/-! ## Independent point marks -/

section Bernoulli

variable {X : Type} [Fintype X] [DecidableEq X] (p : X → ℝ)

/-- The product Bernoulli weight of a mark pattern: point `k` is marked with probability `p k`. -/
def bw (s : X → Bool) : ℝ := ∏ k, if s k then p k else 1 - p k

theorem bw_nonneg (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (s : X → Bool) : 0 ≤ bw p s :=
  Finset.prod_nonneg fun k _ ↦ by
    split_ifs
    · exact hp0 k
    · linarith [hp1 k]

theorem sum_prod_bool (g : X → Bool → ℝ) :
    ∑ s : X → Bool, ∏ k, g k (s k) = ∏ k, (g k true + g k false) := by
  have h := Finset.prod_univ_sum (fun _ : X ↦ (Finset.univ : Finset Bool)) g
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  exact Finset.prod_congr rfl fun k _ ↦ by simp

theorem sum_bw : ∑ s, bw p s = 1 := by
  unfold bw
  rw [sum_prod_bool fun k b ↦ if b then p k else 1 - p k]
  simp

/-- The marginal: point `k` is marked with probability `p k`. -/
theorem sum_bw_mark (k : X) : ∑ s, bw p s * (if s k then (1 : ℝ) else 0) = p k := by
  have e : ∀ s : X → Bool, bw p s * (if s k then (1 : ℝ) else 0) =
      ∏ i, (if s i then p i else 1 - p i) * (if i = k then (if s i then (1 : ℝ) else 0) else 1) := by
    intro s
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k]
    simp [bw]
  simp only [e]
  rw [sum_prod_bool fun i b ↦ (if b then p i else 1 - p i) *
    (if i = k then (if b then (1 : ℝ) else 0) else 1)]
  calc _ = ∏ i, (if i = k then p k else 1) :=
        Finset.prod_congr rfl fun i _ ↦ by by_cases h : i = k <;> simp [h]
    _ = p k := by
        rw [Finset.prod_ite_eq' Finset.univ k]
        simp

variable {J : Type} [DecidableEq J] (row : X → J)

/-- The pattern with the row `j` taken from `s'` and everything else from `s`. -/
def mix (j : J) (s s' : X → Bool) : X → Bool := fun k ↦ if row k = j then s' k else s k

/-- The pattern with the row `j` unmarked. -/
def clean (j : J) (s : X → Bool) : X → Bool := fun k ↦ if row k = j then false else s k

theorem clean_mix (j : J) (s s' : X → Bool) : clean row j (mix row j s s') = clean row j s := by
  funext k
  by_cases h : row k = j <;> simp [clean, mix, h]

theorem clean_clean (j : J) (s : X → Bool) : clean row j (clean row j s) = clean row j s := by
  funext k
  by_cases h : row k = j <;> simp [clean, h]

theorem mix_of_row {j : J} {k : X} (h : row k = j) (s s' : X → Bool) :
    mix row j s s' k = s' k := by simp [mix, h]

theorem bw_mix_mul (j : J) (s s' : X → Bool) :
    bw p (mix row j s s') * bw p (mix row j s' s) = bw p s * bw p s' := by
  unfold bw
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  by_cases h : row k = j
  · simp only [mix, h, ite_true]
    exact mul_comm _ _
  · simp only [mix, h, ite_false]

/-- **Resampling a row.** Replacing the row `j` of a random pattern by the row of an independent
pattern does not change the distribution. -/
theorem sum_bw_mix (j : J) (g : (X → Bool) → ℝ) :
    ∑ s, bw p s * ∑ s', bw p s' * g (mix row j s s') = ∑ s, bw p s * g s := by
  let sw : (X → Bool) × (X → Bool) → (X → Bool) × (X → Bool) :=
    fun v ↦ (mix row j v.1 v.2, mix row j v.2 v.1)
  have hsw : Function.Involutive sw := by
    rintro ⟨s, s'⟩
    refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_) <;>
      by_cases h : row k = j <;> simp [sw, mix, h]
  have h := Equiv.sum_comp hsw.toPerm (fun v : (X → Bool) × (X → Bool) ↦ bw p v.1 * bw p v.2 * g v.1)
  simp only [Function.Involutive.coe_toPerm] at h
  calc ∑ s, bw p s * ∑ s', bw p s' * g (mix row j s s')
      = ∑ v : (X → Bool) × (X → Bool), bw p (sw v).1 * bw p (sw v).2 * g (sw v).1 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ ↦ ?_
        change _ = bw p (mix row j s s') * bw p (mix row j s' s) * g (mix row j s s')
        rw [bw_mix_mul]
        ring
    _ = ∑ v : (X → Bool) × (X → Bool), bw p v.1 * bw p v.2 * g v.1 := h
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        change ∑ y, bw p s * bw p y * g s = _
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_bw, mul_one]

end Bernoulli

/-! ## The potential -/

/-- The potential of the induction: the leaf form `2 (m + x) e + x²` composed with `n` oracle
steps `x ↦ x + 3 r (m + x)`, `e ↦ e + 3 r² (m + x) + 2 r x`. -/
def Pot (r : ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, m, x, e => 2 * (m + x) * e + x ^ 2
  | n + 1, m, x, e => Pot r n m (x + 3 * r * (m + x)) (e + 3 * r ^ 2 * (m + x) + 2 * r * x)

theorem Pot_mono {r : ℝ} (hr : 0 ≤ r) (n : ℕ) {m x e m' x' e' : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x)
    (he : 0 ≤ e) (hmm : m ≤ m') (hxx : x ≤ x') (hee : e ≤ e') :
    Pot r n m x e ≤ Pot r n m' x' e' := by
  induction n generalizing m x e m' x' e' with
  | zero =>
    simp only [Pot]
    have h1 : (m + x) * e ≤ (m' + x') * e' :=
      mul_le_mul (by linarith) hee he (by linarith)
    have h2 : x ^ 2 ≤ x' ^ 2 := pow_le_pow_left₀ hx hxx 2
    linarith
  | succ n ih =>
    simp only [Pot]
    have h3 : 0 ≤ 3 * r := by positivity
    have h4 : 0 ≤ 3 * r ^ 2 := by positivity
    have h5 : 0 ≤ 2 * r := by positivity
    refine ih hm (by positivity) (by positivity) hmm ?_ ?_
    · nlinarith [mul_le_mul_of_nonneg_left (add_le_add hmm hxx) h3]
    · nlinarith [mul_le_mul_of_nonneg_left (add_le_add hmm hxx) h4,
        mul_le_mul_of_nonneg_left hxx h5]

theorem Pot_zero_le {r : ℝ} (hr : 0 ≤ r) (n : ℕ) {m x e : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x)
    (he : 0 ≤ e) : Pot r 0 m x e ≤ Pot r n m x e := by
  induction n generalizing x e with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [Pot]
    have h3 : 0 ≤ 3 * r * (m + x) := by positivity
    have h4 : 0 ≤ 3 * r ^ 2 * (m + x) + 2 * r * x := by positivity
    exact (Pot_mono hr 0 hm hx he le_rfl (by linarith) (by linarith)).trans
      (ih (by positivity) (by positivity))

/-- `ℓ²` triangle inequality for a nonnegative combination of three families. -/
theorem sum_lin_sq_le {ι : Type*} (t : Finset ι) (a b c : ι → ℝ) {A B C α β γ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (ha : ∑ i ∈ t, a i ^ 2 ≤ A ^ 2) (hb : ∑ i ∈ t, b i ^ 2 ≤ B ^ 2)
    (hc : ∑ i ∈ t, c i ^ 2 ≤ C ^ 2) :
    ∑ i ∈ t, (α * a i + β * b i + γ * c i) ^ 2 ≤ (α * A + β * B + γ * C) ^ 2 := by
  have hab := sum_mul_le_of_sq t a b hA hB ha hb
  have hac := sum_mul_le_of_sq t a c hA hC ha hc
  have hbc := sum_mul_le_of_sq t b c hB hC hb hc
  have e : ∑ i ∈ t, (α * a i + β * b i + γ * c i) ^ 2 =
      α ^ 2 * ∑ i ∈ t, a i ^ 2 + β ^ 2 * ∑ i ∈ t, b i ^ 2 + γ ^ 2 * ∑ i ∈ t, c i ^ 2 +
        2 * α * β * ∑ i ∈ t, a i * b i + 2 * α * γ * ∑ i ∈ t, a i * c i +
        2 * β * γ * ∑ i ∈ t, b i * c i := by
    simp only [Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left ha (sq_nonneg α)
  have h2 := mul_le_mul_of_nonneg_left hb (sq_nonneg β)
  have h3 := mul_le_mul_of_nonneg_left hc (sq_nonneg γ)
  have h4 := mul_le_mul_of_nonneg_left hab (by positivity : (0 : ℝ) ≤ 2 * α * β)
  have h5 := mul_le_mul_of_nonneg_left hac (by positivity : (0 : ℝ) ≤ 2 * α * γ)
  have h6 := mul_le_mul_of_nonneg_left hbc (by positivity : (0 : ℝ) ≤ 2 * β * γ)
  nlinarith

/-- **The potential is subadditive under splittings** (Cauchy–Schwarz). -/
theorem Pot_sum_le {ι : Type*} {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (t : Finset ι) (mi xi ei : ι → ℝ)
    (hmi0 : ∀ i, 0 ≤ mi i) (hxi0 : ∀ i, 0 ≤ xi i) (hei0 : ∀ i, 0 ≤ ei i) {m x e : ℝ}
    (hm : 0 ≤ m) (hx : 0 ≤ x) (he : 0 ≤ e) (hmi : ∑ i ∈ t, mi i ^ 2 ≤ m ^ 2)
    (hxi : ∑ i ∈ t, xi i ^ 2 ≤ x ^ 2) (hei : ∑ i ∈ t, ei i ^ 2 ≤ e ^ 2) :
    ∑ i ∈ t, Pot r n (mi i) (xi i) (ei i) ≤ Pot r n m x e := by
  induction n generalizing mi xi ei m x e with
  | zero =>
    simp only [Pot]
    have h1 := sum_mul_le_of_sq t mi ei hm he hmi hei
    have h2 := sum_mul_le_of_sq t xi ei hx he hxi hei
    have e1 : ∑ i ∈ t, (2 * (mi i + xi i) * ei i + xi i ^ 2) =
        2 * ∑ i ∈ t, mi i * ei i + 2 * ∑ i ∈ t, xi i * ei i + ∑ i ∈ t, xi i ^ 2 := by
      simp only [Finset.mul_sum]
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [e1]
    nlinarith
  | succ n ih =>
    simp only [Pot]
    have h3 : 0 ≤ 3 * r := by positivity
    have h4 : 0 ≤ 3 * r ^ 2 := by positivity
    have h5 : 0 ≤ 2 * r := by positivity
    refine ih mi (fun i ↦ xi i + 3 * r * (mi i + xi i))
      (fun i ↦ ei i + 3 * r ^ 2 * (mi i + xi i) + 2 * r * xi i) hmi0
      (fun i ↦ by have := hmi0 i; have := hxi0 i; positivity)
      (fun i ↦ by have := hmi0 i; have := hxi0 i; have := hei0 i; positivity)
      hm (by positivity) (by positivity) hmi ?_ ?_
    · have h := sum_lin_sq_le t xi mi (fun _ ↦ 0) hx hm le_rfl
        (by positivity : (0 : ℝ) ≤ 1 + 3 * r) h3 le_rfl hxi hmi (by simp)
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_)) (h.trans (le_of_eq ?_))
      · ring
      · ring
    · have h := sum_lin_sq_le t ei mi xi he hm hx zero_le_one h4
        (by positivity : (0 : ℝ) ≤ 3 * r ^ 2 + 2 * r) hei hmi hxi
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_)) (h.trans (le_of_eq ?_))
      · ring
      · ring

/-- **Closed form.**  From `(m, 0, 0)`, if `6 r q ≤ 1`, the potential after `q` oracle steps is at
most `84 q² r² m²`. -/
theorem Pot_le {r : ℝ} (hr : 0 ≤ r) (q : ℕ) (hq : 6 * r * q ≤ 1) {m : ℝ} (hm : 0 ≤ m) :
    Pot r q m 0 0 ≤ 84 * (q : ℝ) ^ 2 * r ^ 2 * m ^ 2 := by
  have key : ∀ (n t : ℕ) (x e : ℝ), t + n = q → 0 ≤ x → 0 ≤ e → x ≤ 6 * r * t * m →
      e ≤ 6 * r ^ 2 * (t + (t : ℝ) ^ 2) * m → Pot r n m x e ≤ 84 * (q : ℝ) ^ 2 * r ^ 2 * m ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro t x e ht hx he hxt het
      have htq : t = q := by omega
      subst htq
      simp only [Pot]
      have hq0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have hxm : x ≤ m := by nlinarith
      have ht2 : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos t with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ t := by exact_mod_cast h
          nlinarith
      have he2 : e ≤ 12 * r ^ 2 * (t : ℝ) ^ 2 * m := by
        have : 6 * r ^ 2 * (t + (t : ℝ) ^ 2) * m ≤ 12 * r ^ 2 * (t : ℝ) ^ 2 * m := by
          have h6 : 0 ≤ 6 * r ^ 2 * m := by positivity
          nlinarith
        linarith
      have hx2 : x ^ 2 ≤ 36 * r ^ 2 * (t : ℝ) ^ 2 * m ^ 2 := by
        have := pow_le_pow_left₀ hx hxt 2
        nlinarith
      have h1 : (m + x) * e ≤ (2 * m) * (12 * r ^ 2 * (t : ℝ) ^ 2 * m) :=
        mul_le_mul (by linarith) he2 he (by positivity)
      nlinarith
    | succ n ih =>
      intro t x e ht hx he hxt het
      simp only [Pot]
      have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have htq : (t : ℝ) + 1 ≤ q := by
        have : t + 1 ≤ q := by omega
        exact_mod_cast this
      have h6 : 6 * r * t ≤ 1 := by nlinarith
      refine ih (t + 1) _ _ (by omega) (by positivity) (by positivity) ?_ ?_
      · push_cast
        have : 3 * r * (m + x) ≤ 3 * r * (m + 6 * r * t * m) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h7 : 3 * r * (6 * r * t * m) ≤ 3 * r * m := by
          have : 6 * r * t * m ≤ 1 * m := mul_le_mul_of_nonneg_right h6 hm
          nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 3 * r)]
        nlinarith
      · push_cast
        have hxm : x ≤ m := by nlinarith
        have h8 : 3 * r ^ 2 * (m + x) ≤ 6 * r ^ 2 * m := by
          nlinarith [mul_le_mul_of_nonneg_left hxm (by positivity : (0 : ℝ) ≤ 3 * r ^ 2)]
        have h9 : 2 * r * x ≤ 12 * r ^ 2 * t * m := by
          nlinarith [mul_le_mul_of_nonneg_left hxt (by positivity : (0 : ℝ) ≤ 2 * r)]
        have h10 : 0 ≤ 6 * r ^ 2 * m := by positivity
        nlinarith
  exact key q 0 0 0 (by omega) le_rfl le_rfl (by simp) (by simp)

/-! ## One oracle call on families indexed by mark patterns and rows -/

section Step

variable {X Y J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
  (p : X → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (r : ℝ) (hr : 0 ≤ r)
  (hpr : ∀ k, p k ≤ r ^ 2) (row : X → J) (G h : X → Y)

/-- The function of a mark pattern: the marked points take the value `h`, the others `G`. -/
def Hw (s : X → Bool) : X → Y := fun k ↦ if s k then h k else G k

/-- Mean of a family over a resampled row `j`. -/
noncomputable def etaT {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (η : (X → Bool) → J → E) (s : X → Bool) (j : J) : E :=
  ∑ s', (bw p s' : ℂ) • η (mix row j s s') j

theorem dsum_eq (f : (X → Bool) → J → ℝ) :
    ∑ s, bw p s * ∑ j, f s j = ∑ v : (X → Bool) × J, bw p v.1 * f v.1 v.2 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun s _ ↦ Finset.mul_sum _ _ _

include hp0 hp1 in
/-- Weighted Minkowski over patterns and rows. -/
theorem mink2 (f a b : (X → Bool) → J → ℝ) (hf0 : ∀ s j, 0 ≤ f s j)
    (hf : ∀ s j, f s j ≤ a s j + b s j)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∑ s, bw p s * ∑ j, a s j ^ 2 ≤ A ^ 2)
    (hb : ∑ s, bw p s * ∑ j, b s j ^ 2 ≤ B ^ 2) :
    ∑ s, bw p s * ∑ j, f s j ^ 2 ≤ (A + B) ^ 2 := by
  rw [dsum_eq] at ha hb ⊢
  refine le_trans (Finset.sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hf0 v.1 v.2) (hf v.1 v.2) 2) (bw_nonneg p hp0 hp1 v.1)) ?_
  exact sum_mul_add_sq_le (fun v : (X → Bool) × J ↦ bw p v.1) (fun v ↦ a v.1 v.2)
    (fun v ↦ b v.1 v.2) (fun v ↦ bw_nonneg p hp0 hp1 v.1) hA hB ha hb

include hpr hp0 in
theorem sum_bw_mark_le (j : J) (k : X) :
    ∑ s' with k ∈ (Finset.univ.filter fun k' ↦ row k' = j ∧ s' k' = true), bw p s' ≤
      if row k = j then r ^ 2 else 0 := by
  rw [Finset.sum_filter]
  by_cases hk : row k = j
  · simp only [hk, Finset.mem_filter, Finset.mem_univ, true_and, ite_true]
    refine le_trans (le_of_eq ?_) (hpr k)
    rw [← sum_bw_mark p k]
    exact Finset.sum_congr rfl fun s' _ ↦ by split_ifs <;> simp
  · simp [hk]

variable {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [NormedAddCommGroup E₃]
  [InnerProductSpace ℂ E₃] (Iq : OracleInterface X Y E₂) (T : E₁ ≃ₗᵢ[ℂ] E₂)
  (T' : E₂ ≃ₗᵢ[ℂ] E₃) (ψ : (X → Bool) → E₁) (φ : (X → Bool) → J → E₁)
  (hφ : ∀ s j, φ s j = φ (clean row j s) j)

include hφ in
theorem phi_mix (j : J) (s s' : X → Bool) : φ (mix row j s s') j = φ s j := by
  rw [hφ (mix row j s s') j, clean_mix, ← hφ]

/-- Row masses of the cleaned vectors: bounded by the real vector and the deviations. -/
theorem row_mass_le (s : X → Bool) :
    ∑ j, ∑ k, (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) ≤
      2 * ‖ψ s‖ ^ 2 + 2 * ∑ j, ‖ψ s - φ s j‖ ^ 2 := by
  have h1 : ∀ j k, ‖Iq.P k (T (φ s j))‖ ^ 2 ≤
      2 * ‖Iq.P k (T (ψ s))‖ ^ 2 + 2 * ‖Iq.P k (T (ψ s - φ s j))‖ ^ 2 := by
    intro j k
    have e : Iq.P k (T (φ s j)) = Iq.P k (T (ψ s)) - Iq.P k (T (ψ s - φ s j)) := by
      simp only [map_sub]; abel
    rw [e]
    have := norm_sub_le (Iq.P k (T (ψ s))) (Iq.P k (T (ψ s - φ s j)))
    nlinarith [norm_nonneg (Iq.P k (T (ψ s)) - Iq.P k (T (ψ s - φ s j))),
      norm_nonneg (Iq.P k (T (ψ s))), norm_nonneg (Iq.P k (T (ψ s - φ s j))),
      sq_nonneg (‖Iq.P k (T (ψ s))‖ - ‖Iq.P k (T (ψ s - φ s j))‖)]
  have h2 : ∑ j, ∑ k, (if row k = j then 2 * ‖Iq.P k (T (ψ s))‖ ^ 2 else 0) ≤ 2 * ‖ψ s‖ ^ 2 := by
    rw [Finset.sum_comm]
    have : ∀ k, ∑ j, (if row k = j then 2 * ‖Iq.P k (T (ψ s))‖ ^ 2 else 0) =
        2 * ‖Iq.P k (T (ψ s))‖ ^ 2 := fun k ↦ by simp
    simp only [this]
    rw [← Finset.mul_sum]
    have := Iq.P_sum_le (T (ψ s))
    rw [LinearIsometryEquiv.norm_map] at this
    linarith
  have h3 : ∀ j, ∑ k, (if row k = j then 2 * ‖Iq.P k (T (ψ s - φ s j))‖ ^ 2 else 0) ≤
      2 * ‖ψ s - φ s j‖ ^ 2 := by
    intro j
    have := Iq.P_sum_le (T (ψ s - φ s j))
    rw [LinearIsometryEquiv.norm_map] at this
    calc ∑ k, (if row k = j then 2 * ‖Iq.P k (T (ψ s - φ s j))‖ ^ 2 else 0)
        ≤ ∑ k, 2 * ‖Iq.P k (T (ψ s - φ s j))‖ ^ 2 :=
          Finset.sum_le_sum fun k _ ↦ by
            split_ifs
            · exact le_rfl
            · positivity
      _ = 2 * ∑ k, ‖Iq.P k (T (ψ s - φ s j))‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by linarith
  calc ∑ j, ∑ k, (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)
      ≤ ∑ j, ∑ k, ((if row k = j then 2 * ‖Iq.P k (T (ψ s))‖ ^ 2 else 0) +
          (if row k = j then 2 * ‖Iq.P k (T (ψ s - φ s j))‖ ^ 2 else 0)) :=
        Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun k _ ↦ by
          split_ifs
          · exact h1 j k
          · simp
    _ = ∑ j, ∑ k, (if row k = j then 2 * ‖Iq.P k (T (ψ s))‖ ^ 2 else 0) +
          ∑ j, ∑ k, (if row k = j then 2 * ‖Iq.P k (T (ψ s - φ s j))‖ ^ 2 else 0) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ 2 * ‖ψ s‖ ^ 2 + ∑ j, 2 * ‖ψ s - φ s j‖ ^ 2 :=
        add_le_add h2 (Finset.sum_le_sum fun j _ ↦ h3 j)
    _ = _ := by rw [Finset.mul_sum]

include hp0 hp1 in
theorem row_mass_avg_le {m x : ℝ} (hm : ∑ s, bw p s * ‖ψ s‖ ^ 2 ≤ m ^ 2)
    (hx : ∑ s, bw p s * ∑ j, ‖ψ s - φ s j‖ ^ 2 ≤ x ^ 2) :
    ∑ s, bw p s * ∑ j, ∑ k, (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) ≤
      2 * m ^ 2 + 2 * x ^ 2 := by
  calc _ ≤ ∑ s, bw p s * (2 * ‖ψ s‖ ^ 2 + 2 * ∑ j, ‖ψ s - φ s j‖ ^ 2) :=
        Finset.sum_le_sum fun s _ ↦
          mul_le_mul_of_nonneg_left (row_mass_le row Iq T ψ φ s) (bw_nonneg p hp0 hp1 s)
    _ = 2 * ∑ s, bw p s * ‖ψ s‖ ^ 2 + 2 * ∑ s, bw p s * ∑ j, ‖ψ s - φ s j‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ ↦ by ring
    _ ≤ _ := by linarith

include hφ hpr hp0 hp1 in
/-- **Hiddenness of the marks of a row from the cleaned vectors of that row.** -/
theorem marked_row_mass_le (j : J) :
    ∑ s, bw p s * ∑ k, (if row k = j ∧ s k = true then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) ≤
      r ^ 2 * ∑ s, bw p s * ∑ k, (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) := by
  rw [← sum_bw_mix p row j fun t ↦
    ∑ k, (if row k = j ∧ t k = true then ‖Iq.P k (T (φ t j))‖ ^ 2 else 0), Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [← mul_assoc, mul_comm (r ^ 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (bw_nonneg p hp0 hp1 s)
  have e : ∀ s', ∑ k, (if row k = j ∧ mix row j s s' k = true then
      ‖Iq.P k (T (φ (mix row j s s') j))‖ ^ 2 else 0) =
      ∑ k, (if row k = j then (if s' k then (1 : ℝ) else 0) * ‖Iq.P k (T (φ s j))‖ ^ 2
        else 0) := by
    intro s'
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [phi_mix row φ hφ]
    by_cases hk : row k = j
    · simp only [hk, true_and, ite_true, mix_of_row row hk]
      split_ifs <;> simp
    · simp [hk]
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  by_cases hk : row k = j
  · simp only [hk, ite_true]
    have : ∑ s', bw p s' * ((if s' k then (1 : ℝ) else 0) * ‖Iq.P k (T (φ s j))‖ ^ 2) =
        p k * ‖Iq.P k (T (φ s j))‖ ^ 2 := by
      rw [← sum_bw_mark p k, Finset.sum_mul]
      exact Finset.sum_congr rfl fun s' _ ↦ by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (hpr k) (sq_nonneg _)
  · simp [hk]

theorem swap_sum (c : ℝ) (f : (X → Bool) → J → ℝ) :
    ∑ s, bw p s * ∑ j, c * f s j = c * ∑ j, ∑ s, bw p s * f s j := by
  calc ∑ s, bw p s * ∑ j, c * f s j = ∑ s, ∑ j, c * (bw p s * f s j) :=
        Finset.sum_congr rfl fun s _ ↦ by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ∑ j, ∑ s, c * (bw p s * f s j) := Finset.sum_comm
    _ = c * ∑ j, ∑ s, bw p s * f s j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]

theorem swap_sum_one (f : (X → Bool) → J → ℝ) :
    ∑ j, ∑ s, bw p s * f s j = ∑ s, bw p s * ∑ j, f s j := by
  have h := swap_sum p 1 f
  simp only [one_mul] at h
  exact h.symm

theorem Hw_ne_mem (j : J) (s : X → Bool) (k : X)
    (hne : Hw G h s k ≠ Hw G h (clean row j s) k) :
    k ∈ (Finset.univ.filter fun k' ↦ row k' = j ∧ s k' = true) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hc
  refine hne ?_
  by_cases hk : row k = j
  · by_cases hs : s k = true
    · exact absurd ⟨hk, hs⟩ hc
    · simp [Hw, clean, hk, hs]
  · simp [Hw, clean, hk]

theorem Hw_mix_ne_mem (j : J) (s s' : X → Bool) (k : X)
    (hne : Hw G h (mix row j s s') k ≠ Hw G h (clean row j s) k) :
    k ∈ (Finset.univ.filter fun k' ↦ row k' = j ∧ s' k' = true) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hc
  refine hne ?_
  by_cases hk : row k = j
  · by_cases hs : s' k = true
    · exact absurd ⟨hk, hs⟩ hc
    · simp [Hw, clean, mix, hk, hs]
  · simp [Hw, clean, mix, hk]

include hφ hpr hp0 hp1 hr in
/-- **One oracle call.**  The real vectors evolve under the function of their pattern, the
cleaned vectors of row `j` under the function of the pattern with row `j` cleaned.  The three
tracked quantities change by at most `m ↦ m`, `x ↦ x + 3 r (m + x)`,
`e ↦ e + 3 r² (m + x) + 2 r x`. -/
theorem rows_query_step {m x e : ℝ} (hm0 : 0 ≤ m) (hx0 : 0 ≤ x) (he0 : 0 ≤ e)
    (hm : ∑ s, bw p s * ‖ψ s‖ ^ 2 ≤ m ^ 2)
    (hx : ∑ s, bw p s * ∑ j, ‖ψ s - φ s j‖ ^ 2 ≤ x ^ 2)
    (he : ∑ s, bw p s * ∑ j, ‖etaT p row (fun s j ↦ ψ s - φ s j) s j‖ ^ 2 ≤ e ^ 2) :
    (∑ s, bw p s * ‖T' (Iq.O (Hw G h s) (T (ψ s)))‖ ^ 2 ≤ m ^ 2) ∧
    (∑ s, bw p s * ∑ j, ‖T' (Iq.O (Hw G h s) (T (ψ s))) -
        T' (Iq.O (Hw G h (clean row j s)) (T (φ s j)))‖ ^ 2 ≤ (x + 3 * r * (m + x)) ^ 2) ∧
    (∑ s, bw p s * ∑ j, ‖etaT p row (fun s j ↦ T' (Iq.O (Hw G h s) (T (ψ s))) -
        T' (Iq.O (Hw G h (clean row j s)) (T (φ s j)))) s j‖ ^ 2 ≤
      (e + 3 * r ^ 2 * (m + x) + 2 * r * x) ^ 2) := by
  have hw := bw_nonneg p hp0 hp1
  have hmass := row_mass_avg_le p hp0 hp1 row Iq T ψ φ hm hx
  have hmass0 : 0 ≤ ∑ s, bw p s * ∑ j, ∑ k,
      (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (Finset.sum_nonneg fun j _ ↦
      Finset.sum_nonneg fun k _ ↦ by split_ifs <;> positivity)
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (hw s)) hm
    rw [LinearIsometryEquiv.norm_map]
    refine (Iq.O_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
  · -- deviations
    have key1 : ∀ s j, T' (Iq.O (Hw G h s) (T (ψ s))) -
        T' (Iq.O (Hw G h (clean row j s)) (T (φ s j))) =
        T' (Iq.O (Hw G h s) (T (ψ s - φ s j)) +
          Iq.D (Hw G h s) (Hw G h (clean row j s)) (T (φ s j))) := by
      intro s j
      simp only [OracleInterface.D, map_sub, map_add]
      abel
    have hD : ∑ s, bw p s * ∑ j,
        ‖Iq.D (Hw G h s) (Hw G h (clean row j s)) (T (φ s j))‖ ^ 2 ≤ (3 * r * (m + x)) ^ 2 := by
      have h1 : ∀ s j, ‖Iq.D (Hw G h s) (Hw G h (clean row j s)) (T (φ s j))‖ ^ 2 ≤
          4 * ∑ k, (if row k = j ∧ s k = true then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) := by
        intro s j
        have := Iq.norm_D_sq_le (Hw G h s) (Hw G h (clean row j s)) _
          (Hw_ne_mem row G h j s) (T (φ s j))
        rwa [Finset.sum_filter] at this
      calc _ ≤ ∑ s, bw p s * ∑ j, 4 * ∑ k,
            (if row k = j ∧ s k = true then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) :=
          Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ ↦ h1 s j) (hw s)
        _ = 4 * ∑ j, ∑ s, bw p s * ∑ k,
            (if row k = j ∧ s k = true then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) := swap_sum p 4 _
        _ ≤ 4 * ∑ j, r ^ 2 * ∑ s, bw p s * ∑ k,
            (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦
            marked_row_mass_le p hp0 hp1 r hpr row Iq T φ hφ j) (by norm_num)
        _ = 4 * r ^ 2 * ∑ s, bw p s * ∑ j, ∑ k,
            (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0) := by
          rw [← Finset.mul_sum, swap_sum_one p fun s j ↦ ∑ k,
            (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)]
          ring
        _ ≤ 4 * r ^ 2 * (2 * m ^ 2 + 2 * x ^ 2) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
        _ ≤ _ := by
          have h4 : 0 ≤ r ^ 2 := sq_nonneg r
          nlinarith [mul_nonneg h4 (mul_nonneg hm0 hx0), mul_nonneg h4 (sq_nonneg m),
            mul_nonneg h4 (sq_nonneg x)]
    have h := mink2 p hp0 hp1
      (fun s j ↦ ‖T' (Iq.O (Hw G h s) (T (ψ s))) -
        T' (Iq.O (Hw G h (clean row j s)) (T (φ s j)))‖)
      (fun s j ↦ ‖ψ s - φ s j‖)
      (fun s j ↦ ‖Iq.D (Hw G h s) (Hw G h (clean row j s)) (T (φ s j))‖)
      (fun _ _ ↦ norm_nonneg _)
      (fun s j ↦ by
        rw [key1, LinearIsometryEquiv.norm_map]
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (Iq.O_le _ _).trans ?_
        rw [LinearIsometryEquiv.norm_map])
      hx0 (by positivity) hx hD
    exact h
  · -- conditional means
    have key2 : ∀ (s : X → Bool) (j : J) (s' : X → Bool),
        T' (Iq.O (Hw G h (mix row j s s')) (T (ψ (mix row j s s')))) -
          T' (Iq.O (Hw G h (clean row j (mix row j s s'))) (T (φ (mix row j s s') j))) =
        T' (Iq.O (Hw G h (clean row j s)) (T (ψ (mix row j s s') - φ (mix row j s s') j)) +
          Iq.D (Hw G h (mix row j s s')) (Hw G h (clean row j s))
            (T (ψ (mix row j s s') - φ (mix row j s s') j)) +
          Iq.D (Hw G h (mix row j s s')) (Hw G h (clean row j s)) (T (φ s j))) := by
      intro s j s'
      rw [clean_mix, phi_mix row φ hφ]
      simp only [OracleInterface.D, map_sub, map_add]
      abel
    -- the two correction terms
    let B1 : (X → Bool) → J → ℝ := fun s j ↦
      ‖∑ s', (bw p s' : ℂ) • Iq.D (Hw G h (mix row j s s')) (Hw G h (clean row j s))
        (T (ψ (mix row j s s') - φ (mix row j s s') j))‖
    let B2 : (X → Bool) → J → ℝ := fun s j ↦
      ‖∑ s', (bw p s' : ℂ) • Iq.D (Hw G h (mix row j s s')) (Hw G h (clean row j s))
        (T (φ s j))‖
    have hε2 : ∀ (j : J) (k : X),
        ∑ s' with k ∈ (Finset.univ.filter fun k' ↦ row k' = j ∧ s' k' = true), bw p s' ≤
          r ^ 2 := fun j k ↦
      (sum_bw_mark_le p hp0 r hpr row j k).trans (by
        split_ifs
        · exact le_rfl
        · exact sq_nonneg r)
    have hB1 : ∀ s j, B1 s j ^ 2 ≤ 4 * r ^ 2 *
        ∑ s', bw p s' * ‖ψ (mix row j s s') - φ (mix row j s s') j‖ ^ 2 := by
      intro s j
      have h := norm_avg_D_sq_le_var Iq (bw p) hw (fun s' ↦ Hw G h (mix row j s s'))
        (Hw G h (clean row j s))
        (fun s' ↦ Finset.univ.filter fun k' ↦ row k' = j ∧ s' k' = true)
        (fun s' k ↦ Hw_mix_ne_mem row G h j s s' k) (r ^ 2) (sq_nonneg r) (hε2 j)
        (fun s' ↦ T (ψ (mix row j s s') - φ (mix row j s s') j))
      simpa only [LinearIsometryEquiv.norm_map] using h
    have hB2 : ∀ s j, B2 s j ^ 2 ≤ 4 * r ^ 2 * (r ^ 2 *
        ∑ k, (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)) := by
      intro s j
      have h := norm_avg_D_sq_le Iq (bw p) hw (fun s' ↦ Hw G h (mix row j s s'))
        (Hw G h (clean row j s))
        (fun s' ↦ Finset.univ.filter fun k' ↦ row k' = j ∧ s' k' = true)
        (fun s' k ↦ Hw_mix_ne_mem row G h j s s' k) (fun _ ↦ T (φ s j))
      have hk : ∀ k, (∑ s' with k ∈ (Finset.univ.filter fun k' ↦ row k' = j ∧ s' k' = true),
          bw p s' * ‖Iq.P k (T (φ s j))‖) ^ 2 ≤
          r ^ 2 * (r ^ 2 * (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)) := by
        intro k
        rw [← Finset.sum_mul, mul_pow]
        have h0 : 0 ≤ ∑ s' with k ∈ (Finset.univ.filter fun k' ↦ row k' = j ∧ s' k' = true),
            bw p s' := Finset.sum_nonneg fun s' _ ↦ hw s'
        have hle := sum_bw_mark_le p hp0 r hpr row j k
        by_cases hk : row k = j
        · simp only [hk, ite_true] at hle ⊢
          have h2 := pow_le_pow_left₀ h0 hle 2
          calc _ ≤ (r ^ 2) ^ 2 * ‖Iq.P k (T (φ s j))‖ ^ 2 :=
                mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
            _ = _ := by ring
        · simp only [hk, ite_false] at hle ⊢
          have : ∑ s' with k ∈ (Finset.univ.filter fun k' ↦ row k' = j ∧ s' k' = true),
              bw p s' = 0 := le_antisymm hle h0
          rw [this]
          simp
      calc _ ≤ _ := h
        _ ≤ 4 * ∑ k, r ^ 2 * (r ^ 2 * (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ hk k) (by norm_num)
        _ = _ := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
            ring
    have hS1 : ∑ s, bw p s * ∑ j, B1 s j ^ 2 ≤ (2 * r * x) ^ 2 := by
      calc _ ≤ ∑ s, bw p s * ∑ j, 4 * r ^ 2 *
            ∑ s', bw p s' * ‖ψ (mix row j s s') - φ (mix row j s s') j‖ ^ 2 :=
          Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ ↦ hB1 s j) (hw s)
        _ = 4 * r ^ 2 * ∑ j, ∑ s, bw p s *
            ∑ s', bw p s' * ‖ψ (mix row j s s') - φ (mix row j s s') j‖ ^ 2 :=
          swap_sum p (4 * r ^ 2) _
        _ = 4 * r ^ 2 * ∑ j, ∑ s, bw p s * ‖ψ s - φ s j‖ ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl fun j _ ↦
            sum_bw_mix p row j fun t ↦ ‖ψ t - φ t j‖ ^ 2
        _ = 4 * r ^ 2 * ∑ s, bw p s * ∑ j, ‖ψ s - φ s j‖ ^ 2 := by
          rw [swap_sum_one p fun s j ↦ ‖ψ s - φ s j‖ ^ 2]
        _ ≤ 4 * r ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = _ := by ring
    have hS2 : ∑ s, bw p s * ∑ j, B2 s j ^ 2 ≤ (3 * r ^ 2 * (m + x)) ^ 2 := by
      calc _ ≤ ∑ s, bw p s * ∑ j, 4 * r ^ 2 * (r ^ 2 *
            ∑ k, (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)) :=
          Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ ↦ hB2 s j) (hw s)
        _ = 4 * r ^ 2 * ∑ j, ∑ s, bw p s * (r ^ 2 *
            ∑ k, (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)) :=
          swap_sum p (4 * r ^ 2) _
        _ = 4 * r ^ 2 * (r ^ 2 * ∑ s, bw p s * ∑ j, ∑ k,
            (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)) := by
          rw [swap_sum_one p fun s j ↦ r ^ 2 *
            ∑ k, (if row k = j then ‖Iq.P k (T (φ s j))‖ ^ 2 else 0)]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [← Finset.mul_sum]
          ring
        _ ≤ 4 * r ^ 2 * (r ^ 2 * (2 * m ^ 2 + 2 * x ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (sq_nonneg r))
            (by positivity)
        _ ≤ _ := by
          have h4 : 0 ≤ r ^ 2 * r ^ 2 := by positivity
          nlinarith [mul_nonneg h4 (mul_nonneg hm0 hx0), mul_nonneg h4 (sq_nonneg m),
            mul_nonneg h4 (sq_nonneg x)]
    have hS12 := mink2 p hp0 hp1 (fun s j ↦ B1 s j + B2 s j) B1 B2
      (fun _ _ ↦ add_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _ _ ↦ le_rfl)
      (by positivity) (by positivity) hS1 hS2
    have hnorm : ∀ s j, ‖etaT p row (fun s j ↦ T' (Iq.O (Hw G h s) (T (ψ s))) -
        T' (Iq.O (Hw G h (clean row j s)) (T (φ s j)))) s j‖ ≤
        ‖etaT p row (fun s j ↦ ψ s - φ s j) s j‖ + (B1 s j + B2 s j) := by
      intro s j
      have e : etaT p row (fun s j ↦ T' (Iq.O (Hw G h s) (T (ψ s))) -
          T' (Iq.O (Hw G h (clean row j s)) (T (φ s j)))) s j =
          T' (Iq.O (Hw G h (clean row j s)) (T (etaT p row (fun s j ↦ ψ s - φ s j) s j)) +
            ∑ s', (bw p s' : ℂ) • Iq.D (Hw G h (mix row j s s')) (Hw G h (clean row j s))
              (T (ψ (mix row j s s') - φ (mix row j s s') j)) +
            ∑ s', (bw p s' : ℂ) • Iq.D (Hw G h (mix row j s s')) (Hw G h (clean row j s))
              (T (φ s j))) := by
        unfold etaT
        simp only [key2]
        rw [map_add, map_add, map_sum, map_sum, map_sum, map_sum, map_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s' _ ↦ ?_
        simp only [map_smul, map_add, smul_add]
      rw [e, LinearIsometryEquiv.norm_map]
      refine (norm_add_le _ _).trans ?_
      have h1 := norm_add_le
        (Iq.O (Hw G h (clean row j s)) (T (etaT p row (fun s j ↦ ψ s - φ s j) s j)))
        (∑ s', (bw p s' : ℂ) • Iq.D (Hw G h (mix row j s s')) (Hw G h (clean row j s))
          (T (ψ (mix row j s s') - φ (mix row j s s') j)))
      have h2 : ‖Iq.O (Hw G h (clean row j s))
          (T (etaT p row (fun s j ↦ ψ s - φ s j) s j))‖ ≤
          ‖etaT p row (fun s j ↦ ψ s - φ s j) s j‖ := by
        refine (Iq.O_le _ _).trans ?_
        rw [LinearIsometryEquiv.norm_map]
      linarith
    have h := mink2 p hp0 hp1
      (fun s j ↦ ‖etaT p row (fun s j ↦ T' (Iq.O (Hw G h s) (T (ψ s))) -
        T' (Iq.O (Hw G h (clean row j s)) (T (φ s j)))) s j‖)
      (fun s j ↦ ‖etaT p row (fun s j ↦ ψ s - φ s j) s j‖) (fun s j ↦ B1 s j + B2 s j)
      (fun _ _ ↦ norm_nonneg _) hnorm he0 (by positivity) he hS12
    refine h.trans (le_of_eq ?_)
    ring

end Step

/-! ## The induction over the program -/

theorem Pot_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) {m x e : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x)
    (he : 0 ≤ e) : 0 ≤ Pot r n m x e :=
  le_trans (by simp only [Pot]; positivity) (Pot_zero_le hr n hm hx he)

/-- Weighted Cauchy–Schwarz. -/
theorem wsum_mul_le {ι : Type*} [Fintype ι] (w a b : ι → ℝ) (hw : ∀ s, 0 ≤ w s) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∑ s, w s * a s ^ 2 ≤ A ^ 2)
    (hb : ∑ s, w s * b s ^ 2 ≤ B ^ 2) : ∑ s, w s * (a s * b s) ≤ A * B := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun s ↦ w s * (a s * b s)) (f := fun s ↦ w s * a s ^ 2) (g := fun s ↦ w s * b s ^ 2)
    (fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _)) (fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _))
    (fun s _ ↦ le_of_eq (by ring))
  have h2 : (∑ s, w s * (a s * b s)) ^ 2 ≤ (A * B) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (mul_le_mul ha hb (Finset.sum_nonneg fun s _ ↦
      mul_nonneg (hw s) (sq_nonneg _)) (sq_nonneg _))
  exact le_of_sq_le_sq h2 (mul_nonneg hA hB)

theorem sum3_comm {S J K : Type*} [Fintype S] [Fintype J] [Fintype K] (w : S → ℝ) (c : J → ℝ)
    (a b : S → J → K → ℝ) :
    ∑ s, w s * ∑ j, c j * (∑ κ, a s j κ - ∑ κ, b s j κ) =
      ∑ κ, ∑ s, w s * ∑ j, c j * (a s j κ - b s j κ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]

theorem prim_kraus_sigma_le {L : LocalSig.{u, v}} {A : QReg} (I : L.Interp) (o : L.Op A)
    (t : Finset (L.Outcome o)) (u : EuclideanSpace ℂ (A × Unit)) :
    ∑ i ∈ t.sigma fun b ↦ (Finset.univ : Finset ((L.next o b × Unit) × (A × Unit))),
      ‖primKraus I o i.1 i.2 u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [Finset.sum_sigma]
  exact prim_kraus_sum_le I o t u

section Program

variable {X Y J : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype J] [DecidableEq J] {L : LocalSig.{u, v}} {W : QReg → Type w}
  (p : X → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (r : ℝ) (hr : 0 ≤ r)
  (hpr : ∀ k, p k ≤ r ^ 2) (row : X → J) (G h F : X → Y) (I : L.Interp)
  (Ev : J → (Σ u, W u) → Prop) (hdisj : ∀ i j l, Ev i l → Ev j l → i = j)
  (c : J → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)

/-- The weighted difference "cleaned row of the output index" minus "real", summed over the
output indices. -/
noncomputable def Lam {A : QReg} (x : QuantumComp L (qrom2Spec X Y) W A)
    (ψ : (X → Bool) → EuclideanSpace ℂ (A × Unit))
    (φ : (X → Bool) → J → EuclideanSpace ℂ (A × Unit)) : ℝ :=
  ∑ s, bw p s * ∑ j, c j * (pvP I F (Hw G h (clean row j s)) x (Ev j) (φ s j) -
    pvP I F (Hw G h s) x (Ev j) (ψ s))

/-- Kraus maps contract the weighted double sums (`ν i u` stands for `‖K i u‖`). -/
theorem kraus_dsum_le {ι V : Type*} [NormedAddCommGroup V]
    (t : Finset ι) (ν : ι → V → ℝ) (hK : ∀ u, ∑ i ∈ t, ν i u ^ 2 ≤ ‖u‖ ^ 2)
    (w : (X → Bool) → ℝ) (hw : ∀ s, 0 ≤ w s) (f : (X → Bool) → J → V) :
    ∑ i ∈ t, ∑ s, w s * ∑ j, ν i (f s j) ^ 2 ≤ ∑ s, w s * ∑ j, ‖f s j‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hw s)
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun j _ ↦ hK _

theorem kraus_sum_le' {ι V : Type*} [NormedAddCommGroup V]
    (t : Finset ι) (ν : ι → V → ℝ) (hK : ∀ u, ∑ i ∈ t, ν i u ^ 2 ≤ ‖u‖ ^ 2)
    (w : (X → Bool) → ℝ) (hw : ∀ s, 0 ≤ w s) (f : (X → Bool) → V) :
    ∑ i ∈ t, ∑ s, w s * ν i (f s) ^ 2 ≤ ∑ s, w s * ‖f s‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hK _) (hw s)

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
theorem prim_m_le {A : QReg} (o : L.Op A) (t : Finset (L.Outcome o)) (w : (X → Bool) → ℝ)
    (hw : ∀ s, 0 ≤ w s) (ψ : (X → Bool) → EuclideanSpace ℂ (A × Unit)) :
    ∑ i ∈ t.sigma fun b ↦ (Finset.univ : Finset ((L.next o b × Unit) × (A × Unit))),
        ∑ s, w s * ‖primKraus I o i.1 i.2 (ψ s)‖ ^ 2 ≤ ∑ s, w s * ‖ψ s‖ ^ 2 :=
by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (prim_kraus_sigma_le I o t (ψ s)) (hw s)

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
theorem prim_d_le {A : QReg} (o : L.Op A) (t : Finset (L.Outcome o)) (w : (X → Bool) → ℝ)
    (hw : ∀ s, 0 ≤ w s) (f : (X → Bool) → J → EuclideanSpace ℂ (A × Unit)) :
    ∑ i ∈ t.sigma fun b ↦ (Finset.univ : Finset ((L.next o b × Unit) × (A × Unit))),
        ∑ s, w s * ∑ j, ‖primKraus I o i.1 i.2 (f s j)‖ ^ 2 ≤ ∑ s, w s * ∑ j, ‖f s j‖ ^ 2 :=
by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hw s)
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun j _ ↦ prim_kraus_sigma_le I o t (f s j)

set_option maxHeartbeats 1600000 in
include hp0 hp1 hr hpr hdisj hc0 hc1 in
/-- **The invariant of the induction over the program.** -/
theorem Lam_le {A : QReg} (x : QuantumComp L (qrom2Spec X Y) W A) :
    ∀ bud : Bool → ℕ, x.IsQueryBound bud → ∀ (ψ : (X → Bool) → EuclideanSpace ℂ (A × Unit))
      (φ : (X → Bool) → J → EuclideanSpace ℂ (A × Unit)),
      (∀ s j, φ s j = φ (clean row j s) j) → ∀ m xx e : ℝ, 0 ≤ m → 0 ≤ xx → 0 ≤ e →
      ∑ s, bw p s * ‖ψ s‖ ^ 2 ≤ m ^ 2 →
      ∑ s, bw p s * ∑ j, ‖ψ s - φ s j‖ ^ 2 ≤ xx ^ 2 →
      ∑ s, bw p s * ∑ j, ‖etaT p row (fun s j ↦ ψ s - φ s j) s j‖ ^ 2 ≤ e ^ 2 →
      |Lam p row G h F I Ev c x ψ φ| ≤ Pot r (bud true) m xx e := by
  classical
  have hw := bw_nonneg p hp0 hp1
  refine QuantumComp.inductionOn (motive := fun A x ↦ ∀ bud : Bool → ℕ, x.IsQueryBound bud →
    ∀ (ψ : (X → Bool) → EuclideanSpace ℂ (A × Unit))
      (φ : (X → Bool) → J → EuclideanSpace ℂ (A × Unit)),
      (∀ s j, φ s j = φ (clean row j s) j) → ∀ m xx e : ℝ, 0 ≤ m → 0 ≤ xx → 0 ≤ e →
      ∑ s, bw p s * ‖ψ s‖ ^ 2 ≤ m ^ 2 →
      ∑ s, bw p s * ∑ j, ‖ψ s - φ s j‖ ^ 2 ≤ xx ^ 2 →
      ∑ s, bw p s * ∑ j, ‖etaT p row (fun s j ↦ ψ s - φ s j) s j‖ ^ 2 ≤ e ^ 2 →
      |Lam p row G h F I Ev c x ψ φ| ≤ Pot r (bud true) m xx e) ?_ ?_ ?_ x
  · -- leaf
    intro A y bud _ ψ φ hφ m xx e hm0 hx0 he0 hm hx he
    refine le_trans ?_ (Pot_zero_le hr (bud true) hm0 hx0 he0)
    simp only [Lam, pvP_pure, Pot]
    by_cases hex : ∃ j0, Ev j0 ⟨A, y⟩
    · obtain ⟨j0, hj0⟩ := hex
      have hsingle : ∀ s, ∑ j, c j * ((if Ev j ⟨A, y⟩ then ‖φ s j‖ ^ 2 else 0) -
          (if Ev j ⟨A, y⟩ then ‖ψ s‖ ^ 2 else 0)) = c j0 * (‖φ s j0‖ ^ 2 - ‖ψ s‖ ^ 2) := by
        intro s
        rw [Finset.sum_eq_single j0]
        · simp [hj0]
        · intro j _ hne
          have : ¬ Ev j ⟨A, y⟩ := fun hj ↦ hne (hdisj j j0 _ hj hj0)
          simp [this]
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      simp only [hsingle]
      have hterm : ∀ s, bw p s * (c j0 * (‖φ s j0‖ ^ 2 - ‖ψ s‖ ^ 2)) =
          -(c j0) * (2 * (bw p s * (inner ℂ (φ s j0) (ψ s - φ s j0)).re) +
            bw p s * ‖ψ s - φ s j0‖ ^ 2) := by
        intro s
        have h' := norm_add_sq (𝕜 := ℂ) (φ s j0) (ψ s - φ s j0)
        simp only [RCLike.re_to_complex, add_sub_cancel] at h'
        rw [h']
        ring
      have hcross : ∑ s, bw p s * (inner ℂ (φ s j0) (ψ s - φ s j0)).re =
          ∑ s, bw p s * (inner ℂ (φ s j0)
            (etaT p row (fun s j ↦ ψ s - φ s j) s j0)).re := by
        rw [← sum_bw_mix p row j0 fun t ↦ (inner ℂ (φ t j0) (ψ t - φ t j0)).re]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        congr 1
        unfold etaT
        rw [inner_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun s' _ ↦ ?_
        rw [inner_smul_right, Complex.re_ofReal_mul]
        beta_reduce
        rw [phi_mix row φ hφ]
      rw [Finset.sum_congr rfl fun s _ ↦ hterm s, ← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum, hcross]
      have hN : ∑ s, bw p s * ‖ψ s - φ s j0‖ ^ 2 ≤ xx ^ 2 :=
        le_trans (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun j ↦ ‖ψ s - φ s j‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
            (Finset.mem_univ j0)) (hw s)) hx
      have hN0 : 0 ≤ ∑ s, bw p s * ‖ψ s - φ s j0‖ ^ 2 :=
        Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _)
      have hE : ∑ s, bw p s * ‖etaT p row (fun s j ↦ ψ s - φ s j) s j0‖ ^ 2 ≤ e ^ 2 :=
        le_trans (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (Finset.single_le_sum
            (f := fun j ↦ ‖etaT p row (fun s j ↦ ψ s - φ s j) s j‖ ^ 2)
            (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j0)) (hw s)) he
      have hφn : ∑ s, bw p s * ‖φ s j0‖ ^ 2 ≤ (m + xx) ^ 2 := by
        refine le_trans (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (hw s))
          (sum_mul_add_sq_le (bw p) (fun s ↦ ‖ψ s‖) (fun s ↦ ‖ψ s - φ s j0‖) hw hm0 hx0 hm hN)
        calc ‖φ s j0‖ = ‖ψ s - (ψ s - φ s j0)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have hX : |∑ s, bw p s * (inner ℂ (φ s j0)
          (etaT p row (fun s j ↦ ψ s - φ s j) s j0)).re| ≤ (m + xx) * e := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun s _ ↦ ?_)
          (wsum_mul_le (bw p) (fun s ↦ ‖φ s j0‖)
            (fun s ↦ ‖etaT p row (fun s j ↦ ψ s - φ s j) s j0‖) hw (by positivity) he0 hφn hE))
        rw [abs_mul, abs_of_nonneg (hw s)]
        exact mul_le_mul_of_nonneg_left
          ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)) (hw s)
      have hc0' := hc0 j0
      have hc1' := hc1 j0
      have hX' := abs_le.1 hX
      have hme : 0 ≤ (m + xx) * e := by positivity
      rw [abs_le]
      constructor <;> nlinarith
    · have hno : ∀ j, ¬ Ev j ⟨A, y⟩ := fun j hj ↦ hex ⟨j, hj⟩
      simp only [hno, ite_false, sub_self, mul_zero, Finset.sum_const_zero, abs_zero]
      positivity
  · -- local operation
    intro A o k ih bud hq ψ φ hφ m xx e hm0 hx0 he0 hm hx he
    have hq' : ∀ b, (k b).IsQueryBound bud := (QuantumComp.isQueryBound_primBind_iff o k _).1 hq
    have hT : HasSum (fun b ↦ ∑ s, bw p s * ∑ j, c j *
        ((∑ κ, pvP I F (Hw G h (clean row j s)) (k b) (Ev j) (primKraus I o b κ (φ s j))) -
          ∑ κ, pvP I F (Hw G h s) (k b) (Ev j) (primKraus I o b κ (ψ s))))
        (Lam p row G h F I Ev c (QuantumComp.primBind o k) ψ φ) := by
      unfold Lam
      refine hasSum_sum fun s _ ↦ HasSum.mul_left _ (hasSum_sum fun j _ ↦ HasSum.mul_left _ ?_)
      obtain ⟨s1, e1⟩ := pvP_primBind I F (Hw G h (clean row j s)) o k (Ev j) (φ s j)
      obtain ⟨s2, e2⟩ := pvP_primBind I F (Hw G h s) o k (Ev j) (ψ s)
      exact (e1 ▸ s1.hasSum).sub (e2 ▸ s2.hasSum)
    rw [← hT.tsum_eq]
    refine abs_tsum_le _ _ fun t ↦ ?_
    let mi : (Σ b : L.Outcome o, (L.next o b × Unit) × (A × Unit)) → ℝ := fun i ↦
      Real.sqrt (∑ s, bw p s * ‖primKraus I o i.1 i.2 (ψ s)‖ ^ 2)
    let xi : (Σ b : L.Outcome o, (L.next o b × Unit) × (A × Unit)) → ℝ := fun i ↦
      Real.sqrt (∑ s, bw p s * ∑ j, ‖primKraus I o i.1 i.2 (ψ s - φ s j)‖ ^ 2)
    let ei : (Σ b : L.Outcome o, (L.next o b × Unit) × (A × Unit)) → ℝ := fun i ↦
      Real.sqrt (∑ s, bw p s * ∑ j,
        ‖primKraus I o i.1 i.2 (etaT p row (fun s j ↦ ψ s - φ s j) s j)‖ ^ 2)
    have hmi2 : ∀ i, mi i ^ 2 = ∑ s, bw p s * ‖primKraus I o i.1 i.2 (ψ s)‖ ^ 2 := fun i ↦
      Real.sq_sqrt (Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _))
    have hxi2 : ∀ i, xi i ^ 2 =
        ∑ s, bw p s * ∑ j, ‖primKraus I o i.1 i.2 (ψ s - φ s j)‖ ^ 2 := fun i ↦
      Real.sq_sqrt (Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s)
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    have hei2 : ∀ i, ei i ^ 2 = ∑ s, bw p s * ∑ j,
        ‖primKraus I o i.1 i.2 (etaT p row (fun s j ↦ ψ s - φ s j) s j)‖ ^ 2 := fun i ↦
      Real.sq_sqrt (Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s)
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    have hbr : ∀ (b : L.Outcome o) (κ : (L.next o b × Unit) × (A × Unit)),
        |∑ s, bw p s * ∑ j, c j *
          (pvP I F (Hw G h (clean row j s)) (k b) (Ev j) (primKraus I o b κ (φ s j)) -
            pvP I F (Hw G h s) (k b) (Ev j) (primKraus I o b κ (ψ s)))| ≤
        Pot r (bud true) (mi ⟨b, κ⟩) (xi ⟨b, κ⟩) (ei ⟨b, κ⟩) := by
      intro b κ
      have h0 := ih b bud (hq' b) (fun s ↦ primKraus I o b κ (ψ s))
        (fun s j ↦ primKraus I o b κ (φ s j)) (fun s j ↦ congrArg _ (hφ s j))
        (mi ⟨b, κ⟩) (xi ⟨b, κ⟩) (ei ⟨b, κ⟩) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (le_of_eq (hmi2 ⟨b, κ⟩).symm)
        (by
          rw [hxi2]
          exact le_of_eq (by simp only [map_sub]))
        (by
          rw [hei2]
          refine le_of_eq ?_
          simp only [etaT, map_sum, map_smul, map_sub])
      unfold Lam at h0
      exact h0
    have hTb : ∀ b, |∑ s, bw p s * ∑ j, c j *
        ((∑ κ, pvP I F (Hw G h (clean row j s)) (k b) (Ev j) (primKraus I o b κ (φ s j))) -
          ∑ κ, pvP I F (Hw G h s) (k b) (Ev j) (primKraus I o b κ (ψ s)))| ≤
        ∑ κ, Pot r (bud true) (mi ⟨b, κ⟩) (xi ⟨b, κ⟩) (ei ⟨b, κ⟩) := by
      intro b
      rw [sum3_comm (bw p) c
        (fun s j κ ↦ pvP I F (Hw G h (clean row j s)) (k b) (Ev j) (primKraus I o b κ (φ s j)))
        (fun s j κ ↦ pvP I F (Hw G h s) (k b) (Ev j) (primKraus I o b κ (ψ s)))]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun κ _ ↦ ?_)
      exact hbr b κ
    refine le_trans (Finset.sum_le_sum fun b _ ↦ hTb b) ?_
    rw [← Finset.sum_sigma t
      (fun b ↦ (Finset.univ : Finset ((L.next o b × Unit) × (A × Unit))))
      (fun i ↦ Pot r (bud true) (mi i) (xi i) (ei i))]
    refine Pot_sum_le hr _ _ mi xi ei (fun _ ↦ Real.sqrt_nonneg _) (fun _ ↦ Real.sqrt_nonneg _)
      (fun _ ↦ Real.sqrt_nonneg _) hm0 hx0 he0 ?_ ?_ ?_
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ hmi2 i)) ?_
      exact (prim_m_le I o t (bw p) hw ψ).trans hm
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ hxi2 i)) ?_
      exact (prim_d_le I o t (bw p) hw (fun s j ↦ ψ s - φ s j)).trans hx
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ hei2 i)) ?_
      exact (prim_d_le I o t (bw p) hw
        (fun s j ↦ etaT p row (fun s j ↦ ψ s - φ s j) s j)).trans he
  · -- oracle call
    intro A i E' ℓ k ih bud hq ψ φ hφ m xx e hm0 hx0 he0 hm hx he
    obtain ⟨hn, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff (L := L) (spec := qrom2Spec X Y)
      i E' ℓ k bud).1 hq
    have hLam : Lam p row G h F I Ev c (QuantumComp.queryBind (spec := qrom2Spec X Y) i E' ℓ k)
        ψ φ = Lam p row G h F I Ev c (k ()) (fun s ↦ qvec ℓ (ports F (Hw G h s) i) (ψ s))
          (fun s j ↦ qvec ℓ (ports F (Hw G h (clean row j s)) i) (φ s j)) := by
      simp only [Lam, pvP_queryBind]
    rw [hLam]
    cases i with
    | false =>
      simp only [ports_false]
      have hb : Function.update bud false (bud false - 1) true = bud true := by simp
      have hsub : ∀ a b : EuclideanSpace ℂ (A × Unit),
          qvec ℓ F a - qvec ℓ F b = qvec ℓ F (a - b) := fun a b ↦ by simp only [qvec, map_sub]
      have h' := ih () _ (hk ()) (fun s ↦ qvec ℓ F (ψ s)) (fun s j ↦ qvec ℓ F (φ s j))
        (fun s j ↦ congrArg _ (hφ s j)) m xx e hm0 hx0 he0
        ((Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_qvec_le ℓ F (ψ s)) 2) (hw s)).trans hm)
        ((Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ ↦ by
            rw [hsub]
            exact pow_le_pow_left₀ (norm_nonneg _) (norm_qvec_le ℓ F _) 2) (hw s)).trans hx)
        ((Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ ↦ by
            have e1 : etaT p row (fun s j ↦ qvec ℓ F (ψ s) - qvec ℓ F (φ s j)) s j =
                qvec ℓ F (etaT p row (fun s j ↦ ψ s - φ s j) s j) := by
              simp only [etaT, qvec, map_sum, map_smul, map_sub]
            rw [e1]
            exact pow_le_pow_left₀ (norm_nonneg _) (norm_qvec_le ℓ F _) 2) (hw s)).trans he)
      rwa [hb] at h'
    | true =>
      simp only [ports_true]
      obtain ⟨n, hn'⟩ : ∃ n, bud true = n + 1 := ⟨bud true - 1, by omega⟩
      have hb : Function.update bud true (bud true - 1) true = n := by simp [hn']
      obtain ⟨c1, c2, c3⟩ := rows_query_step p hp0 hp1 r hr hpr row G h
        (stdOracle X Y (E' × Unit)) (splitIso ℓ) (joinIso X Y E') ψ φ hφ hm0 hx0 he0 hm hx he
      have h' := ih () _ (hk ()) (fun s ↦ qvec ℓ (Hw G h s) (ψ s))
        (fun s j ↦ qvec ℓ (Hw G h (clean row j s)) (φ s j))
        (fun s j ↦ by rw [clean_clean, ← hφ]) m (xx + 3 * r * (m + xx))
        (e + 3 * r ^ 2 * (m + xx) + 2 * r * xx) hm0 (by positivity) (by positivity) c1 c2 c3
      rw [hb] at h'
      rw [hn']
      exact h'

end Program

/-! ## The target-count-free bound -/

section Final

/-- An empty event has weight zero. -/
theorem gv_empty {A : Type*} [Fintype A] [DecidableEq A] {ι : Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] (q : DSubInstrument A ι B) (E : ι → Prop) (hE : ∀ i, ¬ E i)
    (v : EuclideanSpace ℂ A) : gv q E v = 0 := by
  have : IsEmpty {i // E i} := ⟨fun c ↦ hE c.1 c.2⟩
  rw [gv, DW_re, tsum_empty]

/-- Disjoint leaf events have total weight at most the squared norm of the input. -/
theorem gv_sum_disjoint_le {A : Type*} [Fintype A] [DecidableEq A] {ι J : Type*} [Fintype J]
    {B : ι → Type*} [∀ i, Fintype (B i)] (q : DSubInstrument A ι B) (Ev : J → ι → Prop)
    (hdisj : ∀ i j l, Ev i l → Ev j l → i = j) (v : EuclideanSpace ℂ A) :
    ∑ j, gv q (Ev j) v ≤ ‖v‖ ^ 2 := by
  classical
  have hσ := posSemidef_ketBra_self v
  have hs := q.isCPTNIFamily.summable_trace_re_apply hσ
  have hnn : ∀ i, 0 ≤ (q.branch i (ketBra v v)).trace.re := fun i ↦
    q.trace_re_branch_apply_nonneg i hσ
  have e : ∀ j, gv q (Ev j) v =
      ∑' i, Set.indicator {i | Ev j i} (fun i ↦ (q.branch i (ketBra v v)).trace.re) i := by
    intro j
    rw [gv, DW_re]
    exact tsum_subtype {i | Ev j i} fun i ↦ (q.branch i (ketBra v v)).trace.re
  simp only [e]
  rw [← Summable.tsum_finsetSum fun j _ ↦ hs.indicator _]
  refine le_trans (Summable.tsum_le_tsum (fun i ↦ ?_)
    (summable_sum fun j _ ↦ hs.indicator _) hs)
    ((q.tsum_trace_re_le hσ).trans (le_of_eq (trace_re_ketBra_self v)))
  by_cases hex : ∃ j0, Ev j0 i
  · obtain ⟨j0, hj0⟩ := hex
    rw [Finset.sum_eq_single j0]
    · simp [hj0]
    · intro j _ hne
      have : ¬ Ev j i := fun hj ↦ hne (hdisj j j0 i hj hj0)
      simp [this]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · have : ∀ j, ¬ Ev j i := fun j hj ↦ hex ⟨j, hj⟩
    simp [this, hnn i]

variable {X Y J : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype J] [DecidableEq J] {L : LocalSig.{u, v}} {W : QReg → Type w}
  (p : X → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (r : ℝ) (hr : 0 ≤ r)
  (hpr : ∀ k, p k ≤ r ^ 2) (row : X → J) (G h F : X → Y) (I : L.Interp)
  (Ev : J → (Σ u, W u) → Prop) (hdisj : ∀ i j l, Ev i l → Ev j l → i = j)

/-- The row `j` carries no mark. -/
def rowClean (j : J) (s : X → Bool) : Prop := ∀ k, row k = j → s k = false

instance (j : J) (s : X → Bool) : Decidable (rowClean row j s) := by
  unfold rowClean
  infer_instance

/-- The probability that the row `j` carries no mark. -/
noncomputable def gam (j : J) : ℝ := ∑ s, bw p s * (if rowClean row j s then (1 : ℝ) else 0)

include hp0 hp1 in
theorem gam_nonneg (j : J) : 0 ≤ gam p row j :=
  Finset.sum_nonneg fun s _ ↦ mul_nonneg (bw_nonneg p hp0 hp1 s) (by split_ifs <;> norm_num)

include hp0 hp1 in
theorem gam_le_one (j : J) : gam p row j ≤ 1 := by
  rw [← sum_bw p]
  exact Finset.sum_le_sum fun s _ ↦ by
    have := bw_nonneg p hp0 hp1 s
    split_ifs <;> nlinarith

theorem clean_of_rowClean {j : J} {s : X → Bool} (hs : rowClean row j s) : clean row j s = s := by
  funext k
  by_cases hk : row k = j
  · simp [clean, hk, hs k hk]
  · simp [clean, hk]

/-- **Independence**: whether the row `j` is clean is independent of the rest of the pattern. -/
theorem sum_bw_rowClean (j : J) (g : (X → Bool) → ℝ) :
    ∑ s, bw p s * ((if rowClean row j s then (1 : ℝ) else 0) * g (clean row j s)) =
      gam p row j * ∑ s, bw p s * g (clean row j s) := by
  rw [← sum_bw_mix p row j fun t ↦ (if rowClean row j t then (1 : ℝ) else 0) * g (clean row j t),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have e : ∀ s', (if rowClean row j (mix row j s s') then (1 : ℝ) else 0) *
      g (clean row j (mix row j s s')) =
      (if rowClean row j s' then (1 : ℝ) else 0) * g (clean row j s) := by
    intro s'
    rw [clean_mix]
    have : rowClean row j (mix row j s s') ↔ rowClean row j s' :=
      forall_congr' fun k ↦ imp_congr_right fun hk ↦ by rw [mix_of_row row hk]
    simp only [this]
  simp only [e]
  rw [gam, Finset.sum_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s' _ ↦ by ring

include hp0 hp1 hr hpr hdisj in
/-- **Target-count-free bound, pure input.**  Independent point marks with probabilities
`p k ≤ r²`; the marked points take the value `h`, the others `G`; `Ev j` are pairwise disjoint
leaf events ("the output names the row `j`").  Then the signed sum over the rows of the
probabilities of `Ev j`, with sign `+` when the row `j` is clean and `−` otherwise, is at most
`(g + 168 q² r²) ‖v‖²`, where `2 γ_j − 1 ≤ g` for every row, `γ_j` the probability that the row
`j` is clean, and `q` the number of calls of port `true` — whatever the number of rows. -/
theorem rows_adv_vec_le {A : QReg} (x : QuantumComp L (qrom2Spec X Y) W A) (bud : Bool → ℕ)
    (hx : x.IsQueryBound bud) (v : EuclideanSpace ℂ (A × Unit)) (g : ℝ) (hg0 : 0 ≤ g)
    (hg : ∀ j, (∃ l, Ev j l) → 2 * gam p row j - 1 ≤ g) :
    ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
        pvP I F (Hw G h s) x (Ev j) v ≤
      (g + 168 * ((bud true : ℕ) : ℝ) ^ 2 * r ^ 2) * ‖v‖ ^ 2 := by
  have hw := bw_nonneg p hp0 hp1
  have hpv0 : ∀ H j, 0 ≤ pvP I F H x (Ev j) v := fun H j ↦ gv_nonneg _ _ _
  have hpvsum : ∀ H, ∑ j, pvP I F H x (Ev j) v ≤ ‖v‖ ^ 2 := fun H ↦
    gv_sum_disjoint_le (runP I F H x) Ev hdisj v
  have hBtot : ∑ s, bw p s * ∑ j, pvP I F (Hw G h s) x (Ev j) v ≤ ‖v‖ ^ 2 := by
    calc _ ≤ ∑ s, bw p s * ‖v‖ ^ 2 :=
          Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hpvsum _) (hw s)
      _ = _ := by rw [← Finset.sum_mul, sum_bw, one_mul]
  have hq2 : (0 : ℝ) ≤ 168 * ((bud true : ℕ) : ℝ) ^ 2 * r ^ 2 := by positivity
  by_cases hsmall : 6 * r * (bud true : ℕ) ≤ 1
  swap
  · -- trivial regime
    have h36 : 1 < 36 * ((bud true : ℕ) : ℝ) ^ 2 * r ^ 2 := by
      have h1 : 1 < 6 * r * (bud true : ℕ) := lt_of_not_ge hsmall
      nlinarith
    have hle : ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
        pvP I F (Hw G h s) x (Ev j) v ≤ ∑ s, bw p s * ∑ j, pvP I F (Hw G h s) x (Ev j) v :=
      Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ ↦ by
          have := hpv0 (Hw G h s) j
          split_ifs <;> nlinarith) (hw s)
    have hv := sq_nonneg ‖v‖
    nlinarith [hle, hBtot, mul_nonneg hg0 hv]
  -- main regime
  have hLam := Lam_le p hp0 hp1 r hr hpr row G h F I Ev hdisj (gam p row)
    (gam_nonneg p hp0 hp1 row) (gam_le_one p hp0 hp1 row) x bud hx (fun _ ↦ v) (fun _ _ ↦ v)
    (fun _ _ ↦ rfl) ‖v‖ 0 0 (norm_nonneg _) le_rfl le_rfl
    (by rw [← Finset.sum_mul, sum_bw, one_mul])
    (by simp) (by simp [etaT])
  have hPot := Pot_le hr (bud true) hsmall (norm_nonneg v)
  have hL := (abs_le.1 (hLam.trans hPot)).2
  -- decomposition
  have hA : ∀ j, ∑ s, bw p s * ((if rowClean row j s then (1 : ℝ) else 0) *
      pvP I F (Hw G h s) x (Ev j) v) =
      gam p row j * ∑ s, bw p s * pvP I F (Hw G h (clean row j s)) x (Ev j) v := by
    intro j
    rw [← sum_bw_rowClean p row j fun t ↦ pvP I F (Hw G h t) x (Ev j) v]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases hs : rowClean row j s
    · rw [clean_of_rowClean row hs]
    · simp [hs]
  have hdecomp : ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
      pvP I F (Hw G h s) x (Ev j) v =
      ∑ j, (2 * gam p row j - 1) * ∑ s, bw p s * pvP I F (Hw G h s) x (Ev j) v +
        2 * Lam p row G h F I Ev (gam p row) x (fun _ ↦ v) (fun _ _ ↦ v) := by
    have e1 : ∀ s j, (if rowClean row j s then (1 : ℝ) else -1) * pvP I F (Hw G h s) x (Ev j) v =
        2 * ((if rowClean row j s then (1 : ℝ) else 0) * pvP I F (Hw G h s) x (Ev j) v) -
          pvP I F (Hw G h s) x (Ev j) v := by
      intro s j
      split_ifs <;> ring
    have e2 : ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
        pvP I F (Hw G h s) x (Ev j) v =
        ∑ j, (2 * (gam p row j * ∑ s, bw p s * pvP I F (Hw G h (clean row j s)) x (Ev j) v) -
          ∑ s, bw p s * pvP I F (Hw G h s) x (Ev j) v) := by
      simp only [e1]
      rw [← swap_sum_one p]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← hA j, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ ↦ by ring
    have e3 : Lam p row G h F I Ev (gam p row) x (fun _ ↦ v) (fun _ _ ↦ v) =
        ∑ j, gam p row j * (∑ s, bw p s * pvP I F (Hw G h (clean row j s)) x (Ev j) v -
          ∑ s, bw p s * pvP I F (Hw G h s) x (Ev j) v) := by
      unfold Lam
      rw [← swap_sum_one p]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ ↦ by ring
    rw [e2, e3, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hB0 : ∀ j, 0 ≤ ∑ s, bw p s * pvP I F (Hw G h s) x (Ev j) v := fun j ↦
    Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (hpv0 _ j)
  have hfirst : ∑ j, (2 * gam p row j - 1) * ∑ s, bw p s * pvP I F (Hw G h s) x (Ev j) v ≤
      g * ‖v‖ ^ 2 := by
    calc _ ≤ ∑ j, g * ∑ s, bw p s * pvP I F (Hw G h s) x (Ev j) v :=
          Finset.sum_le_sum fun j _ ↦ by
            by_cases hne : ∃ l, Ev j l
            · exact mul_le_mul_of_nonneg_right (hg j hne) (hB0 j)
            · have hz : ∀ s, pvP I F (Hw G h s) x (Ev j) v = 0 := fun s ↦
                gv_empty _ _ (fun l hl ↦ hne ⟨l, hl⟩) v
              simp [hz]
      _ = g * ∑ s, bw p s * ∑ j, pvP I F (Hw G h s) x (Ev j) v := by
          rw [← Finset.mul_sum, swap_sum_one p]
      _ ≤ _ := mul_le_mul_of_nonneg_left hBtot hg0
  rw [hdecomp]
  nlinarith [hfirst, hL]

include hp0 hp1 hr hpr hdisj in
/-- **Target-count-free bound** for a second-port program run from an arbitrary positive
semidefinite (unnormalised) joint operator. -/
theorem rows_adv_le {A : QReg} (x : QuantumComp L (qrom2Spec X Y) W A) (bud : Bool → ℕ)
    (hx : x.IsQueryBound bud) {σ : Matrix (A × Unit) (A × Unit) ℂ} (hσ : σ.PosSemidef) (g : ℝ)
    (hg0 : 0 ≤ g) (hg : ∀ j, (∃ l, Ev j l) → 2 * gam p row j - 1 ≤ g) :
    ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
        (leafProb (twoRuntime (ports F (Hw G h s))) I x σ (Ev j)).toReal ≤
      (g + 168 * ((bud true : ℕ) : ℝ) ^ 2 * r ^ 2) * σ.trace.re := by
  obtain ⟨vs, hvs⟩ := exists_ketBra_sum hσ
  have hnorm : ∑ i, ‖vs i‖ ^ 2 = σ.trace.re := by
    conv_rhs => rw [hvs]
    rw [Matrix.trace_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (trace_re_ketBra_self _).symm
  have hq : ∀ (H : X → Y) (j : J),
      (leafProb (twoRuntime (ports F H)) I x σ (Ev j)).toReal =
        ∑ i, pvP I F H x (Ev j) (vs i) := fun H j ↦ by
    rw [leafProbPorts_toReal_eq_DW I F H x hσ]
    conv_lhs => rw [hvs]
    rw [map_sum, Complex.re_sum]
    rfl
  have e : ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
      (leafProb (twoRuntime (ports F (Hw G h s))) I x σ (Ev j)).toReal =
      ∑ i, ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
        pvP I F (Hw G h s) x (Ev j) (vs i) := by
    simp only [hq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]
  rw [e, ← hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    rows_adv_vec_le p hp0 hp1 r hr hpr row G h F I Ev hdisj x bud hx (vs i) g hg0 hg

end Final

end PQ.QROM.Rows

#print axioms PQ.QROM.Rows.Lam_le
#print axioms PQ.QROM.Rows.rows_adv_le
