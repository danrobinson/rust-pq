import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A tight (second-order) quantum-query distinguishing bound in the pure-state circuit model

The one-way-to-hiding bounds of `PQ/QROM/Distinguish.lean` are of order `q √ε`.  Here we prove,
in an elementary vector model, the second-order bound `8 q² ε` for the *averaged* acceptance
probability when the real oracle differs from a hybrid oracle `G` only on a hidden set that
contains each point with probability at most `ε`.

## The model

* `OracleInterface X Y E`: a complex inner product space `E`, "query input is `k`" operators
  `P k` with pairwise orthogonal ranges and `∑ k, ‖P k φ‖² ≤ ‖φ‖²`, and for every function
  `H : X → Y` a contraction `O H` such that the difference `O H - O G` is block diagonal
  (`diff_comm`), decomposes over the blocks (`diff_sum`), vanishes on the blocks where `H` and `G`
  agree (`local`) and has norm at most `2` on each block (`diff_le`).  The standard oracle
  `U_H ⊗ 1` on `X × Y × workspace` is an instance (`PQ/QROM/TightOracle.lean`).
* `QAlg E`: an initial vector of norm at most one and contractions `U 0, U 1, …` (unitaries
  included).  `A.state I H t` is the state `U_t O_H U_{t-1} … O_H U_0 ψ` after `t` queries, and
  `A.acc I q Q H = ‖Q (A.state I H q)‖²` the acceptance probability of the `q`-query circuit with
  final contraction `Q` (e.g. an orthogonal projection).

## Main results

* `tight_avg`: for weights `w s ≥ 0` (not necessarily normalised), real functions `Hs s`, marked
  sets `S s ⊇ {k | Hs s k ≠ G k}` with `∑_{s : k ∈ S s} w s ≤ ε` for every `k`:
  `|∑ s, w s * acc (Hs s) - (∑ s, w s) * acc G| ≤ 8 q² ε`.
* `tight_view`: the version with a view: worlds `ω` with weights `w ω`, the algorithm, the final
  operator and the hybrid function depend on `view ω`; the marked set is `ε`-hidden given the
  view; an additional view-independent selector `c ω ∈ [0, 1]` is allowed (used for DSPR).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PQ.QROM.Tight

variable {X Y E : Type*} [Fintype X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Pythagoras for a finite pairwise orthogonal family. -/
theorem norm_sq_sum_orth (u : X → E) (h : ∀ k l, k ≠ l → inner ℂ (u k) (u l) = 0) :
    ‖∑ k, u k‖ ^ 2 = ∑ k, ‖u k‖ ^ 2 := by
  classical
  have e : inner ℂ (∑ k, u k) (∑ k, u k) = ∑ k, inner ℂ (u k) (u k) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [inner_sum]
    exact Finset.sum_eq_single k (fun l _ hl ↦ h k l hl.symm) (by simp)
  have e2 := congrArg Complex.re e
  rw [Complex.re_sum] at e2
  have h1 : ∀ x : E, (inner ℂ x x).re = ‖x‖ ^ 2 := fun x ↦ by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) x
    simpa using this
  simpa only [h1] using e2

/-- The oracle interface of the pure-state circuit model. -/
structure OracleInterface (X Y E : Type*) [Fintype X] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] where
  /-- "The query input is `k`". -/
  P : X → E →L[ℂ] E
  /-- The oracle operator of a function. -/
  O : (X → Y) → E →L[ℂ] E
  O_le : ∀ H φ, ‖O H φ‖ ≤ ‖φ‖
  P_orth : ∀ k l, k ≠ l → ∀ φ ψ, inner ℂ (P k φ) (P l ψ) = 0
  P_sum_le : ∀ φ, ∑ k, ‖P k φ‖ ^ 2 ≤ ‖φ‖ ^ 2
  /-- The difference of two oracle operators decomposes over the blocks. -/
  diff_sum : ∀ H G φ, O H φ - O G φ = ∑ k, (O H (P k φ) - O G (P k φ))
  /-- The oracle operator on block `k` only depends on the value at `k`. -/
  «local» : ∀ H G k, H k = G k → ∀ φ, O H (P k φ) = O G (P k φ)
  /-- The difference of two oracle operators is block diagonal. -/
  diff_comm : ∀ H G k φ, P k (O H φ - O G φ) = O H (P k φ) - O G (P k φ)
  diff_le : ∀ H G k φ, ‖O H (P k φ) - O G (P k φ)‖ ≤ 2 * ‖P k φ‖

namespace OracleInterface

variable (I : OracleInterface X Y E)

/-- The difference `O H - O G`, applied to a vector. -/
def D (H G : X → Y) (φ : E) : E := I.O H φ - I.O G φ

theorem D_add (H G : X → Y) (φ ψ : E) : I.D H G (φ + ψ) = I.D H G φ + I.D H G ψ := by
  simp only [D, map_add]; abel

theorem sum_P_D (H G : X → Y) (φ : E) : ∑ k, I.P k (I.D H G φ) = I.D H G φ := by
  simp only [D, I.diff_comm]
  exact (I.diff_sum H G φ).symm

theorem P_D_orth (H G : X → Y) (φ : E) (k l : X) (h : k ≠ l) :
    inner ℂ (I.P k (I.D H G φ)) (I.P l (I.D H G φ)) = 0 := I.P_orth k l h _ _

/-- **First-order operator bound.** `‖(O H - O G) φ‖² ≤ 4 ∑_{k ∈ S} ‖P k φ‖²` whenever `H` and
`G` agree outside `S`. -/
theorem norm_D_sq_le [DecidableEq X] (H G : X → Y) (S : Finset X)
    (hS : ∀ k, H k ≠ G k → k ∈ S) (φ : E) :
    ‖I.D H G φ‖ ^ 2 ≤ 4 * ∑ k ∈ S, ‖I.P k φ‖ ^ 2 := by
  classical
  rw [← I.sum_P_D H G φ, norm_sq_sum_orth _ (I.P_D_orth H G φ), Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not univ (· ∈ S)]
  have h0 : ∑ k ∈ univ.filter (fun k ↦ ¬ k ∈ S), ‖I.P k (I.D H G φ)‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk' : H k = G k := by
      by_contra hne
      exact (Finset.mem_filter.1 hk).2 (hS k hne)
    rw [D, I.diff_comm, I.local H G k hk', sub_self]
    simp
  rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rw [D, I.diff_comm]
  have := I.diff_le H G k φ
  nlinarith [norm_nonneg (I.O H (I.P k φ) - I.O G (I.P k φ)), norm_nonneg (I.P k φ)]

end OracleInterface

section Avg

variable [DecidableEq X] (I : OracleInterface X Y E) {ι : Type*} [Fintype ι]
  (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (Hs : ι → X → Y) (G : X → Y) (S : ι → Finset X)
  (hS : ∀ s k, Hs s k ≠ G k → k ∈ S s)

include hw hS

/-- Block-diagonal estimate for the averaged difference operator. -/
theorem norm_avg_D_sq_le (a : ι → E) :
    ‖∑ s, (w s : ℂ) • I.D (Hs s) G (a s)‖ ^ 2 ≤
      4 * ∑ k, (∑ s with k ∈ S s, w s * ‖I.P k (a s)‖) ^ 2 := by
  classical
  set v : E := ∑ s, (w s : ℂ) • I.D (Hs s) G (a s) with hv
  have hPv : ∀ k, I.P k v = ∑ s, (w s : ℂ) • I.P k (I.D (Hs s) G (a s)) := by
    intro k
    rw [hv, map_sum]
    exact Finset.sum_congr rfl fun s _ ↦ map_smul _ _ _
  have hsum : ∑ k, I.P k v = v := by
    simp only [hPv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← Finset.smul_sum, I.sum_P_D]
  have horth : ∀ k l, k ≠ l → inner ℂ (I.P k v) (I.P l v) = 0 := fun k l h ↦ I.P_orth k l h _ _
  rw [← hsum, norm_sq_sum_orth _ horth, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hk : ‖I.P k v‖ ≤ 2 * ∑ s with k ∈ S s, w s * ‖I.P k (a s)‖ := by
    rw [hPv k, Finset.mul_sum, Finset.sum_filter]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hw s), OracleInterface.D, I.diff_comm]
    split_ifs with hks
    · have := I.diff_le (Hs s) G k (a s)
      nlinarith [hw s]
    · have hk' : Hs s k = G k := by
        by_contra hne
        exact hks (hS s k hne)
      rw [I.local _ _ k hk', sub_self, norm_zero, mul_zero]
  have h0 : 0 ≤ ∑ s with k ∈ S s, w s * ‖I.P k (a s)‖ :=
    Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (norm_nonneg _)
  nlinarith [norm_nonneg (I.P k v)]

variable (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ∀ k, ∑ s with k ∈ S s, w s ≤ ε)

include hε0 hε

/-- **Averaged operator bound, varying vectors.**
`‖∑_s w_s (O_{H_s} - O_G) a_s‖² ≤ 4 ε ∑_s w_s ‖a_s‖²`. -/
theorem norm_avg_D_sq_le_var (a : ι → E) :
    ‖∑ s, (w s : ℂ) • I.D (Hs s) G (a s)‖ ^ 2 ≤ 4 * ε * ∑ s, w s * ‖a s‖ ^ 2 := by
  classical
  refine (norm_avg_D_sq_le I w hw Hs G S hS a).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ k, (∑ s with k ∈ S s, w s * ‖I.P k (a s)‖) ^ 2
      ≤ ∑ k, ε * ∑ s, w s * ‖I.P k (a s)‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ.filter fun s ↦ k ∈ S s)
          (r := fun s ↦ w s * ‖I.P k (a s)‖) (f := fun s ↦ w s)
          (g := fun s ↦ w s * ‖I.P k (a s)‖ ^ 2) (fun s _ ↦ hw s)
          (fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _)) (fun s _ ↦ le_of_eq (by ring))
        have hnn : 0 ≤ ∑ s with k ∈ S s, w s * ‖I.P k (a s)‖ ^ 2 :=
          Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _)
        have hsub : ∑ s with k ∈ S s, w s * ‖I.P k (a s)‖ ^ 2 ≤ ∑ s, w s * ‖I.P k (a s)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun s _ _ ↦ mul_nonneg (hw s) (sq_nonneg _)
        calc _ ≤ _ := hcs
          _ ≤ ε * ∑ s with k ∈ S s, w s * ‖I.P k (a s)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hε k) hnn
          _ ≤ _ := mul_le_mul_of_nonneg_left hsub
            ((Finset.sum_nonneg fun s _ ↦ hw s).trans (hε k))
    _ = ε * ∑ s, w s * ∑ k, ‖I.P k (a s)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ ε * ∑ s, w s * ‖a s‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (I.P_sum_le _) (hw s)) hε0

/-- **Averaged operator bound, fixed vector.** `‖∑_s w_s (O_{H_s} - O_G) φ‖ ≤ 2 ε ‖φ‖`. -/
theorem norm_avg_D_le_fixed (φ : E) :
    ‖∑ s, (w s : ℂ) • I.D (Hs s) G φ‖ ≤ 2 * ε * ‖φ‖ := by
  classical
  have h := norm_avg_D_sq_le I w hw Hs G S hS fun _ ↦ φ
  have h2 : ∑ k, (∑ s with k ∈ S s, w s * ‖I.P k φ‖) ^ 2 ≤ ε ^ 2 * ‖φ‖ ^ 2 := by
    calc ∑ k, (∑ s with k ∈ S s, w s * ‖I.P k φ‖) ^ 2
        ≤ ∑ k, ε ^ 2 * ‖I.P k φ‖ ^ 2 := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          rw [← Finset.sum_mul, mul_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (Finset.sum_nonneg fun s _ ↦ hw s) (hε k) 2) (sq_nonneg _)
      _ ≤ _ := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (I.P_sum_le φ) (sq_nonneg _)
  have h3 : ‖∑ s, (w s : ℂ) • I.D (Hs s) G φ‖ ^ 2 ≤ (2 * ε * ‖φ‖) ^ 2 := by
    calc _ ≤ _ := h
      _ ≤ 4 * (ε ^ 2 * ‖φ‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := by ring
  exact le_of_sq_le_sq h3 (by positivity)

/-- The averaged squared mass on the marked sets is at most `ε`. -/
theorem sum_marked_mass_le (φ : E) :
    ∑ s, w s * ∑ k ∈ S s, ‖I.P k φ‖ ^ 2 ≤ ε * ‖φ‖ ^ 2 := by
  classical
  calc ∑ s, w s * ∑ k ∈ S s, ‖I.P k φ‖ ^ 2
      = ∑ k, (∑ s with k ∈ S s, w s) * ‖I.P k φ‖ ^ 2 := by
        have : ∀ s, w s * ∑ k ∈ S s, ‖I.P k φ‖ ^ 2 =
            ∑ k, if k ∈ S s then w s * ‖I.P k φ‖ ^ 2 else 0 := fun s ↦ by
          rw [Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
        simp only [this]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.sum_mul, Finset.sum_filter]
    _ ≤ ∑ k, ε * ‖I.P k φ‖ ^ 2 :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (hε k) (sq_nonneg _)
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (I.P_sum_le φ) hε0

end Avg

/-! ### Algorithms -/

/-- A query algorithm in the pure-state circuit model: an initial vector and contractions
`U 0, U 1, …` interleaved with the oracle. -/
structure QAlg (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  init : E
  init_le : ‖init‖ ≤ 1
  U : ℕ → E →L[ℂ] E
  U_le : ∀ t φ, ‖U t φ‖ ≤ ‖φ‖

namespace QAlg

variable (A : QAlg E) (I : OracleInterface X Y E)

/-- The state after `t` queries: `U_t O_H U_{t-1} … O_H U_0 ψ`. -/
def state (H : X → Y) : ℕ → E
  | 0 => A.U 0 A.init
  | t + 1 => A.U (t + 1) (I.O H (state H t))

/-- Acceptance probability of the `q`-query circuit with final operator `Q`. -/
def acc (q : ℕ) (Q : E →L[ℂ] E) (H : X → Y) : ℝ := ‖Q (A.state I H q)‖ ^ 2

theorem norm_state_le (H : X → Y) (t : ℕ) : ‖A.state I H t‖ ≤ 1 := by
  induction t with
  | zero => exact (A.U_le 0 _).trans A.init_le
  | succ t ih => exact (A.U_le _ _).trans ((I.O_le H _).trans ih)

theorem acc_nonneg (q : ℕ) (Q : E →L[ℂ] E) (H : X → Y) : 0 ≤ A.acc I q Q H := sq_nonneg _

theorem acc_le_one (q : ℕ) (Q : E →L[ℂ] E) (hQ : ∀ φ, ‖Q φ‖ ≤ ‖φ‖) (H : X → Y) :
    A.acc I q Q H ≤ 1 := by
  have h := (hQ (A.state I H q)).trans (A.norm_state_le I H q)
  have h0 := norm_nonneg (Q (A.state I H q))
  unfold acc
  nlinarith

/-- Complementary final operators give probabilities summing to at most one. -/
theorem acc_add_le_one (q : ℕ) (Q₀ Q₁ : E →L[ℂ] E)
    (hQ : ∀ φ, ‖Q₀ φ‖ ^ 2 + ‖Q₁ φ‖ ^ 2 ≤ ‖φ‖ ^ 2) (H : X → Y) :
    A.acc I q Q₀ H + A.acc I q Q₁ H ≤ 1 := by
  have h := A.norm_state_le I H q
  have h0 := norm_nonneg (A.state I H q)
  have := hQ (A.state I H q)
  unfold acc
  nlinarith

/-- **First-order (BBBV) bound.** -/
theorem norm_state_sub_le (H G : X → Y) (t : ℕ) :
    ‖A.state I H t - A.state I G t‖ ≤ ∑ j ∈ range t, ‖I.D H G (A.state I G j)‖ := by
  induction t with
  | zero => simp [state]
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have e : A.state I H (t + 1) - A.state I G (t + 1) =
        A.U (t + 1) (I.O H (A.state I H t - A.state I G t) + I.D H G (A.state I G t)) := by
      simp only [state, OracleInterface.D, map_sub, map_add]
      abel
    rw [e]
    refine (A.U_le _ _).trans ((norm_add_le _ _).trans ?_)
    exact add_le_add ((I.O_le H _).trans ih) le_rfl

end QAlg

/-! ### The second-order bound -/

section Main

variable [DecidableEq X] (I : OracleInterface X Y E) (A : QAlg E) {ι : Type*} [Fintype ι]
  (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (Hs : ι → X → Y) (G : X → Y) (S : ι → Finset X)
  (hS : ∀ s k, Hs s k ≠ G k → k ∈ S s) (ε : ℝ) (hε0 : 0 ≤ ε)
  (hε : ∀ k, ∑ s with k ∈ S s, w s ≤ ε)

include hw hS hε0 hε

/-- (a) The averaged squared first-order deviation is at most `4 t² ε`. -/
theorem sum_norm_state_sub_sq_le (t : ℕ) :
    ∑ s, w s * ‖A.state I (Hs s) t - A.state I G t‖ ^ 2 ≤ 4 * (t : ℝ) ^ 2 * ε := by
  classical
  have h1 : ∀ s, ‖A.state I (Hs s) t - A.state I G t‖ ^ 2 ≤
      t * ∑ j ∈ range t, 4 * ∑ k ∈ S s, ‖I.P k (A.state I G j)‖ ^ 2 := by
    intro s
    calc ‖A.state I (Hs s) t - A.state I G t‖ ^ 2
        ≤ (∑ j ∈ range t, ‖I.D (Hs s) G (A.state I G j)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (A.norm_state_sub_le I (Hs s) G t) 2
      _ ≤ (range t).card * ∑ j ∈ range t, ‖I.D (Hs s) G (A.state I G j)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ _ := by
          rw [Finset.card_range]
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ ↦ I.norm_D_sq_le (Hs s) G (S s) (hS s) _)
            (Nat.cast_nonneg t)
  calc ∑ s, w s * ‖A.state I (Hs s) t - A.state I G t‖ ^ 2
      ≤ ∑ s, w s * (t * ∑ j ∈ range t, 4 * ∑ k ∈ S s, ‖I.P k (A.state I G j)‖ ^ 2) :=
        Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (h1 s) (hw s)
    _ = 4 * t * ∑ j ∈ range t, ∑ s, w s * ∑ k ∈ S s, ‖I.P k (A.state I G j)‖ ^ 2 := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ 4 * t * ∑ j ∈ range t, ε * 1 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ ?_) (by positivity)
        refine (sum_marked_mass_le I w hw Hs G S hS ε hε0 hε _).trans
          (mul_le_mul_of_nonneg_left ?_ hε0)
        have := A.norm_state_le I G j
        nlinarith [norm_nonneg (A.state I G j)]
    _ = _ := by
        simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- (c) The averaged deviation is of second order: `‖∑_s w_s (ψ^s_t - ψ⁰_t)‖ ≤ 2 t² ε`. -/
theorem norm_avg_state_sub_le (t : ℕ) :
    ‖∑ s, (w s : ℂ) • (A.state I (Hs s) t - A.state I G t)‖ ≤ 2 * (t : ℝ) ^ 2 * ε := by
  classical
  induction t with
  | zero => simp [QAlg.state]
  | succ t ih =>
    have e : ∑ s, (w s : ℂ) • (A.state I (Hs s) (t + 1) - A.state I G (t + 1)) =
        A.U (t + 1) (I.O G (∑ s, (w s : ℂ) • (A.state I (Hs s) t - A.state I G t)) +
          ∑ s, (w s : ℂ) • I.D (Hs s) G (A.state I G t) +
          ∑ s, (w s : ℂ) • I.D (Hs s) G (A.state I (Hs s) t - A.state I G t)) := by
      rw [map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, map_sum]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [map_smul, ← smul_add, ← smul_add, map_smul]
      congr 1
      simp only [QAlg.state, OracleInterface.D, map_sub, map_add]
      abel
    rw [e]
    have hfix := norm_avg_D_le_fixed I w hw Hs G S hS ε hε0 hε (A.state I G t)
    have hvar : ‖∑ s, (w s : ℂ) • I.D (Hs s) G (A.state I (Hs s) t - A.state I G t)‖ ≤
        4 * t * ε := by
      have h := norm_avg_D_sq_le_var I w hw Hs G S hS ε hε0 hε
        fun s ↦ A.state I (Hs s) t - A.state I G t
      have h2 := sum_norm_state_sub_sq_le I A w hw Hs G S hS ε hε0 hε t
      have h3 : ‖∑ s, (w s : ℂ) • I.D (Hs s) G (A.state I (Hs s) t - A.state I G t)‖ ^ 2 ≤
          (4 * t * ε) ^ 2 := by
        calc _ ≤ _ := h
          _ ≤ 4 * ε * (4 * (t : ℝ) ^ 2 * ε) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := by ring
      exact le_of_sq_le_sq h3 (by positivity)
    have hO := (I.O_le G _).trans ih
    have hst := A.norm_state_le I G t
    have hst0 := norm_nonneg (A.state I G t)
    refine (A.U_le _ _).trans ((norm_add_le _ _).trans ?_)
    have h12 := norm_add_le (I.O G (∑ s, (w s : ℂ) • (A.state I (Hs s) t - A.state I G t)))
      (∑ s, (w s : ℂ) • I.D (Hs s) G (A.state I G t))
    push_cast
    nlinarith

/-- **Tight hidden-set bound (second order).**  If the functions `Hs s` differ from `G` only on
marked sets `S s` that contain every point with total weight at most `ε`, then the `w`-averaged
acceptance probability against `Hs s` differs from the one against `G` by at most `8 q² ε`. -/
theorem tight_avg (q : ℕ) (Q : E →L[ℂ] E) (hQ : ∀ φ, ‖Q φ‖ ≤ ‖φ‖) :
    |∑ s, w s * A.acc I q Q (Hs s) - (∑ s, w s) * A.acc I q Q G| ≤ 8 * (q : ℝ) ^ 2 * ε := by
  classical
  set δ : E := ∑ s, (w s : ℂ) • (A.state I (Hs s) q - A.state I G q) with hδ
  have hterm : ∀ s, w s * A.acc I q Q (Hs s) = w s * A.acc I q Q G +
      (2 * (w s * (inner ℂ (Q (A.state I G q))
        (Q (A.state I (Hs s) q - A.state I G q))).re) +
        w s * ‖Q (A.state I (Hs s) q - A.state I G q)‖ ^ 2) := by
    intro s
    have e : Q (A.state I (Hs s) q) =
        Q (A.state I G q) + Q (A.state I (Hs s) q - A.state I G q) := by
      rw [← map_add]; congr 1; abel
    have h := norm_add_sq (𝕜 := ℂ) (Q (A.state I G q)) (Q (A.state I (Hs s) q - A.state I G q))
    simp only [RCLike.re_to_complex] at h
    unfold QAlg.acc
    rw [e, h]
    ring
  have hre : ∑ s, w s * (inner ℂ (Q (A.state I G q))
      (Q (A.state I (Hs s) q - A.state I G q))).re = (inner ℂ (Q (A.state I G q)) (Q δ)).re := by
    rw [hδ, map_sum, inner_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, inner_smul_right, Complex.re_ofReal_mul]
  have hsum : ∑ s, w s * A.acc I q Q (Hs s) - (∑ s, w s) * A.acc I q Q G =
      2 * (inner ℂ (Q (A.state I G q)) (Q δ)).re +
        ∑ s, w s * ‖Q (A.state I (Hs s) q - A.state I G q)‖ ^ 2 := by
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hre]
    ring
  have hδle : ‖δ‖ ≤ 2 * (q : ℝ) ^ 2 * ε :=
    norm_avg_state_sub_le I A w hw Hs G S hS ε hε0 hε q
  have h1 : |(inner ℂ (Q (A.state I G q)) (Q δ)).re| ≤ 2 * (q : ℝ) ^ 2 * ε := by
    refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    have ha : ‖Q (A.state I G q)‖ ≤ 1 := (hQ _).trans (A.norm_state_le I G q)
    have hb : ‖Q δ‖ ≤ 2 * (q : ℝ) ^ 2 * ε := (hQ _).trans hδle
    calc ‖Q (A.state I G q)‖ * ‖Q δ‖ ≤ 1 * (2 * (q : ℝ) ^ 2 * ε) :=
          mul_le_mul ha hb (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h2 : ∑ s, w s * ‖Q (A.state I (Hs s) q - A.state I G q)‖ ^ 2 ≤ 4 * (q : ℝ) ^ 2 * ε :=
    (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hQ _) 2) (hw s)).trans
      (sum_norm_state_sub_sq_le I A w hw Hs G S hS ε hε0 hε q)
  have h2' : 0 ≤ ∑ s, w s * ‖Q (A.state I (Hs s) q - A.state I G q)‖ ^ 2 :=
    Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _)
  rw [hsum, abs_le]
  have := abs_le.1 h1
  constructor <;> nlinarith

end Main

/-! ### The version with a view -/

section View

variable [DecidableEq X] (I : OracleInterface X Y E) {Ω V : Type*} [Fintype Ω] [Fintype V]
  [DecidableEq V]

/-- **Tight hidden-set bound with a view (second order).**  Worlds `ω` with weights `w ω ≥ 0`.
The algorithm `A v`, its final operator `Q v` and the hybrid function `Ghyb v` only depend on the
view `v = view ω`; the real function `Hreal ω` differs from the hybrid one only on the marked set
`S ω`, which is `ε`-hidden given the view: for every view `v` and point `k`,
`w {ω | view ω = v, k ∈ S ω} ≤ ε · w {ω | view ω = v}`.  `c ω ∈ [0, 1]` is an arbitrary selector
(take `c = 1` for plain distinguishing).  Then the real and hybrid acceptance probabilities differ
by at most `8 q² ε` times the total weight. -/
theorem tight_view (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω)
    (hc1 : ∀ ω, c ω ≤ 1) (view : Ω → V) (S : Ω → Finset X) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hH : ∀ v k, ∑ ω with view ω = v ∧ k ∈ S ω, w ω ≤ ε * ∑ ω with view ω = v, w ω)
    (A : V → QAlg E) (q : ℕ) (Q : V → E →L[ℂ] E) (hQ : ∀ v φ, ‖Q v φ‖ ≤ ‖φ‖)
    (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) :
    |∑ ω, w ω * c ω * (A (view ω)).acc I q (Q (view ω)) (Hreal ω) -
        ∑ ω, w ω * c ω * (A (view ω)).acc I q (Q (view ω)) (Ghyb (view ω))| ≤
      8 * (q : ℝ) ^ 2 * ε * ∑ ω, w ω := by
  classical
  have key : ∀ f : Ω → V → ℝ, ∑ ω, f ω (view ω) = ∑ v, ∑ ω, if view ω = v then f ω v else 0 := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp
  have hv : ∀ v, |(∑ ω, if view ω = v then w ω * c ω * (A v).acc I q (Q v) (Hreal ω) else 0) -
      ∑ ω, if view ω = v then w ω * c ω * (A v).acc I q (Q v) (Ghyb v) else 0| ≤
      8 * (q : ℝ) ^ 2 * (ε * ∑ ω with view ω = v, w ω) := by
    intro v
    have hμ : 0 ≤ ∑ ω with view ω = v, w ω := Finset.sum_nonneg fun ω _ ↦ hw ω
    have h := tight_avg I (A v) (fun ω ↦ if view ω = v then w ω * c ω else 0)
      (fun ω ↦ by split_ifs <;> [exact mul_nonneg (hw ω) (hc0 ω); exact le_rfl])
      (fun ω ↦ if view ω = v then Hreal ω else Ghyb v) (Ghyb v) S
      (fun ω k hne ↦ by
        by_cases hω : view ω = v
        · simp only [hω, ite_true] at hne
          exact hS ω k (by rw [hω]; exact hne)
        · simp [hω] at hne)
      (ε * ∑ ω with view ω = v, w ω) (mul_nonneg hε0 hμ)
      (fun k ↦ by
        refine le_trans ?_ (hH v k)
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_le_sum fun ω _ ↦ ?_
        by_cases h1 : view ω = v <;> by_cases h2 : k ∈ S ω <;> simp [h1, h2]
        nlinarith [hw ω, hc0 ω, hc1 ω])
      q (Q v) (hQ v)
    have e1 : ∑ ω, (if view ω = v then w ω * c ω else 0) *
        (A v).acc I q (Q v) (if view ω = v then Hreal ω else Ghyb v) =
        ∑ ω, if view ω = v then w ω * c ω * (A v).acc I q (Q v) (Hreal ω) else 0 :=
      Finset.sum_congr rfl fun ω _ ↦ by split_ifs <;> simp
    have e2 : (∑ ω, if view ω = v then w ω * c ω else 0) * (A v).acc I q (Q v) (Ghyb v) =
        ∑ ω, if view ω = v then w ω * c ω * (A v).acc I q (Q v) (Ghyb v) else 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ω _ ↦ by split_ifs <;> simp
    rw [e1, e2] at h
    exact h
  rw [key fun ω v ↦ w ω * c ω * (A v).acc I q (Q v) (Hreal ω),
    key fun ω v ↦ w ω * c ω * (A v).acc I q (Q v) (Ghyb v), ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun v _ ↦ hv v).trans ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_fiberwise]
  exact le_of_eq (by ring)

end View

end PQ.QROM.Tight

#print axioms PQ.QROM.Tight.tight_avg
#print axioms PQ.QROM.Tight.tight_view
#print axioms PQ.QROM.Tight.QAlg.acc_le_one
