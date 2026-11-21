import PQ.QROM.TightCore
import PQ.QROM.TightOracle
import PQ.QROM.Distinguish

/-!
# Tight (second-order) bounds for PRF, undetectability and DSPR of a random function

Instances of `Tight.tight_view` (`PQ/QROM/TightCore.lean`) with the couplings of
`PQ/QROM/Distinguish.lean`.  The bounds are `8 q² / size` instead of the one-way-to-hiding
`4 q / √size` proved there.  Adversaries are `q`-query circuits `QAlg` in the pure-state model
(contractions interleaved with the oracle of an arbitrary `OracleInterface`, e.g. the standard
`U_H ⊗ 1`, see `PQ/QROM/TightOracle.lean`); probabilities are real numbers, every experiment is an
explicit finite uniform average of acceptance probabilities `acc`.

* `prf_tight`: PRF with a hidden key, `|Pr_real - Pr_ideal| ≤ 8 q² / |K|`.
* `ud_tight`: multi-target undetectability (all tweaks, one hidden preimage per tweak; the circuit
  may depend on the targets), `|Pr_real - Pr_ideal| ≤ 8 q² / |Msg|`.
* `dspr_tight`: decisional second-preimage resistance,
  `Pr[b = SP] ≤ max (p, 1 - p) + 8 q² / |Y|`; `dspr_tight_adv`: the Bernstein–Hülsing advantage
  `max (0, Pr[b = SP] - p) ≤ 8 q² / |Y|` when `p = Pr[SP] ≥ 1/2`.
-/

open Finset ENNReal

set_option linter.unusedSectionVars false

namespace PQ.QROM.Tight

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### Real-valued helpers -/

theorem card_ne_zero_real (α : Type) [Fintype α] [Nonempty α] : (Fintype.card α : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem toReal_sum_ind {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∑ a, if p a then (1 : ℝ≥0∞) else 0).toReal = ∑ a, if p a then (1 : ℝ) else 0 := by
  rw [ENNReal.toReal_sum fun a _ ↦ by split_ifs <;> simp]
  exact Finset.sum_congr rfl fun a _ ↦ by split_ifs <;> simp

/-- Worlds `(a, v)` with `a` uniform and independent of the view `v`: real-valued version of
`hidden_indep`, in the form needed by `tight_view`. -/
theorem hidden_indep_real {A V X : Type} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq X]
    (κ ε : ℝ) (hκ : 0 ≤ κ) (S : A → Finset X)
    (hS : ∀ x, ∑ a : A, (if x ∈ S a then (1 : ℝ) else 0) ≤ ε * Fintype.card A) (v : V) (x : X) :
    ∑ ω : A × V with ω.2 = v ∧ x ∈ S ω.1, κ ≤ ε * ∑ ω : A × V with ω.2 = v, κ := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have e : ∑ a, (if x ∈ S a then κ else 0) = κ * ∑ a, if x ∈ S a then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by split_ifs <;> simp
  rw [e]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  nlinarith [hS x]

/-! ## 1. PRF with a hidden key -/

section PRF

variable {K D Y : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D] [Fintype Y]
  [DecidableEq Y]

/-- Real-valued version of `sum_prfSwapRow`. -/
theorem sum_prfSwapRow_real (k : K) (g : (K × D → Y) → ℝ) :
    ∑ v : (K × D → Y) × (D → Y), g (prfSwapRow k v.1 v.2) =
      Fintype.card (D → Y) * ∑ F : K × D → Y, g F := by
  have h := Equiv.sum_comp (prfSwap_involutive (D := D) (Y := Y) k).toPerm (fun v ↦ g v.1)
  calc ∑ v : (K × D → Y) × (D → Y), g (prfSwapRow k v.1 v.2)
      = ∑ v : (K × D → Y) × (D → Y), g v.1 := h
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

theorem prf_coupling_real [Nonempty K] [Nonempty D] [Nonempty Y]
    (g : ((K × D) ⊕ D → Y) → ℝ) :
    (∑ ω : K × ((K × D → Y) × (D → Y)),
        ((Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × D → Y) : ℝ)⁻¹ *
          (Fintype.card (D → Y) : ℝ)⁻¹)) * g (prfReal ω.1 (prfSwapRow ω.1 ω.2.1 ω.2.2)) =
      ∑ k : K, ∑ F : K × D → Y,
        ((Fintype.card K : ℝ)⁻¹ * (Fintype.card (K × D → Y) : ℝ)⁻¹) * g (prfReal k F)) ∧
    (∑ ω : K × ((K × D → Y) × (D → Y)),
        ((Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × D → Y) : ℝ)⁻¹ *
          (Fintype.card (D → Y) : ℝ)⁻¹)) * g (prfIdeal ω.2.1 ω.2.2) =
      ∑ F : K × D → Y, ∑ R : D → Y,
        ((Fintype.card (K × D → Y) : ℝ)⁻¹ * (Fintype.card (D → Y) : ℝ)⁻¹) *
          g (prfIdeal F R)) ∧
    ∑ _ω : K × ((K × D → Y) × (D → Y)),
        ((Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × D → Y) : ℝ)⁻¹ *
          (Fintype.card (D → Y) : ℝ)⁻¹)) = 1 := by
  have iK := card_ne_zero_real K
  have iF := card_ne_zero_real (K × D → Y)
  have iR := card_ne_zero_real (D → Y)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    refine (sum_prfSwapRow_real k fun F ↦ ((Fintype.card K : ℝ)⁻¹ *
      ((Fintype.card (K × D → Y) : ℝ)⁻¹ * (Fintype.card (D → Y) : ℝ)⁻¹)) * g (prfReal k F)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    field_simp
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    field_simp
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    field_simp

/-- **Tight PRF security of a random keyed function with a hidden key.**  `F : K × D → Y`
uniform, `k : K` uniform.  The `q`-query circuit `A` (final contraction `Q`) queries the folded
function on `(K × D) ⊕ D`: on the left the keyed hash `F` (all keys), on the right `F (k, ·)` in
the real world and an independent uniform `R` in the ideal world.  The acceptance probabilities
differ by at most `8 q² / |K|`. -/
theorem prf_tight [Nonempty K] [Nonempty D] [Nonempty Y]
    (I : OracleInterface ((K × D) ⊕ D) Y E) (A : QAlg E) (q : ℕ) (Q : E →L[ℂ] E)
    (hQ : ∀ φ, ‖Q φ‖ ≤ ‖φ‖) :
    |∑ k : K, ∑ F : K × D → Y,
          ((Fintype.card K : ℝ)⁻¹ * (Fintype.card (K × D → Y) : ℝ)⁻¹) *
            A.acc I q Q (prfReal k F) -
        ∑ F : K × D → Y, ∑ R : D → Y,
          ((Fintype.card (K × D → Y) : ℝ)⁻¹ * (Fintype.card (D → Y) : ℝ)⁻¹) *
            A.acc I q Q (prfIdeal F R)| ≤ 8 * (q : ℝ) ^ 2 / Fintype.card K := by
  obtain ⟨e1, e2, e3⟩ := prf_coupling_real (K := K) (D := D) (Y := Y) (A.acc I q Q)
  have hκ : (0 : ℝ) ≤ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × D → Y) : ℝ)⁻¹ *
      (Fintype.card (D → Y) : ℝ)⁻¹) := by positivity
  have hid : ∀ x : (K × D) ⊕ D, ∑ k : K, (if x ∈ prfMarked (D := D) k then (1 : ℝ) else 0) ≤
      (Fintype.card K : ℝ)⁻¹ * Fintype.card K := by
    intro x
    rw [inv_mul_cancel₀ (card_ne_zero_real K)]
    rcases x with ⟨k', d⟩ | d
    · have hm : ∀ k : K, (Sum.inl (k', d) ∈ prfMarked (D := D) k) ↔ k = k' := by
        intro k
        simp only [prfMarked, Finset.mem_image, Finset.mem_univ, true_and, Sum.inl.injEq,
          Prod.mk.injEq]
        constructor
        · rintro ⟨_, h, _⟩
          exact h
        · intro h
          exact ⟨d, h, rfl⟩
      simp [hm]
    · have hm : ∀ k : K, ¬ (Sum.inr d ∈ prfMarked (D := D) k) := by
        intro k
        simp [prfMarked]
      simp [hm]
  have h := tight_view I (Ω := K × ((K × D → Y) × (D → Y)))
    (fun _ ↦ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × D → Y) : ℝ)⁻¹ *
      (Fintype.card (D → Y) : ℝ)⁻¹)) (fun _ ↦ hκ) (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    (fun _ ↦ le_rfl) (fun ω ↦ ω.2) (fun ω ↦ prfMarked (D := D) ω.1) (Fintype.card K : ℝ)⁻¹
    (by positivity) (hidden_indep_real _ _ hκ _ hid) (fun _ ↦ A) q (fun _ ↦ Q) (fun _ ↦ hQ)
    (fun ω ↦ prfReal ω.1 (prfSwapRow ω.1 ω.2.1 ω.2.2)) (fun v ↦ prfIdeal v.1 v.2) prf_differ
  simp only [mul_one] at h
  rw [e1, e2, e3] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end PRF

/-! ## 2. Multi-target undetectability -/

section UD

variable {T Msg Y : Type} [Fintype T] [DecidableEq T] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y]

/-- Real-valued version of `sum_udReprog`. -/
theorem sum_udReprog_real (xs : T → Msg) (g : (T → Y) → (T × Msg → Y) → ℝ) :
    ∑ v : (T → Y) × (T × Msg → Y), g v.1 (udReprog xs v.1 v.2) =
      Fintype.card (T → Y) * ∑ H : T × Msg → Y, g (udTargets xs H) H := by
  have h := Equiv.sum_comp (udSwap_involutive (Y := Y) xs).toPerm
    (fun v ↦ g (udTargets xs v.2) v.2)
  have h' : ∀ v : (T → Y) × (T × Msg → Y),
      g (udTargets xs (udSwap xs v).2) (udSwap xs v).2 = g v.1 (udReprog xs v.1 v.2) := by
    intro v
    simp only [udSwap, udTargets_udReprog]
  calc ∑ v : (T → Y) × (T × Msg → Y), g v.1 (udReprog xs v.1 v.2)
      = ∑ v : (T → Y) × (T × Msg → Y), g (udTargets xs (udSwap xs v).2) (udSwap xs v).2 :=
        Finset.sum_congr rfl fun v _ ↦ (h' v).symm
    _ = ∑ v : (T → Y) × (T × Msg → Y), g (udTargets xs v.2) v.2 := h
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

/-- Real-valued version of `sum_udMarked`. -/
theorem sum_udMarked_real (p : T × Msg) :
    ∑ xs : T → Msg, (if p ∈ udMarked xs then (1 : ℝ) else 0) =
      (Fintype.card Msg : ℝ)⁻¹ * Fintype.card (T → Msg) := by
  have h := congrArg ENNReal.toReal (sum_udMarked (T := T) (Msg := Msg) p)
  rw [toReal_sum_ind, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast] at h
  exact h

theorem ud_coupling_real [Nonempty T] [Nonempty Msg] [Nonempty Y]
    (g : (T → Y) → (T × Msg → Y) → ℝ) :
    (∑ ω : (T → Msg) × ((T → Y) × (T × Msg → Y)),
        ((Fintype.card (T → Msg) : ℝ)⁻¹ * ((Fintype.card (T → Y) : ℝ)⁻¹ *
          (Fintype.card (T × Msg → Y) : ℝ)⁻¹)) * g ω.2.1 (udReprog ω.1 ω.2.1 ω.2.2) =
      ∑ xs : T → Msg, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Msg) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
          g (udTargets xs H) H) ∧
    (∑ ω : (T → Msg) × ((T → Y) × (T × Msg → Y)),
        ((Fintype.card (T → Msg) : ℝ)⁻¹ * ((Fintype.card (T → Y) : ℝ)⁻¹ *
          (Fintype.card (T × Msg → Y) : ℝ)⁻¹)) * g ω.2.1 ω.2.2 =
      ∑ y : T → Y, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Y) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) * g y H) ∧
    ∑ _ω : (T → Msg) × ((T → Y) × (T × Msg → Y)),
        ((Fintype.card (T → Msg) : ℝ)⁻¹ * ((Fintype.card (T → Y) : ℝ)⁻¹ *
          (Fintype.card (T × Msg → Y) : ℝ)⁻¹)) = 1 := by
  have iS := card_ne_zero_real (T → Msg)
  have iY := card_ne_zero_real (T → Y)
  have iH := card_ne_zero_real (T × Msg → Y)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun xs _ ↦ ?_
    refine (sum_udReprog_real xs fun y H ↦ ((Fintype.card (T → Msg) : ℝ)⁻¹ *
      ((Fintype.card (T → Y) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹)) * g y H).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    field_simp
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    field_simp
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    field_simp

/-- **Tight multi-target undetectability of a random tweakable function.**  `H : T × Msg → Y`
uniform.  Real: `x* : T → Msg` uniform and hidden, targets `y t = H (t, x* t)`.  Ideal: targets
`y : T → Y` uniform and independent of `H`.  The `q`-query circuit `A y` and its final
contraction `Q y` may depend on the targets.  The acceptance probabilities differ by at most
`8 q² / |Msg|`, independently of the number of tweaks. -/
theorem ud_tight [Nonempty T] [Nonempty Msg] [Nonempty Y]
    (I : OracleInterface (T × Msg) Y E) (A : (T → Y) → QAlg E) (q : ℕ)
    (Q : (T → Y) → E →L[ℂ] E) (hQ : ∀ y φ, ‖Q y φ‖ ≤ ‖φ‖) :
    |∑ xs : T → Msg, ∑ H : T × Msg → Y,
          ((Fintype.card (T → Msg) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
            (A (udTargets xs H)).acc I q (Q (udTargets xs H)) H -
        ∑ y : T → Y, ∑ H : T × Msg → Y,
          ((Fintype.card (T → Y) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
            (A y).acc I q (Q y) H| ≤ 8 * (q : ℝ) ^ 2 / Fintype.card Msg := by
  obtain ⟨e1, e2, e3⟩ := ud_coupling_real (T := T) (Msg := Msg) (Y := Y)
    fun y H ↦ (A y).acc I q (Q y) H
  have hκ : (0 : ℝ) ≤ (Fintype.card (T → Msg) : ℝ)⁻¹ * ((Fintype.card (T → Y) : ℝ)⁻¹ *
      (Fintype.card (T × Msg → Y) : ℝ)⁻¹) := by positivity
  have h := tight_view I (Ω := (T → Msg) × ((T → Y) × (T × Msg → Y)))
    (fun _ ↦ (Fintype.card (T → Msg) : ℝ)⁻¹ * ((Fintype.card (T → Y) : ℝ)⁻¹ *
      (Fintype.card (T × Msg → Y) : ℝ)⁻¹)) (fun _ ↦ hκ) (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    (fun _ ↦ le_rfl) (fun ω ↦ ω.2) (fun ω ↦ udMarked ω.1) (Fintype.card Msg : ℝ)⁻¹
    (by positivity) (hidden_indep_real _ _ hκ _ fun p ↦ le_of_eq (sum_udMarked_real p))
    (fun v ↦ A v.1) q (fun v ↦ Q v.1) (fun v ↦ hQ v.1)
    (fun ω ↦ udReprog ω.1 ω.2.1 ω.2.2) (fun v ↦ v.2) ud_differ
  simp only [mul_one] at h
  rw [e1, e2, e3] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end UD

/-! ## 3. Decisional second-preimage resistance -/

section DSPR

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Real-valued indicator that `x` has no second preimage under `H`. -/
noncomputable def noSPr (H : X → Y) (x : X) : ℝ := (noSPw H x).toReal

theorem noSPr_of_SP {H : X → Y} {x : X} (h : SecondPreimage H x) : noSPr H x = 0 := by
  rw [noSPr, noSPw_of_SP h, ENNReal.toReal_zero]

theorem noSPr_of_not_SP {H : X → Y} {x : X} (h : ¬ SecondPreimage H x) : noSPr H x = 1 := by
  rw [noSPr, noSPw_of_not_SP h, ENNReal.toReal_one]

theorem noSPw_ne_top (H : X → Y) (x : X) : noSPw H x ≠ ⊤ := by
  by_cases h : SecondPreimage H x
  · rw [noSPw_of_SP h]; exact ENNReal.zero_ne_top
  · rw [noSPw_of_not_SP h]; exact ENNReal.one_ne_top

/-- Real-valued version of `sum_fst_comp`. -/
theorem sum_fst_comp_real {X A B : Type} [Fintype X] [DecidableEq X] [Fintype A] [Fintype B]
    (F : (X → A) → ℝ) :
    ∑ τ : X → A × B, F (fun k ↦ (τ k).1) = Fintype.card (X → B) * ∑ H : X → A, F H := by
  rw [← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow X (fun _ ↦ A) (fun _ ↦ B)).symm,
    Fintype.sum_prod_type]
  simp [Equiv.arrowProdEquivProdArrow, Finset.mul_sum]

theorem dspr_coupling_real [Nonempty X] [Nontrivial Y] (g : X → (X → Y) → ℝ) :
    (∑ ω : X × (X → Y × NZ Y),
        ((Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹ *
          (Fintype.card (X → NZ Y) : ℝ)⁻¹) * g ω.1 (fun k ↦ (ω.2 k).1) =
      ∑ H : X → Y, ∑ x : X,
        ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) * g x H) ∧
    ∑ _ω : X × (X → Y × NZ Y),
        ((Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹ *
          (Fintype.card (X → NZ Y) : ℝ)⁻¹) = 1 := by
  obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
  have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
  have iX := card_ne_zero_real X
  have iXY := card_ne_zero_real (X → Y)
  have iXD := card_ne_zero_real (X → NZ Y)
  refine ⟨?_, ?_⟩
  · rw [Fintype.sum_prod_type, Finset.sum_comm (γ := X → Y)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have e := sum_fst_comp_real (X := X) (A := Y) (B := NZ Y)
      (fun H ↦ ((Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹ *
          (Fintype.card (X → NZ Y) : ℝ)⁻¹) * g x H)
    refine e.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    field_simp
  · rw [Fintype.sum_prod_type]
    have e := sum_fst_comp_real (X := X) (A := Y) (B := NZ Y)
      (fun _ ↦ (Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹ *
          (Fintype.card (X → NZ Y) : ℝ)⁻¹)
    simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- Real-valued version of `dspr_hidden`, in the form needed by `tight_view`. -/
theorem dspr_hidden_real (κ : ℝ) (hκ : 0 ≤ κ) (v : X × (X → Y)) (k : X) :
    ∑ ω : X × (X → Y × NZ Y) with (ω.1, dsprHyb ω.1 ω.2) = v ∧ k ∈ dsprMarked ω, κ ≤
      (Fintype.card Y : ℝ)⁻¹ *
        ∑ ω : X × (X → Y × NZ Y) with (ω.1, dsprHyb ω.1 ω.2) = v, κ := by
  have h := dspr_hidden (X := X) (Y := Y) 1 k (fun u ↦ if u = v then 1 else 0)
  simp only [one_mul, ← ite_and] at h
  have hY : (Fintype.card Y : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have h' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hY (ENNReal.sum_ne_top.2 fun ω _ ↦ by split_ifs <;> simp)) h
  rw [toReal_sum_ind, ENNReal.toReal_mul, toReal_sum_ind, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at h'
  rw [Finset.sum_filter, Finset.sum_filter]
  have a1 : ∑ ω : X × (X → Y × NZ Y),
      (if (ω.1, dsprHyb ω.1 ω.2) = v ∧ k ∈ dsprMarked ω then κ else 0) =
      κ * ∑ ω : X × (X → Y × NZ Y),
        if k ∈ dsprMarked ω ∧ (ω.1, dsprHyb ω.1 ω.2) = v then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    by_cases h1 : (ω.1, dsprHyb ω.1 ω.2) = v <;> by_cases h2 : k ∈ dsprMarked ω <;> simp [h1, h2]
  have a2 : ∑ ω : X × (X → Y × NZ Y), (if (ω.1, dsprHyb ω.1 ω.2) = v then κ else 0) =
      κ * ∑ ω : X × (X → Y × NZ Y), if (ω.1, dsprHyb ω.1 ω.2) = v then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    split_ifs <;> simp
  rw [a1, a2]
  calc _ ≤ κ * _ := mul_le_mul_of_nonneg_left h' hκ
    _ = _ := by ring

/-- Real-valued version of `dspr_noSP_indep`. -/
theorem dspr_noSP_indep_real (κ : ℝ) (hκ : 0 ≤ κ) (P : X × (X → Y) → ℝ) (hP : ∀ v, 0 ≤ P v) :
    ∑ ω : X × (X → Y × NZ Y),
        noSPr (fun k ↦ (ω.2 k).1) ω.1 * (κ * P (ω.1, dsprHyb ω.1 ω.2)) =
      (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1) *
        ∑ ω : X × (X → Y × NZ Y), κ * P (ω.1, dsprHyb ω.1 ω.2) := by
  have h := congrArg ENNReal.toReal (dspr_noSP_indep (X := X) (Y := Y) (ENNReal.ofReal κ)
    (fun v ↦ ENNReal.ofReal (P v)))
  have hc : (Fintype.card Y : ℝ≥0∞)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.2 (by exact_mod_cast Fintype.card_pos (α := Y))
  rw [ENNReal.toReal_sum (fun ω _ ↦ ENNReal.mul_ne_top (noSPw_ne_top _ _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)),
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sum (fun ω _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ENNReal.toReal_sub_of_le hc ENNReal.one_ne_top, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ, ENNReal.toReal_ofReal (hP _),
    ENNReal.toReal_one] at h
  exact h

open Classical in
/-- **Tight decisional second-preimage resistance of a random function.**  `H : X → Y` uniform,
`x : X` uniform; the `q`-query circuit `A x` gets `x` and oracle access to `H`, and ends with a
two-outcome measurement with operators `Q₁ x` (output "second preimage") and `Q₀ x` (output "no
second preimage"), `‖Q₁ φ‖² + ‖Q₀ φ‖² ≤ ‖φ‖²`.  It wins iff the output is correct.  With
`1 - p = (1 - 1/|Y|)^(|X|-1)` the exact probability of having no second preimage
(`dspr_prob_noSP`), the winning probability is at most `max (p, 1 - p) + 8 q² / |Y|`. -/
theorem dspr_tight (I : OracleInterface X Y E) (A : X → QAlg E) (q : ℕ)
    (Q₁ Q₀ : X → E →L[ℂ] E) (hQ : ∀ x φ, ‖Q₁ x φ‖ ^ 2 + ‖Q₀ x φ‖ ^ 2 ≤ ‖φ‖ ^ 2) :
    ∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (if SecondPreimage H x then (A x).acc I q (Q₁ x) H else (A x).acc I q (Q₀ x) H) ≤
      max (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))
          ((1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1)) +
        8 * (q : ℝ) ^ 2 / Fintype.card Y := by
  have hQ1 : ∀ x φ, ‖Q₁ x φ‖ ≤ ‖φ‖ := fun x φ ↦
    le_of_sq_le_sq (by nlinarith [hQ x φ, sq_nonneg ‖Q₀ x φ‖]) (norm_nonneg _)
  have hQ0 : ∀ x φ, ‖Q₀ x φ‖ ≤ ‖φ‖ := fun x φ ↦
    le_of_sq_le_sq (by nlinarith [hQ x φ, sq_nonneg ‖Q₁ x φ‖]) (norm_nonneg _)
  have hcY : (1 : ℝ) ≤ Fintype.card Y := by exact_mod_cast Fintype.card_pos (α := Y)
  have hinv0 : (0 : ℝ) ≤ (Fintype.card Y : ℝ)⁻¹ := by positivity
  have hinv1 : (Fintype.card Y : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hcY
  set γ : ℝ := (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1) with hγdef
  have hγ0 : 0 ≤ γ := pow_nonneg (by linarith) _
  have hγ1 : γ ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hδ : (0 : ℝ) ≤ 8 * (q : ℝ) ^ 2 / Fintype.card Y := by positivity
  have hmax0 : 0 ≤ max (1 - γ) γ := hγ0.trans (le_max_right _ _)
  rcases isEmpty_or_nonempty X with hX | hX
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero]
    positivity
  have hle1 : ∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
      (if SecondPreimage H x then (A x).acc I q (Q₁ x) H else (A x).acc I q (Q₀ x) H) ≤ 1 := by
    calc _ ≤ ∑ _H : X → Y, ∑ _x : X,
          ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) * 1 := by
          refine Finset.sum_le_sum fun H _ ↦ Finset.sum_le_sum fun x _ ↦
            mul_le_mul_of_nonneg_left ?_ (by positivity)
          split_ifs
          · exact (A x).acc_le_one I q _ (hQ1 x) H
          · exact (A x).acc_le_one I q _ (hQ0 x) H
      _ = 1 := by
          have iX := card_ne_zero_real X
          have iXY := card_ne_zero_real (X → Y)
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          field_simp
  by_cases hYnt : Nontrivial Y
  swap
  · have hY1 : Fintype.card Y = 1 := by
      have h1 := Fintype.card_pos (α := Y)
      have h2 : ¬ 1 < Fintype.card Y := fun h ↦ hYnt (Fintype.one_lt_card_iff_nontrivial.1 h)
      omega
    have hγ : γ = 0 ∨ γ = 1 := by
      rw [hγdef, hY1]
      rcases Nat.eq_zero_or_pos (Fintype.card X - 1) with h0 | h0
      · right; simp [h0]
      · left; simp [h0.ne']
    have : max (1 - γ) γ = 1 := by rcases hγ with h | h <;> simp [h]
    rw [this]
    linarith
  -- main case
  obtain ⟨e1, e2⟩ := dspr_coupling_real (X := X) (Y := Y)
    fun x H ↦ if SecondPreimage H x then (A x).acc I q (Q₁ x) H else (A x).acc I q (Q₀ x) H
  set κ : ℝ := (Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹ *
          (Fintype.card (X → NZ Y) : ℝ)⁻¹ with hκdef
  have hκ : 0 ≤ κ := by positivity
  rw [← e1]
  let nsp : X × (X → Y × NZ Y) → ℝ := fun ω ↦ noSPr (fun k ↦ (ω.2 k).1) ω.1
  let a₁ : X × (X → Y × NZ Y) → ℝ := fun ω ↦ (A ω.1).acc I q (Q₁ ω.1) (fun k ↦ (ω.2 k).1)
  let P1 : X × (X → Y) → ℝ := fun v ↦ (A v.1).acc I q (Q₁ v.1) v.2
  let P0 : X × (X → Y) → ℝ := fun v ↦ (A v.1).acc I q (Q₀ v.1) v.2
  have hterm : ∀ ω : X × (X → Y × NZ Y),
      κ * (if SecondPreimage (fun k ↦ (ω.2 k).1) ω.1 then
          (A ω.1).acc I q (Q₁ ω.1) (fun k ↦ (ω.2 k).1)
        else (A ω.1).acc I q (Q₀ ω.1) (fun k ↦ (ω.2 k).1)) =
      κ * (1 - nsp ω) * a₁ ω + nsp ω * (κ * P0 (ω.1, dsprHyb ω.1 ω.2)) := by
    intro ω
    by_cases hsp : SecondPreimage (fun k ↦ (ω.2 k).1) ω.1
    · simp only [nsp, a₁, noSPr_of_SP hsp, hsp, ↓reduceIte]
      ring
    · have hfun : (fun k ↦ (ω.2 k).1) = dsprHyb ω.1 ω.2 := by
        funext k
        by_contra hne
        have hk := dspr_differ ω k hne
        simp only [dsprMarked, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hsp ⟨k, hk.1, hk.2⟩
      simp only [nsp, P0, noSPr_of_not_SP hsp, hsp, ↓reduceIte]
      rw [hfun]
      ring
  have tv := tight_view I (Ω := X × (X → Y × NZ Y)) (fun _ ↦ κ) (fun _ ↦ hκ)
    (fun ω ↦ 1 - nsp ω)
    (fun ω ↦ by
      by_cases hsp : SecondPreimage (fun k ↦ (ω.2 k).1) ω.1
      · simp [nsp, noSPr_of_SP hsp]
      · simp [nsp, noSPr_of_not_SP hsp])
    (fun ω ↦ by
      by_cases hsp : SecondPreimage (fun k ↦ (ω.2 k).1) ω.1
      · simp [nsp, noSPr_of_SP hsp]
      · simp [nsp, noSPr_of_not_SP hsp])
    (fun ω ↦ (ω.1, dsprHyb ω.1 ω.2)) dsprMarked (Fintype.card Y : ℝ)⁻¹ hinv0
    (dspr_hidden_real κ hκ) (fun v ↦ A v.1) q (fun v ↦ Q₁ v.1) (fun v ↦ hQ1 v.1)
    (fun ω k ↦ (ω.2 k).1) (fun v ↦ v.2) dspr_differ
  rw [e2] at tv
  have i1 := dspr_noSP_indep_real κ hκ P1 fun v ↦ (A v.1).acc_nonneg I q _ _
  have i0 := dspr_noSP_indep_real κ hκ P0 fun v ↦ (A v.1).acc_nonneg I q _ _
  set A1 : ℝ := ∑ ω : X × (X → Y × NZ Y), κ * P1 (ω.1, dsprHyb ω.1 ω.2) with hA1
  set A0 : ℝ := ∑ ω : X × (X → Y × NZ Y), κ * P0 (ω.1, dsprHyb ω.1 ω.2) with hA0
  have hA1nn : 0 ≤ A1 := Finset.sum_nonneg fun ω _ ↦ mul_nonneg hκ ((A ω.1).acc_nonneg I q _ _)
  have hA0nn : 0 ≤ A0 := Finset.sum_nonneg fun ω _ ↦ mul_nonneg hκ ((A ω.1).acc_nonneg I q _ _)
  have hA : A1 + A0 ≤ 1 := by
    rw [hA1, hA0, ← Finset.sum_add_distrib, ← e2]
    refine Finset.sum_le_sum fun ω _ ↦ ?_
    rw [← mul_add]
    have := (A ω.1).acc_add_le_one I q (Q₁ ω.1) (Q₀ ω.1) (hQ ω.1) (dsprHyb ω.1 ω.2)
    calc κ * (P1 (ω.1, dsprHyb ω.1 ω.2) + P0 (ω.1, dsprHyb ω.1 ω.2)) ≤ κ * 1 :=
          mul_le_mul_of_nonneg_left this hκ
      _ = κ := mul_one _
  have hhyb : ∑ ω : X × (X → Y × NZ Y), κ * (1 - nsp ω) * P1 (ω.1, dsprHyb ω.1 ω.2) =
      A1 - γ * A1 := by
    rw [← i1, hA1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ ↦ by simp only [nsp]; ring
  have hsum : ∑ ω : X × (X → Y × NZ Y),
      κ * (if SecondPreimage (fun k ↦ (ω.2 k).1) ω.1 then
          (A ω.1).acc I q (Q₁ ω.1) (fun k ↦ (ω.2 k).1)
        else (A ω.1).acc I q (Q₀ ω.1) (fun k ↦ (ω.2 k).1)) =
      ∑ ω : X × (X → Y × NZ Y), κ * (1 - nsp ω) * a₁ ω + γ * A0 := by
    rw [← i0, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ ↦ hterm ω
  rw [hsum]
  have tv' := (abs_le.1 tv).2
  have htv : ∑ ω : X × (X → Y × NZ Y), κ * (1 - nsp ω) * a₁ ω ≤
      (A1 - γ * A1) + 8 * (q : ℝ) ^ 2 / Fintype.card Y := by
    rw [← hhyb]
    have e : 8 * (q : ℝ) ^ 2 * (Fintype.card Y : ℝ)⁻¹ * 1 = 8 * (q : ℝ) ^ 2 / Fintype.card Y := by
      ring
    rw [e] at tv'
    linarith
  have hfin : (1 - γ) * A1 + γ * A0 ≤ max (1 - γ) γ :=
    calc (1 - γ) * A1 + γ * A0 ≤ max (1 - γ) γ * A1 + max (1 - γ) γ * A0 :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hA1nn)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0nn)
      _ = max (1 - γ) γ * (A1 + A0) := by ring
      _ ≤ max (1 - γ) γ * 1 := mul_le_mul_of_nonneg_left hA hmax0
      _ = _ := mul_one _
  linarith

open Classical in
/-- **Tight DSPR, Bernstein–Hülsing advantage form.**  With `p = Pr[SP] = 1 - (1 - 1/|Y|)^(|X|-1)`
and `p ≥ 1/2` (stated as the hypothesis `(1 - 1/|Y|)^(|X|-1) ≤ 1/2`, i.e. the trivial strategy is
"always answer SP"), the DSPR advantage `max (0, Pr[b = SP] - p)` is at most `8 q² / |Y|`.
Without `p ≥ 1/2` only `dspr_tight` is available. -/
theorem dspr_tight_adv (I : OracleInterface X Y E) (A : X → QAlg E) (q : ℕ)
    (Q₁ Q₀ : X → E →L[ℂ] E) (hQ : ∀ x φ, ‖Q₁ x φ‖ ^ 2 + ‖Q₀ x φ‖ ^ 2 ≤ ‖φ‖ ^ 2)
    (hp : (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1) ≤ 1 / 2) :
    max 0 (∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (if SecondPreimage H x then (A x).acc I q (Q₁ x) H else (A x).acc I q (Q₀ x) H) -
      (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))) ≤
        8 * (q : ℝ) ^ 2 / Fintype.card Y := by
  have h := dspr_tight I A q Q₁ Q₀ hQ
  rw [max_eq_left (by linarith)] at h
  refine max_le (by positivity) ?_
  linarith

/-- If `|Y| < |X|` then `x` has no second preimage with probability at most `1/2`:
`(1 - 1/|Y|)^(|X|-1) ≤ (1 - 1/|Y|)^|Y| ≤ e⁻¹ ≤ 1/2`. -/
theorem pow_noSP_le_half (hcard : Fintype.card Y < Fintype.card X) :
    (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1) ≤ 1 / 2 := by
  have hN : 0 < Fintype.card Y := Fintype.card_pos
  have hN' : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hN
  have hinv1 : (Fintype.card Y : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
  have h0 : (0 : ℝ) ≤ 1 - (Fintype.card Y : ℝ)⁻¹ := by linarith
  have h1 : 1 - (Fintype.card Y : ℝ)⁻¹ ≤ 1 := by linarith [inv_nonneg.2 hN'.le]
  have hexp : 1 - (Fintype.card Y : ℝ)⁻¹ ≤ Real.exp (-(Fintype.card Y : ℝ)⁻¹) := by
    have := Real.add_one_le_exp (-(Fintype.card Y : ℝ)⁻¹)
    linarith
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    exact inv_anti₀ (by norm_num) h2
  calc (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1)
      ≤ (1 - (Fintype.card Y : ℝ)⁻¹) ^ Fintype.card Y :=
        pow_le_pow_of_le_one h0 h1 (by omega)
    _ ≤ Real.exp (-(Fintype.card Y : ℝ)⁻¹) ^ Fintype.card Y := pow_le_pow_left₀ h0 hexp _
    _ = Real.exp (-1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
    _ ≤ 1 / 2 := he

open Classical in
/-- **Tight DSPR, Bernstein–Hülsing advantage form, numeric condition.**  If `|Y| < |X|` (so that
`p = Pr[SP] ≥ 1 - e⁻¹ ≥ 1/2`), the DSPR advantage `max (0, Pr[b = SP] - p)` is at most
`8 q² / |Y|`. -/
theorem dspr_tight_adv_of_card_lt (I : OracleInterface X Y E) (A : X → QAlg E) (q : ℕ)
    (Q₁ Q₀ : X → E →L[ℂ] E) (hQ : ∀ x φ, ‖Q₁ x φ‖ ^ 2 + ‖Q₀ x φ‖ ^ 2 ≤ ‖φ‖ ^ 2)
    (hcard : Fintype.card Y < Fintype.card X) :
    max 0 (∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (if SecondPreimage H x then (A x).acc I q (Q₁ x) H else (A x).acc I q (Q₀ x) H) -
      (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))) ≤
        8 * (q : ℝ) ^ 2 / Fintype.card Y :=
  dspr_tight_adv I A q Q₁ Q₀ hQ (pow_noSP_le_half hcard)

/-- If `2 ≤ |Y| ≤ |X|` then `x` has no second preimage with probability at most `1/2`:
`(1 - 1/N)^(|X|-1) ≤ (1 - 1/N)^(N-1) ≤ 1/2` (Bernoulli: `(1 + 1/(N-1))^(N-1) ≥ 2`).  This covers
`|X| = |Y|`. -/
theorem pow_noSP_le_half' (hY : 2 ≤ Fintype.card Y) (hXY : Fintype.card Y ≤ Fintype.card X) :
    (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1) ≤ 1 / 2 := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card Y = k + 1 := ⟨Fintype.card Y - 1, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have ha : 1 - (Fintype.card Y : ℝ)⁻¹ = (k : ℝ) / (k + 1) := by
    rw [hk]
    push_cast
    field_simp
    ring
  have h0 : (0 : ℝ) ≤ (k : ℝ) / (k + 1) := by positivity
  have h1 : (k : ℝ) / (k + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hbern : (2 : ℝ) ≤ (1 + (k : ℝ)⁻¹) ^ k := by
    have h := one_add_mul_le_pow (a := (k : ℝ)⁻¹) (by linarith [inv_nonneg.2 hk0.le]) k
    rwa [mul_inv_cancel₀ hk0.ne', one_add_one_eq_two] at h
  have hprod : ((k : ℝ) / (k + 1)) ^ k * (1 + (k : ℝ)⁻¹) ^ k = 1 := by
    rw [← mul_pow]
    have : (k : ℝ) / (k + 1) * (1 + (k : ℝ)⁻¹) = 1 := by
      field_simp
    rw [this, one_pow]
  have hpk : ((k : ℝ) / (k + 1)) ^ k ≤ 1 / 2 := by
    have hpos : (0 : ℝ) ≤ ((k : ℝ) / (k + 1)) ^ k := pow_nonneg h0 _
    nlinarith
  rw [ha]
  exact (pow_le_pow_of_le_one h0 h1 (by omega)).trans hpk

open Classical in
/-- **Tight DSPR, Bernstein–Hülsing advantage form, `2 ≤ |Y| ≤ |X|`** (message type as large as
the output type, equality allowed): the DSPR advantage is at most `8 q² / |Y|`. -/
theorem dspr_tight_adv_of_card_le (I : OracleInterface X Y E) (A : X → QAlg E) (q : ℕ)
    (Q₁ Q₀ : X → E →L[ℂ] E) (hQ : ∀ x φ, ‖Q₁ x φ‖ ^ 2 + ‖Q₀ x φ‖ ^ 2 ≤ ‖φ‖ ^ 2)
    (hY : 2 ≤ Fintype.card Y) (hXY : Fintype.card Y ≤ Fintype.card X) :
    max 0 (∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (if SecondPreimage H x then (A x).acc I q (Q₁ x) H else (A x).acc I q (Q₀ x) H) -
      (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))) ≤
        8 * (q : ℝ) ^ 2 / Fintype.card Y :=
  dspr_tight_adv I A q Q₁ Q₀ hQ (pow_noSP_le_half' hY hXY)

end DSPR

/-! ## Non-vacuity: the PRF bound for standard circuits -/

section Circuit

variable {K D Y W : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype W] [DecidableEq W]

/-- **Tight PRF bound for standard circuits.**  The circuit `U_q O_H U_{q-1} … O_H U_0 |ψ⟩` with
arbitrary unitary matrices `U t` on the register `(((K × D) ⊕ D) × Y) × W`, the standard oracle
`O_H = oracleUnitary H ⊗ 1` and a final computational-basis measurement of an arbitrary
predicate `p`. -/
theorem prf_tight_circuit [Nonempty K] [Nonempty D]
    (ψ : EuclideanSpace ℂ (Reg ((K × D) ⊕ D) Y W)) (hψ : ‖ψ‖ ≤ 1)
    (U : ℕ → Matrix (Reg ((K × D) ⊕ D) Y W) (Reg ((K × D) ⊕ D) Y W) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup (Reg ((K × D) ⊕ D) Y W) ℂ) (q : ℕ)
    (p : Reg ((K × D) ⊕ D) Y W → Prop) [DecidablePred p] :
    |∑ k : K, ∑ F : K × D → Y,
          ((Fintype.card K : ℝ)⁻¹ * (Fintype.card (K × D → Y) : ℝ)⁻¹) *
            (QAlg.ofUnitaries ψ hψ U hU).acc (stdOracle ((K × D) ⊕ D) Y W) q (measProj p)
              (prfReal k F) -
        ∑ F : K × D → Y, ∑ R : D → Y,
          ((Fintype.card (K × D → Y) : ℝ)⁻¹ * (Fintype.card (D → Y) : ℝ)⁻¹) *
            (QAlg.ofUnitaries ψ hψ U hU).acc (stdOracle ((K × D) ⊕ D) Y W) q (measProj p)
              (prfIdeal F R)| ≤ 8 * (q : ℝ) ^ 2 / Fintype.card K :=
  prf_tight _ _ q _ (norm_measProj_le p)

end Circuit

end PQ.QROM.Tight

#print axioms PQ.QROM.Tight.prf_tight
#print axioms PQ.QROM.Tight.ud_tight
#print axioms PQ.QROM.Tight.dspr_tight
#print axioms PQ.QROM.Tight.dspr_tight_adv
#print axioms PQ.QROM.Tight.dspr_tight_adv_of_card_lt
#print axioms PQ.QROM.Tight.dspr_tight_adv_of_card_le
#print axioms PQ.QROM.Tight.prf_tight_circuit
