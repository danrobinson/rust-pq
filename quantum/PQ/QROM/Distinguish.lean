import PQ.QROM.Average
import PQ.QROM.Product
import PQ.QROM.Preimage
import PQ.QROM.Hybrid

/-!
# Distinguishing-type properties of a random function against quantum queries

All oracles of each game are folded into ONE uniformly random function, so that the
single-function interface `HybridModel` applies.  Every bound is of one-way-to-hiding type
(`Hidden.real_le_hyb_add`): the real experiment is rewritten (by an exact change of variables) as
a coupled experiment whose oracle differs from a view-determined oracle only on a marked set that
is `ε`-hidden from the view, and the two probabilities then differ by at most `4 q √ε`.

1. **PRF with a hidden key** (`prf_real_le_ideal_add`, `prf_ideal_le_real_add`, program level
   `prf_qprob_real_le_ideal_add`, `prf_qprob_ideal_le_real_add`).  `F : K × D → Y` uniform with
   full quantum access; real world: additional quantum access to `F (k, ·)` for a hidden uniform
   key `k`; ideal world: to an independent uniform `R : D → Y`.  Advantage `≤ 4 q / √|K|`.
2. **Multi-target undetectability, distinct tweaks, one-shot** (`ud_real_le_ideal_add`,
   `ud_ideal_le_real_add`, program level `ud_qprob_real_le_ideal_add`,
   `ud_qprob_ideal_le_real_add`).  `H : T × Msg → Y` uniform; real targets `y t = H (t, x* t)` for
   hidden uniform `x* : T → Msg`; ideal targets uniform.  Advantage `≤ 4 q / √|Msg|`, independent
   of the number `|T|` of tweaks.
3. **Decisional second-preimage resistance** (`dspr_le`, program level `dspr_qprob_le`).
   `H : X → Y` uniform, `x` uniform and given to the adversary, which outputs a bit `b`;
   `Pr[b = SP(H, x)] ≤ max (p, 1 - p) + 4 q / √|Y|` where `1 - p = (1 - 1/|Y|)^(|X|-1)` is the exact
   probability that `x` has no second preimage (`dspr_prob_noSP`).

**Honest caveat.**  These are one-way-to-hiding bounds of order `q / √size`.  They are NOT claimed
tight: e.g. Grover key search achieves PRF advantage of order `q² / |K|`, the square of the bound
proved here, and no matching `q / √|K|` attack is claimed.  `q` counts ALL quantum queries to the
folded function (e.g. hash queries and PRF-oracle queries together).  The DSPR statement bounds
the probability of guessing the predicate `SP` correctly by the trivial guessing probability plus
the O2H term; it is not the Bernstein–Hülsing advantage definition verbatim.
-/

open MeasureTheory ENNReal Finset Quantum

set_option linter.unusedSectionVars false

universe u v w

namespace PQ.QROM

/-! ### Generic helpers -/

theorem card_mul_inv_cancel (α : Type) [Fintype α] [Nonempty α] :
    (Fintype.card α : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ = 1 :=
  natCast_mul_inv_cancel Fintype.card_ne_zero

section Indep

variable {A V X : Type} [Fintype A] [Fintype V] [Fintype X] [DecidableEq X]

/-- Worlds `(a, v)` with `a` uniform and independent of the view `v`: a marked set `S a` that
depends only on the hidden part `a` and contains each point for at most an `ε`-fraction of the
`a`'s is `ε`-hidden from the view. -/
theorem hidden_indep (κ ε : ℝ≥0∞) (S : A → Finset X)
    (hS : ∀ x, ∑ a : A, (if x ∈ S a then (1 : ℝ≥0∞) else 0) ≤ ε * Fintype.card A) :
    Hidden (Ω := A × V) (fun _ ↦ κ) (fun ω ↦ ω.2) (fun ω ↦ S ω.1) ε := by
  intro x φ
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc ∑ a, ∑ v, κ * (if x ∈ S a then φ v else 0)
      = (∑ a, (if x ∈ S a then (1 : ℝ≥0∞) else 0)) * ∑ v, κ * φ v := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        split_ifs <;> simp
    _ ≤ ε * Fintype.card A * ∑ v, κ * φ v := by
        gcongr
        exact hS x
    _ = ε * ∑ _a : A, ∑ v, κ * φ v := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Indep

variable {Leaf : Type} {q : ℕ}

/-! ## 1. PRF with a hidden key -/

section PRF

variable {K D Y : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D] [Fintype Y]
  [DecidableEq Y]

/-- Real PRF world, folded: the keyed hash `F` on the left, the keyed instance `F (k, ·)` on the
right. -/
def prfReal (k : K) (F : K × D → Y) : (K × D) ⊕ D → Y := Sum.elim F fun d ↦ F (k, d)

/-- Ideal PRF world, folded: the keyed hash `F` on the left, an independent function `R` on the
right. -/
def prfIdeal (F : K × D → Y) (R : D → Y) : (K × D) ⊕ D → Y := Sum.elim F R

/-- `F` with the row of the key `k` replaced by `R`. -/
def prfSwapRow (k : K) (F : K × D → Y) (R : D → Y) : K × D → Y :=
  fun p ↦ if p.1 = k then R p.2 else F p

/-- Swap the row `F (k, ·)` with `R`. -/
def prfSwap (k : K) (v : (K × D → Y) × (D → Y)) : (K × D → Y) × (D → Y) :=
  (prfSwapRow k v.1 v.2, fun d ↦ v.1 (k, d))

theorem prfSwap_involutive (k : K) : Function.Involutive (prfSwap (D := D) (Y := Y) k) := by
  rintro ⟨F, R⟩
  refine Prod.ext ?_ ?_
  · funext p
    by_cases h : p.1 = k
    · simp only [prfSwap, prfSwapRow, h, ite_true]
      rw [← h]
    · simp only [prfSwap, prfSwapRow, h, ite_false]
  · funext d
    simp [prfSwap, prfSwapRow]

/-- Change of variables: for every key, swapping the key's row with `R` preserves the uniform
distribution of `(F, R)`. -/
theorem sum_prfSwapRow (k : K) (g : (K × D → Y) → ℝ≥0∞) :
    ∑ v : (K × D → Y) × (D → Y), g (prfSwapRow k v.1 v.2) =
      Fintype.card (D → Y) * ∑ F : K × D → Y, g F := by
  have h := Equiv.sum_comp (prfSwap_involutive (D := D) (Y := Y) k).toPerm (fun v ↦ g v.1)
  calc ∑ v : (K × D → Y) × (D → Y), g (prfSwapRow k v.1 v.2)
      = ∑ v : (K × D → Y) × (D → Y), g v.1 := h
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

/-- The PRF coupling: worlds `(k, (F, R))`, uniform.  The coupled real oracle
`prfReal k (prfSwapRow k F R)` has exactly the real-world distribution; the hybrid oracle is the
ideal oracle `prfIdeal F R`. -/
private theorem prf_coupling [Nonempty K] [Nonempty D] [Nonempty Y]
    (g : ((K × D) ⊕ D → Y) → ℝ≥0∞) :
    (∑ ω : K × ((K × D → Y) × (D → Y)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (D → Y) : ℝ≥0∞)⁻¹)) * g (prfReal ω.1 (prfSwapRow ω.1 ω.2.1 ω.2.2)) =
      ∑ k : K, ∑ F : K × D → Y,
        ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹) * g (prfReal k F)) ∧
    (∑ ω : K × ((K × D → Y) × (D → Y)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (D → Y) : ℝ≥0∞)⁻¹)) * g (prfIdeal ω.2.1 ω.2.2) =
      ∑ F : K × D → Y, ∑ R : D → Y,
        ((Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (D → Y) : ℝ≥0∞)⁻¹) *
          g (prfIdeal F R)) ∧
    ∑ _ω : K × ((K × D → Y) × (D → Y)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (D → Y) : ℝ≥0∞)⁻¹)) ≤ 1 := by
  have iK := card_mul_inv_cancel K
  have iF := card_mul_inv_cancel (K × D → Y)
  have iR := card_mul_inv_cancel (D → Y)
  set cK : ℝ≥0∞ := (Fintype.card K : ℝ≥0∞)
  set cF : ℝ≥0∞ := (Fintype.card (K × D → Y) : ℝ≥0∞)
  set cR : ℝ≥0∞ := (Fintype.card (D → Y) : ℝ≥0∞)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    refine (sum_prfSwapRow k fun F ↦ (cK⁻¹ * (cF⁻¹ * cR⁻¹)) * g (prfReal k F)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    calc cR * (cK⁻¹ * (cF⁻¹ * cR⁻¹) * g (prfReal k F))
        = (cR * cR⁻¹) * (cK⁻¹ * cF⁻¹ * g (prfReal k F)) := by ring
      _ = _ := by rw [iR, one_mul]
  · rw [Fintype.sum_prod_type]
    dsimp only
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    calc cK * (cK⁻¹ * (cF⁻¹ * cR⁻¹) * g (prfIdeal F R))
        = (cK * cK⁻¹) * (cF⁻¹ * cR⁻¹ * g (prfIdeal F R)) := by ring
      _ = _ := by rw [iK, one_mul]
  · refine le_of_eq ?_
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    calc cK * (cF * cR * (cK⁻¹ * (cF⁻¹ * cR⁻¹)))
        = (cK * cK⁻¹) * (cF * cF⁻¹) * (cR * cR⁻¹) := by ring
      _ = 1 := by rw [iK, iF, iR]; simp

/-- The marked set of the PRF coupling: the row of the hidden key in the keyed hash. -/
def prfMarked (k : K) : Finset ((K × D) ⊕ D) := univ.image fun d ↦ Sum.inl (k, d)

/-- The key row is `1/|K|`-hidden from the view `(F, R)`. -/
theorem prf_hidden (κ : ℝ≥0∞) :
    Hidden (Ω := K × ((K × D → Y) × (D → Y))) (fun _ ↦ κ) (fun ω ↦ ω.2)
      (fun ω ↦ prfMarked (D := D) ω.1) (Fintype.card K : ℝ≥0∞)⁻¹ := by
  refine hidden_indep κ _ _ fun x ↦ ?_
  rcases x with ⟨k', d⟩ | d
  · have : Nonempty K := ⟨k'⟩
    have hm : ∀ k : K, (Sum.inl (k', d) ∈ prfMarked (D := D) k) ↔ k = k' := by
      intro k
      simp only [prfMarked, Finset.mem_image, Finset.mem_univ, true_and, Sum.inl.injEq,
        Prod.mk.injEq]
      constructor
      · rintro ⟨_, h, _⟩
        exact h
      · intro h
        exact ⟨d, h, rfl⟩
    simp only [hm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [mul_comm, card_mul_inv_cancel]
  · have hm : ∀ k : K, ¬ (Sum.inr d ∈ prfMarked (D := D) k) := by
      intro k
      simp [prfMarked]
    simp [hm]

theorem prf_differ (ω : K × ((K × D → Y) × (D → Y))) (x : (K × D) ⊕ D)
    (h : prfReal ω.1 (prfSwapRow ω.1 ω.2.1 ω.2.2) x ≠ prfIdeal ω.2.1 ω.2.2 x) :
    x ∈ prfMarked (D := D) ω.1 := by
  classical
  rcases x with ⟨k', d⟩ | d
  · by_cases hk : k' = ω.1
    · subst hk
      exact Finset.mem_image.2 ⟨d, Finset.mem_univ _, rfl⟩
    · exact absurd (by simp [prfReal, prfIdeal, prfSwapRow, hk]) h
  · exact absurd (by simp [prfReal, prfIdeal, prfSwapRow]) h

/-- **PRF security of a random keyed function with a hidden key (real ≤ ideal).**
`F : K × D → Y` uniform, `k : K` uniform.  The `q`-query algorithm `M` has quantum access to the
folded function on `(K × D) ⊕ D`: on the left always the keyed hash `F` (all keys), on the right
`F (k, ·)` in the real world and an independent uniform `R` in the ideal world.  For every event
`E`, `Pr_real[E] ≤ Pr_ideal[E] + 4 q / √|K|`.  (One-way-to-hiding bound, not tight.) -/
theorem prf_real_le_ideal_add [Nonempty K] [Nonempty D] [Nonempty Y]
    (M : HybridModel ((K × D) ⊕ D) Y Leaf q) (E : Leaf → Prop) :
    ∑ k : K, ∑ F : K × D → Y,
        ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹) *
          M.prob (prfReal k F) E ≤
      ∑ F : K × D → Y, ∑ R : D → Y,
        ((Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (D → Y) : ℝ≥0∞)⁻¹) *
          M.prob (prfIdeal F R) E +
        4 * q * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have : Nonempty ((K × D) ⊕ D) := ⟨Sum.inr (Classical.arbitrary D)⟩
  obtain ⟨e1, e2, hw⟩ := prf_coupling (K := K) (D := D) (Y := Y) fun H ↦ M.prob H E
  have h := (prf_hidden (K := K) (D := D) (Y := Y) _).real_le_hyb_add hw (fun _ ↦ M)
    (fun ω ↦ prfReal ω.1 (prfSwapRow ω.1 ω.2.1 ω.2.2)) (fun v ↦ prfIdeal v.1 v.2)
    prf_differ (fun _ ↦ E)
  rw [← e1, ← e2]
  exact h

/-- **PRF security of a random keyed function with a hidden key (ideal ≤ real).** -/
theorem prf_ideal_le_real_add [Nonempty K] [Nonempty D] [Nonempty Y]
    (M : HybridModel ((K × D) ⊕ D) Y Leaf q) (E : Leaf → Prop) :
    ∑ F : K × D → Y, ∑ R : D → Y,
        ((Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (D → Y) : ℝ≥0∞)⁻¹) *
          M.prob (prfIdeal F R) E ≤
      ∑ k : K, ∑ F : K × D → Y,
        ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹) *
          M.prob (prfReal k F) E +
        4 * q * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have : Nonempty ((K × D) ⊕ D) := ⟨Sum.inr (Classical.arbitrary D)⟩
  obtain ⟨e1, e2, hw⟩ := prf_coupling (K := K) (D := D) (Y := Y) fun H ↦ M.prob H E
  have h := (prf_hidden (K := K) (D := D) (Y := Y) _).hyb_le_real_add hw (fun _ ↦ M)
    (fun ω ↦ prfReal ω.1 (prfSwapRow ω.1 ω.2.1 ω.2.2)) (fun v ↦ prfIdeal v.1 v.2)
    prf_differ (fun _ ↦ E)
  rw [← e1, ← e2]
  exact h

section Program

variable [AddCommGroup Y] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **PRF security, program level (real ≤ ideal).**  For every VCVio quantum query program `x`
with at most `q` calls to the folded oracle on `(K × D) ⊕ D`, every initial state and every
event of the leaf. -/
theorem prf_qprob_real_le_ideal_add [Nonempty K] [Nonempty D] (I : L.Interp)
    (x : QuantumComp L (qromSpec ((K × D) ⊕ D) Y) W A) (ρ : SubState A) (q : ℕ)
    (hx : QueryBounded x q) (E : (Σ u, W u) → Prop) :
    ∑ k : K, ∑ F : K × D → Y,
        ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹) *
          qprob I (prfReal k F) x ρ E ≤
      ∑ F : K × D → Y, ∑ R : D → Y,
        ((Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (D → Y) : ℝ≥0∞)⁻¹) *
          qprob I (prfIdeal F R) x ρ E +
        4 * q * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  prf_real_le_ideal_add (HybridModel.ofProgram I x ρ q hx E) id

/-- **PRF security, program level (ideal ≤ real).** -/
theorem prf_qprob_ideal_le_real_add [Nonempty K] [Nonempty D] (I : L.Interp)
    (x : QuantumComp L (qromSpec ((K × D) ⊕ D) Y) W A) (ρ : SubState A) (q : ℕ)
    (hx : QueryBounded x q) (E : (Σ u, W u) → Prop) :
    ∑ F : K × D → Y, ∑ R : D → Y,
        ((Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (D → Y) : ℝ≥0∞)⁻¹) *
          qprob I (prfIdeal F R) x ρ E ≤
      ∑ k : K, ∑ F : K × D → Y,
        ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × D → Y) : ℝ≥0∞)⁻¹) *
          qprob I (prfReal k F) x ρ E +
        4 * q * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  prf_ideal_le_real_add (HybridModel.ofProgram I x ρ q hx E) id

end Program

end PRF

/-! ## 2. Multi-target undetectability, distinct tweaks, one-shot -/

section UD

variable {T Msg Y : Type} [Fintype T] [DecidableEq T] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y]

/-- The real targets: `y t = H (t, x* t)`. -/
def udTargets (xs : T → Msg) (H : T × Msg → Y) : T → Y := fun t ↦ H (t, xs t)

/-- `H` reprogrammed to `y t` at the points `(t, x* t)`. -/
def udReprog (xs : T → Msg) (y : T → Y) (H : T × Msg → Y) : T × Msg → Y :=
  fun p ↦ if p.2 = xs p.1 then y p.1 else H p

/-- Swap the values of `H` at the points `(t, x* t)` with `y`. -/
def udSwap (xs : T → Msg) (v : (T → Y) × (T × Msg → Y)) : (T → Y) × (T × Msg → Y) :=
  (udTargets xs v.2, udReprog xs v.1 v.2)

theorem udTargets_udReprog (xs : T → Msg) (y : T → Y) (H : T × Msg → Y) :
    udTargets xs (udReprog xs y H) = y := by
  funext t
  simp [udTargets, udReprog]

theorem udSwap_involutive (xs : T → Msg) : Function.Involutive (udSwap (Y := Y) xs) := by
  rintro ⟨y, H⟩
  refine Prod.ext (udTargets_udReprog xs y H) ?_
  funext p
  by_cases h : p.2 = xs p.1
  · simp only [udSwap, udReprog, udTargets, h, ite_true]
    rw [← h]
  · simp only [udSwap, udReprog, h, ite_false]

/-- Change of variables: for every `x*`, reprogramming a uniform `H` at `(t, x* t)` to uniform
independent `y t` gives a uniform function whose targets are `y`. -/
theorem sum_udReprog (xs : T → Msg) (g : (T → Y) → (T × Msg → Y) → ℝ≥0∞) :
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

/-- The marked set of the UD coupling: the hidden preimages `(t, x* t)`. -/
def udMarked (xs : T → Msg) : Finset (T × Msg) := univ.filter fun p ↦ p.2 = xs p.1

/-- A fixed point `(t, m)` is the hidden preimage for a `1/|Msg|` fraction of the `x*`. -/
theorem sum_udMarked (p : T × Msg) :
    ∑ xs : T → Msg, (if p ∈ udMarked xs then (1 : ℝ≥0∞) else 0) =
      (Fintype.card Msg : ℝ≥0∞)⁻¹ * Fintype.card (T → Msg) := by
  have : Nonempty Msg := ⟨p.2⟩
  have hat : ∀ (a : Msg) (ρ : {j // j ≠ p.1} → Msg),
      (Equiv.funSplitAt p.1 Msg).symm (a, ρ) p.1 = a := by
    intro a ρ; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hc : Fintype.card (T → Msg) = Fintype.card Msg * Fintype.card ({j // j ≠ p.1} → Msg) := by
    rw [Fintype.card_congr (Equiv.funSplitAt p.1 Msg), Fintype.card_prod]
  rw [← Equiv.sum_comp (Equiv.funSplitAt p.1 Msg).symm, Fintype.sum_prod_type]
  simp only [udMarked, Finset.mem_filter, Finset.mem_univ, true_and, hat, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, mul_one]
  rw [hc, Nat.cast_mul, ← mul_assoc, mul_comm (Fintype.card Msg : ℝ≥0∞)⁻¹, card_mul_inv_cancel,
    one_mul]

/-- The hidden preimages are `1/|Msg|`-hidden from the view `(y, H)`. -/
theorem ud_hidden (κ : ℝ≥0∞) :
    Hidden (Ω := (T → Msg) × ((T → Y) × (T × Msg → Y))) (fun _ ↦ κ) (fun ω ↦ ω.2)
      (fun ω ↦ udMarked ω.1) (Fintype.card Msg : ℝ≥0∞)⁻¹ :=
  hidden_indep κ _ _ fun p ↦ le_of_eq (sum_udMarked p)

theorem ud_differ (ω : (T → Msg) × ((T → Y) × (T × Msg → Y))) (p : T × Msg)
    (h : udReprog ω.1 ω.2.1 ω.2.2 p ≠ ω.2.2 p) : p ∈ udMarked ω.1 := by
  simp only [udMarked, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hne
  exact h (by simp [udReprog, hne])

/-- The UD coupling: worlds `(x*, (y, H))`, uniform.  The coupled real oracle
`udReprog x* y H` together with the targets `y` has exactly the real-world distribution. -/
private theorem ud_coupling [Nonempty T] [Nonempty Msg] [Nonempty Y]
    (g : (T → Y) → (T × Msg → Y) → ℝ≥0∞) :
    (∑ ω : (T → Msg) × ((T → Y) × (T × Msg → Y)),
        ((Fintype.card (T → Msg) : ℝ≥0∞)⁻¹ * ((Fintype.card (T → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹)) * g ω.2.1 (udReprog ω.1 ω.2.1 ω.2.2) =
      ∑ xs : T → Msg, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Msg) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          g (udTargets xs H) H) ∧
    (∑ ω : (T → Msg) × ((T → Y) × (T × Msg → Y)),
        ((Fintype.card (T → Msg) : ℝ≥0∞)⁻¹ * ((Fintype.card (T → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹)) * g ω.2.1 ω.2.2 =
      ∑ y : T → Y, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) * g y H) ∧
    ∑ _ω : (T → Msg) × ((T → Y) × (T × Msg → Y)),
        ((Fintype.card (T → Msg) : ℝ≥0∞)⁻¹ * ((Fintype.card (T → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹)) ≤ 1 := by
  have iS := card_mul_inv_cancel (T → Msg)
  have iY := card_mul_inv_cancel (T → Y)
  have iH := card_mul_inv_cancel (T × Msg → Y)
  set cS : ℝ≥0∞ := (Fintype.card (T → Msg) : ℝ≥0∞)
  set cY : ℝ≥0∞ := (Fintype.card (T → Y) : ℝ≥0∞)
  set cH : ℝ≥0∞ := (Fintype.card (T × Msg → Y) : ℝ≥0∞)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun xs _ ↦ ?_
    refine (sum_udReprog xs fun y H ↦ (cS⁻¹ * (cY⁻¹ * cH⁻¹)) * g y H).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    calc cY * (cS⁻¹ * (cY⁻¹ * cH⁻¹) * g (udTargets xs H) H)
        = (cY * cY⁻¹) * (cS⁻¹ * cH⁻¹ * g (udTargets xs H) H) := by ring
      _ = _ := by rw [iY, one_mul]
  · rw [Fintype.sum_prod_type]
    dsimp only
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    calc cS * (cS⁻¹ * (cY⁻¹ * cH⁻¹) * g y H)
        = (cS * cS⁻¹) * (cY⁻¹ * cH⁻¹ * g y H) := by ring
      _ = _ := by rw [iS, one_mul]
  · refine le_of_eq ?_
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    calc cS * (cY * cH * (cS⁻¹ * (cY⁻¹ * cH⁻¹)))
        = (cS * cS⁻¹) * (cY * cY⁻¹) * (cH * cH⁻¹) := by ring
      _ = 1 := by rw [iS, iY, iH]; simp

/-- **Multi-target undetectability of a random tweakable function (real ≤ ideal).**
`H : T × Msg → Y` uniform.  Real: `x* : T → Msg` uniform and hidden, targets
`y t = H (t, x* t)`.  Ideal: targets `y : T → Y` uniform and independent of `H`.  The `q`-query
algorithm `M y` gets the targets and quantum access to `H`; `E y` is any event of the targets and
the leaf.  Then `Pr_real[E] ≤ Pr_ideal[E] + 4 q / √|Msg|`, independently of the number of tweaks.
(One-way-to-hiding bound, not tight.) -/
theorem ud_real_le_ideal_add [Nonempty T] [Nonempty Msg] [Nonempty Y]
    (M : (T → Y) → HybridModel (T × Msg) Y Leaf q) (E : (T → Y) → Leaf → Prop) :
    ∑ xs : T → Msg, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Msg) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          (M (udTargets xs H)).prob H (E (udTargets xs H)) ≤
      ∑ y : T → Y, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          (M y).prob H (E y) +
        4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  obtain ⟨e1, e2, hw⟩ := ud_coupling (T := T) (Msg := Msg) (Y := Y)
    fun y H ↦ (M y).prob H (E y)
  have h := (ud_hidden (T := T) (Msg := Msg) (Y := Y) _).real_le_hyb_add hw (fun v ↦ M v.1)
    (fun ω ↦ udReprog ω.1 ω.2.1 ω.2.2) (fun v ↦ v.2) ud_differ (fun v ↦ E v.1)
  rw [← e1, ← e2]
  exact h

/-- **Multi-target undetectability of a random tweakable function (ideal ≤ real).** -/
theorem ud_ideal_le_real_add [Nonempty T] [Nonempty Msg] [Nonempty Y]
    (M : (T → Y) → HybridModel (T × Msg) Y Leaf q) (E : (T → Y) → Leaf → Prop) :
    ∑ y : T → Y, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          (M y).prob H (E y) ≤
      ∑ xs : T → Msg, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Msg) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          (M (udTargets xs H)).prob H (E (udTargets xs H)) +
        4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  obtain ⟨e1, e2, hw⟩ := ud_coupling (T := T) (Msg := Msg) (Y := Y)
    fun y H ↦ (M y).prob H (E y)
  have h := (ud_hidden (T := T) (Msg := Msg) (Y := Y) _).hyb_le_real_add hw (fun v ↦ M v.1)
    (fun ω ↦ udReprog ω.1 ω.2.1 ω.2.2) (fun v ↦ v.2) ud_differ (fun v ↦ E v.1)
  rw [← e1, ← e2]
  exact h

section Program

variable [AddCommGroup Y] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Multi-target undetectability, program level (real ≤ ideal).**  The program `x y`, its
initial state `ρ y` and the event `E y` may depend on the targets `y`. -/
theorem ud_qprob_real_le_ideal_add [Nonempty T] [Nonempty Msg] (I : L.Interp)
    (x : (T → Y) → QuantumComp L (qromSpec (T × Msg) Y) W A) (ρ : (T → Y) → SubState A) (q : ℕ)
    (hx : ∀ y, QueryBounded (x y) q) (E : (T → Y) → (Σ u, W u) → Prop) :
    ∑ xs : T → Msg, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Msg) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          qprob I H (x (udTargets xs H)) (ρ (udTargets xs H)) (E (udTargets xs H)) ≤
      ∑ y : T → Y, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          qprob I H (x y) (ρ y) (E y) +
        4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  ud_real_le_ideal_add (fun y ↦ HybridModel.ofProgram I (x y) (ρ y) q (hx y) (E y)) fun _ ↦ id

/-- **Multi-target undetectability, program level (ideal ≤ real).** -/
theorem ud_qprob_ideal_le_real_add [Nonempty T] [Nonempty Msg] (I : L.Interp)
    (x : (T → Y) → QuantumComp L (qromSpec (T × Msg) Y) W A) (ρ : (T → Y) → SubState A) (q : ℕ)
    (hx : ∀ y, QueryBounded (x y) q) (E : (T → Y) → (Σ u, W u) → Prop) :
    ∑ y : T → Y, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          qprob I H (x y) (ρ y) (E y) ≤
      ∑ xs : T → Msg, ∑ H : T × Msg → Y,
        ((Fintype.card (T → Msg) : ℝ≥0∞)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹) *
          qprob I H (x (udTargets xs H)) (ρ (udTargets xs H)) (E (udTargets xs H)) +
        4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  ud_ideal_le_real_add (fun y ↦ HybridModel.ofProgram I (x y) (ρ y) q (hx y) (E y)) fun _ ↦ id

end Program

end UD

/-! ## 3. Decisional second-preimage resistance -/

section World

variable {Ω V X : Type} [Fintype Ω] [Fintype X] [DecidableEq X] {w : Ω → ℝ≥0∞} {view : Ω → V}
  {S : Ω → Finset X} {ε : ℝ≥0∞} {Y : Type} [DecidableEq Y]

/-- Square-root closeness of the real and hybrid worlds for events that may depend on the whole
world `ω` (not only on the view).  Same proof as `Hidden.sqrt_real_le_sqrt_hyb`. -/
private theorem Hidden.sqrt_world (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (E : Ω → Leaf → Prop) :
    (∑ ω, w ω * (M (view ω)).prob (Hreal ω) (E ω)) ^ (2⁻¹ : ℝ) ≤
        (∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (E ω)) ^ (2⁻¹ : ℝ) +
          2 * q * ε ^ (2⁻¹ : ℝ) ∧
    (∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (E ω)) ^ (2⁻¹ : ℝ) ≤
        (∑ ω, w ω * (M (view ω)).prob (Hreal ω) (E ω)) ^ (2⁻¹ : ℝ) +
          2 * q * ε ^ (2⁻¹ : ℝ) := by
  classical
  have hsub : ∀ ω, ∑ k ∈ univ.filter (fun k ↦ Hreal ω k ≠ Ghyb (view ω) k),
      (M (view ω)).mass (Ghyb (view ω)) k ≤ ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k :=
    fun ω ↦ Finset.sum_le_sum_of_subset fun k hk ↦ hS ω k (Finset.mem_filter.1 hk).2
  have hmass : (∑ ω, w ω * (4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k)) ^
      (2⁻¹ : ℝ) ≤ 2 * q * ε ^ (2⁻¹ : ℝ) := by
    rw [← sqrt_four_mul]
    refine sqrt_le_sqrt ?_
    have h := hH.sum_le hw (fun v k ↦ (M v).mass (Ghyb v) k) q fun v ↦ (M v).mass_sum_le _
    calc ∑ ω, w ω * (4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k)
        = 4 * q * ∑ ω, w ω * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ ↦ mul_left_comm _ _ _
      _ ≤ 4 * q * (ε * q) := by gcongr
  have h1 : ∀ ω, (M (view ω)).prob (Hreal ω) (E ω) ^ (2⁻¹ : ℝ) ≤
      (M (view ω)).prob (Ghyb (view ω)) (E ω) ^ (2⁻¹ : ℝ) +
        (4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k) ^ (2⁻¹ : ℝ) := fun ω ↦
    ((M (view ω)).hybrid (Hreal ω) (Ghyb (view ω)) (E ω)).trans
      (add_le_add le_rfl (sqrt_le_sqrt (mul_le_mul' le_rfl (hsub ω))))
  have h2 : ∀ ω, (M (view ω)).prob (Ghyb (view ω)) (E ω) ^ (2⁻¹ : ℝ) ≤
      (M (view ω)).prob (Hreal ω) (E ω) ^ (2⁻¹ : ℝ) +
        (4 * q * ∑ k ∈ S ω, (M (view ω)).mass (Ghyb (view ω)) k) ^ (2⁻¹ : ℝ) := fun ω ↦
    ((M (view ω)).hybrid' (Hreal ω) (Ghyb (view ω)) (E ω)).trans
      (add_le_add le_rfl (sqrt_le_sqrt (mul_le_mul' le_rfl (hsub ω))))
  exact ⟨(sqrt_sum_le w _ _ _ h1).trans (add_le_add le_rfl hmass),
    (sqrt_sum_le w _ _ _ h2).trans (add_le_add le_rfl hmass)⟩

/-- **Two-world closeness for world-dependent events.**  As `Hidden.real_le_hyb_add`, but the
event `E ω` may depend on the hidden part of the world: `P_real ≤ P_hyb + 4 q √ε`. -/
theorem Hidden.real_le_hyb_add_world [Nonempty X] (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (E : Ω → Leaf → Prop) :
    ∑ ω, w ω * (M (view ω)).prob (Hreal ω) (E ω) ≤
      ∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (E ω) + 4 * q * ε ^ (2⁻¹ : ℝ) := by
  have h := le_add_two_mul_of_sqrt_le
    (sum_mul_prob_le_one hw (fun ω ↦ M (view ω)) Hreal E)
    (sum_mul_prob_le_one hw (fun ω ↦ M (view ω)) (fun ω ↦ Ghyb (view ω)) E)
    (hH.sqrt_world hw M Hreal Ghyb hS E).1
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **Two-world closeness for world-dependent events, converse.** `P_hyb ≤ P_real + 4 q √ε`. -/
theorem Hidden.hyb_le_real_add_world [Nonempty X] (hH : Hidden w view S ε) (hw : ∑ ω, w ω ≤ 1)
    (M : V → HybridModel X Y Leaf q) (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) (E : Ω → Leaf → Prop) :
    ∑ ω, w ω * (M (view ω)).prob (Ghyb (view ω)) (E ω) ≤
      ∑ ω, w ω * (M (view ω)).prob (Hreal ω) (E ω) + 4 * q * ε ^ (2⁻¹ : ℝ) := by
  have h := le_add_two_mul_of_sqrt_le
    (sum_mul_prob_le_one hw (fun ω ↦ M (view ω)) (fun ω ↦ Ghyb (view ω)) E)
    (sum_mul_prob_le_one hw (fun ω ↦ M (view ω)) Hreal E)
    (hH.sqrt_world hw M Hreal Ghyb hS E).2
  calc _ ≤ _ := h
    _ = _ := by ring

/-- An event and its complement have total probability at most one (needs two points of `X`,
because the interface only speaks about `X`-valued decodings of the leaf). -/
theorem HybridModel.prob_add_not_le_one [Nontrivial X] (M : HybridModel X Y Leaf q) (H : X → Y)
    (b : Leaf → Prop) : M.prob H b + M.prob H (fun p ↦ ¬ b p) ≤ 1 := by
  classical
  obtain ⟨x0, x1, hne⟩ := exists_pair_ne X
  let out : Leaf → X := fun p ↦ if b p then x0 else x1
  calc M.prob H b + M.prob H (fun p ↦ ¬ b p)
      ≤ M.prob H (fun p ↦ out p = x0) + M.prob H (fun p ↦ out p = x1) :=
        add_le_add (M.prob_mono H fun p hp ↦ by simp [out, hp])
          (M.prob_mono H fun p hp ↦ by simp [out, hp])
    _ = ∑ k ∈ {x0, x1}, M.prob H (fun p ↦ out p = k) := (Finset.sum_pair (f := fun k ↦ M.prob H (fun p ↦ out p = k)) hne).symm
    _ ≤ ∑ k, M.prob H (fun p ↦ out p = k) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ 1 := M.prob_sum_le H out

end World

section ProdCoord

variable {T Z X : Type} [Fintype T] [DecidableEq Z] [Fintype X] [DecidableEq X]

/-- Change of variables on a whole set `s` of coordinates at once: if the weight `a` and the
constant `β` have the same push-forward under `c`, then under a sum over `τ : X → T` whose
remaining summand sees the coordinates in `s` only through `c ∘ τ`, the product weight
`∏ k ∈ s, a (τ k)` can be replaced by `β ^ |s|`. -/
theorem sum_prod_coord_change (c : T → Z) (a : T → ℝ≥0∞) (β : ℝ≥0∞)
    (h : ∀ z, ∑ t with c t = z, a t = ∑ t with c t = z, β) (s : Finset X)
    (Φ : (X → Z) → (X → T) → ℝ≥0∞)
    (hΦ : ∀ g τ k t, k ∈ s → Φ g (Function.update τ k t) = Φ g τ) :
    ∑ τ : X → T, (∏ k ∈ s, a (τ k)) * Φ (c ∘ τ) τ = β ^ s.card * ∑ τ : X → T, Φ (c ∘ τ) τ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have ih' := ih fun g τ k' t hk' ↦ hΦ g τ k' t (Finset.mem_insert_of_mem hk')
    have hupd : ∀ τ : X → T, Function.update (c ∘ τ) k (c (τ k)) = c ∘ τ := fun τ ↦
      Function.update_eq_self k (c ∘ τ)
    have e := sum_coord_change k c c a (fun _ ↦ β) h
      (fun z τ ↦ (∏ j ∈ s, a (τ j)) * Φ (Function.update (c ∘ τ) k z) τ) (by
        intro z τ t
        have h1 : ∏ j ∈ s, a (Function.update τ k t j) = ∏ j ∈ s, a (τ j) :=
          Finset.prod_congr rfl fun j hj ↦ by
            rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hk)]
        have h2 : Function.update (c ∘ Function.update τ k t) k z =
            Function.update (c ∘ τ) k z := by
          funext j
          by_cases hj : j = k
          · subst hj; simp
          · simp [Function.update, hj]
        rw [h1, h2, hΦ _ _ k t (Finset.mem_insert_self _ _)])
    simp only [hupd] at e
    calc ∑ τ : X → T, (∏ j ∈ insert k s, a (τ j)) * Φ (c ∘ τ) τ
        = ∑ τ : X → T, a (τ k) * ((∏ j ∈ s, a (τ j)) * Φ (c ∘ τ) τ) :=
          Finset.sum_congr rfl fun τ _ ↦ by rw [Finset.prod_insert hk, mul_assoc]
      _ = ∑ τ : X → T, β * ((∏ j ∈ s, a (τ j)) * Φ (c ∘ τ) τ) := e
      _ = β * (β ^ s.card * ∑ τ : X → T, Φ (c ∘ τ) τ) := by rw [← Finset.mul_sum, ih']
      _ = _ := by rw [Finset.card_insert_of_notMem hk, pow_succ]; ring

end ProdCoord

section DSPR

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- `x` has a second preimage under `H`. -/
def SecondPreimage (H : X → Y) (x : X) : Prop := ∃ x', x' ≠ x ∧ H x' = H x

/-- Indicator (as a product over the other points) that `x` has NO second preimage under `H`. -/
noncomputable def noSPw (H : X → Y) (x : X) : ℝ≥0∞ := ∏ k ∈ univ.erase x, if H k ≠ H x then 1 else 0

theorem noSPw_of_SP {H : X → Y} {x : X} (h : SecondPreimage H x) : noSPw H x = 0 := by
  obtain ⟨x', h1, h2⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h1, Finset.mem_univ _⟩) (by simp [h2])

theorem noSPw_of_not_SP {H : X → Y} {x : X} (h : ¬ SecondPreimage H x) : noSPw H x = 1 :=
  Finset.prod_eq_one fun k hk ↦ by
    have hne : H k ≠ H x := fun e ↦ h ⟨k, (Finset.mem_erase.1 hk).1, e⟩
    simp [hne]

/-- The DSPR hybrid function: every second preimage of `y = H x` is resampled away from `y`;
the point `x` keeps its value. -/
def dsprHyb (x : X) (τ : X → Y × NZ Y) : X → Y :=
  Function.update (fun k ↦ resample (τ x).1 (τ k)) x (τ x).1

/-- The marked set of the DSPR coupling: the second preimages of `H x`. -/
def dsprMarked (ω : X × (X → Y × NZ Y)) : Finset X :=
  univ.filter fun k ↦ k ≠ ω.1 ∧ (ω.2 k).1 = (ω.2 ω.1).1

theorem dspr_differ (ω : X × (X → Y × NZ Y)) (k : X)
    (h : (ω.2 k).1 ≠ dsprHyb ω.1 ω.2 k) : k ∈ dsprMarked ω := by
  simp only [dsprMarked, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hne
  refine h ?_
  by_cases hk : k = ω.1
  · rw [hk]; simp [dsprHyb]
  · have hv : (ω.2 k).1 ≠ (ω.2 ω.1).1 := fun e ↦ hne ⟨hk, e⟩
    simp [dsprHyb, Function.update, hk, resample, hv]

/-- Given the hybrid value, a point is unmarked with probability `1 - 1/|Y|`. -/
theorem resample_fiber_ne (y z : Y) :
    ∑ t : Y × NZ Y with resample y t = z, (if t.1 ≠ y then (1 : ℝ≥0∞) else 0) =
      ∑ t : Y × NZ Y with resample y t = z, (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) := by
  have hc : (Fintype.card Y : ℝ≥0∞)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.2 (by exact_mod_cast Fintype.card_pos (α := Y))
  have hadd : (∑ t : Y × NZ Y with resample y t = z, (if t.1 = y then (1 : ℝ≥0∞) else 0)) +
      ∑ t : Y × NZ Y with resample y t = z, (if t.1 ≠ y then (1 : ℝ≥0∞) else 0) =
      (∑ t : Y × NZ Y with resample y t = z, (Fintype.card Y : ℝ≥0∞)⁻¹) +
        ∑ t : Y × NZ Y with resample y t = z, (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [add_tsub_cancel_of_le hc]
    by_cases ht : t.1 = y <;> simp [ht]
  rw [resample_fiber] at hadd
  exact (ENNReal.add_right_inj
    (ENNReal.sum_ne_top.2 fun _ _ ↦ ne_top_of_le_ne_top one_ne_top hc)).1 hadd

/-- **Independence engine for the DSPR coupling.**  For a fixed challenge point `x` and a set `s`
of other points: a product weight over `s` whose factors have push-forward `β` under the
resampling map is independent of the hybrid function. -/
theorem dspr_indep (x : X) (s : Finset X) (hs : x ∉ s) (a : Y → Y × NZ Y → ℝ≥0∞) (β : ℝ≥0∞)
    (h : ∀ y z, ∑ t : Y × NZ Y with resample y t = z, a y t =
      ∑ t : Y × NZ Y with resample y t = z, β) (φ : (X → Y) → ℝ≥0∞) :
    ∑ τ : X → Y × NZ Y, (∏ k ∈ s, a (τ x).1 (τ k)) * φ (dsprHyb x τ) =
      β ^ s.card * ∑ τ : X → Y × NZ Y, φ (dsprHyb x τ) := by
  have hy : ∀ y : Y, ∑ τ : X → Y × NZ Y, (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) *
        ((∏ k ∈ s, a y (τ k)) * φ (Function.update (fun k ↦ resample y (τ k)) x y)) =
      β ^ s.card * ∑ τ : X → Y × NZ Y, (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) *
        φ (Function.update (fun k ↦ resample y (τ k)) x y) := by
    intro y
    have e := sum_prod_coord_change (resample y) (a y) β (h y) s
      (fun g τ ↦ (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) * φ (Function.update g x y))
      (by
        intro g τ k t hk
        have hx : Function.update τ k t x = τ x :=
          Function.update_of_ne (fun e ↦ hs (by rw [e]; exact hk)) _ _
        simp only [hx])
    simp only [Function.comp_def] at e
    rw [← e]
    exact Finset.sum_congr rfl fun τ _ ↦ mul_left_comm _ _ _
  calc ∑ τ : X → Y × NZ Y, (∏ k ∈ s, a (τ x).1 (τ k)) * φ (dsprHyb x τ)
      = ∑ y : Y, ∑ τ : X → Y × NZ Y, (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) *
          ((∏ k ∈ s, a y (τ k)) * φ (Function.update (fun k ↦ resample y (τ k)) x y)) :=
        sum_split_value x fun y τ ↦
          (∏ k ∈ s, a y (τ k)) * φ (Function.update (fun k ↦ resample y (τ k)) x y)
    _ = ∑ y : Y, β ^ s.card * ∑ τ : X → Y × NZ Y, (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) *
          φ (Function.update (fun k ↦ resample y (τ k)) x y) :=
        Finset.sum_congr rfl fun y _ ↦ hy y
    _ = β ^ s.card * ∑ τ : X → Y × NZ Y, φ (dsprHyb x τ) := by
        rw [← Finset.mul_sum]
        congr 1
        exact (sum_split_value x fun y τ ↦
          φ (Function.update (fun k ↦ resample y (τ k)) x y)).symm

/-- The second preimages of `H x` are `1/|Y|`-hidden from the view `(x, G)`. -/
theorem dspr_hidden (κ : ℝ≥0∞) :
    Hidden (Ω := X × (X → Y × NZ Y)) (fun _ ↦ κ) (fun ω ↦ (ω.1, dsprHyb ω.1 ω.2)) dsprMarked
      (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  intro k φ
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  by_cases hk : k = x
  · have hm : ∀ τ : X → Y × NZ Y, k ∉ dsprMarked (x, τ) := by
      intro τ; simp [dsprMarked, hk]
    simp [hm]
  · have e := dspr_indep x {k} (fun h ↦ hk (Finset.mem_singleton.1 h).symm)
      (fun y t ↦ if t.1 = y then (1 : ℝ≥0∞) else 0) _ (fun y z ↦ resample_fiber y z)
      (fun G ↦ κ * φ (x, G))
    simp only [Finset.prod_singleton, Finset.card_singleton, pow_one] at e
    refine le_of_eq (Eq.trans (Finset.sum_congr rfl fun τ _ ↦ ?_) e)
    have hm : k ∈ dsprMarked (x, τ) ↔ (τ k).1 = (τ x).1 := by simp [dsprMarked, hk]
    by_cases hv : (τ k).1 = (τ x).1 <;> simp [hm, hv]

/-- The DSPR coupling: worlds `(x, τ)` uniform, real function `fst ∘ τ`. -/
private theorem dspr_coupling [Nonempty X] [Nontrivial Y] (g : X → (X → Y) → ℝ≥0∞) :
    (∑ ω : X × (X → Y × NZ Y),
        ((Fintype.card X : ℝ≥0∞)⁻¹ * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (X → NZ Y) : ℝ≥0∞)⁻¹) * g ω.1 (fun k ↦ (ω.2 k).1) =
      ∑ H : X → Y, ∑ x : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) * g x H) ∧
    ∑ _ω : X × (X → Y × NZ Y),
        ((Fintype.card X : ℝ≥0∞)⁻¹ * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (X → NZ Y) : ℝ≥0∞)⁻¹) = 1 := by
  obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
  have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
  have iX := card_mul_inv_cancel X
  have iXY := card_mul_inv_cancel (X → Y)
  have iXD := card_mul_inv_cancel (X → NZ Y)
  set cX : ℝ≥0∞ := (Fintype.card X : ℝ≥0∞)
  set cXY : ℝ≥0∞ := (Fintype.card (X → Y) : ℝ≥0∞)
  set cXD : ℝ≥0∞ := (Fintype.card (X → NZ Y) : ℝ≥0∞)
  refine ⟨?_, ?_⟩
  · rw [Fintype.sum_prod_type, Finset.sum_comm (γ := X → Y)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have e := sum_fst_comp (X := X) (A := Y) (B := NZ Y)
      (fun H ↦ (cX⁻¹ * cXY⁻¹ * cXD⁻¹) * g x H)
    refine e.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    calc cXD * (cX⁻¹ * cXY⁻¹ * cXD⁻¹ * g x H)
        = (cXD * cXD⁻¹) * (cXY⁻¹ * cX⁻¹ * g x H) := by ring
      _ = _ := by rw [iXD, one_mul]
  · rw [Fintype.sum_prod_type]
    have e := sum_fst_comp (X := X) (A := Y) (B := NZ Y) (fun _ ↦ cX⁻¹ * cXY⁻¹ * cXD⁻¹)
    simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc cX * (cXD * (cXY * (cX⁻¹ * cXY⁻¹ * cXD⁻¹)))
        = (cX * cX⁻¹) * ((cXY * cXY⁻¹) * (cXD * cXD⁻¹)) := by ring
      _ = 1 := by rw [iX, iXY, iXD]; simp

/-- In the coupled worlds, "no second preimage" is independent of the view `(x, G)` and has
probability exactly `(1 - 1/|Y|)^(|X|-1)`. -/
theorem dspr_noSP_indep (κ : ℝ≥0∞) (P : X × (X → Y) → ℝ≥0∞) :
    ∑ ω : X × (X → Y × NZ Y),
        noSPw (fun k ↦ (ω.2 k).1) ω.1 * (κ * P (ω.1, dsprHyb ω.1 ω.2)) =
      (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) *
        ∑ ω : X × (X → Y × NZ Y), κ * P (ω.1, dsprHyb ω.1 ω.2) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have e := dspr_indep x (univ.erase x) (Finset.notMem_erase x _)
    (fun y t ↦ if t.1 ≠ y then (1 : ℝ≥0∞) else 0) _ (fun y z ↦ resample_fiber_ne y z)
    (fun G ↦ κ * P (x, G))
  rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ] at e
  exact e

/-- **Exact probability of having no second preimage.** -/
theorem dspr_prob_noSP [Nonempty X] [Nontrivial Y] :
    ∑ H : X → Y, ∑ x : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) * noSPw H x =
      (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) := by
  obtain ⟨e1, e2⟩ := dspr_coupling (X := X) (Y := Y) fun x H ↦ noSPw H x
  have h := dspr_noSP_indep (X := X) (Y := Y)
    ((Fintype.card X : ℝ≥0∞)⁻¹ * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
      (Fintype.card (X → NZ Y) : ℝ≥0∞)⁻¹) (fun _ ↦ 1)
  simp only [mul_one] at h
  rw [e2, mul_one] at h
  rw [← e1, ← h]
  exact Finset.sum_congr rfl fun ω _ ↦ mul_comm _ _

/-- The hybrid world: the adversary's bit is a function of the view `(x, G)`, while "second
preimage" is an independent Bernoulli variable, so the adversary is right with probability at
most `max (p, 1 - p)`. -/
private theorem dspr_hyb_le [Nontrivial X] (κ : ℝ≥0∞)
    (hw : ∑ _ω : X × (X → Y × NZ Y), κ ≤ 1) (M : X → HybridModel X Y Leaf q)
    (b : X → Leaf → Prop) :
    ∑ ω : X × (X → Y × NZ Y), κ * (M ω.1).prob (dsprHyb ω.1 ω.2)
        (fun p ↦ b ω.1 p ↔ SecondPreimage (fun k ↦ (ω.2 k).1) ω.1) ≤
      max (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1))
        ((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1)) := by
  set γ : ℝ≥0∞ := (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) with hγdef
  have hγ : γ ≤ 1 := pow_le_one₀ zero_le tsub_le_self
  let P1 : X × (X → Y) → ℝ≥0∞ := fun v ↦ (M v.1).prob v.2 (b v.1)
  let P0 : X × (X → Y) → ℝ≥0∞ := fun v ↦ (M v.1).prob v.2 (fun p ↦ ¬ b v.1 p)
  set A1 : ℝ≥0∞ := ∑ ω : X × (X → Y × NZ Y), κ * P1 (ω.1, dsprHyb ω.1 ω.2) with hA1
  set A0 : ℝ≥0∞ := ∑ ω : X × (X → Y × NZ Y), κ * P0 (ω.1, dsprHyb ω.1 ω.2) with hA0
  set Hy : ℝ≥0∞ := ∑ ω : X × (X → Y × NZ Y), κ * (M ω.1).prob (dsprHyb ω.1 ω.2)
        (fun p ↦ b ω.1 p ↔ SecondPreimage (fun k ↦ (ω.2 k).1) ω.1) with hHy
  have hterm : ∀ ω : X × (X → Y × NZ Y),
      κ * (M ω.1).prob (dsprHyb ω.1 ω.2)
          (fun p ↦ b ω.1 p ↔ SecondPreimage (fun k ↦ (ω.2 k).1) ω.1) +
        noSPw (fun k ↦ (ω.2 k).1) ω.1 * (κ * P1 (ω.1, dsprHyb ω.1 ω.2)) =
      κ * P1 (ω.1, dsprHyb ω.1 ω.2) +
        noSPw (fun k ↦ (ω.2 k).1) ω.1 * (κ * P0 (ω.1, dsprHyb ω.1 ω.2)) := by
    intro ω
    by_cases hsp : SecondPreimage (fun k ↦ (ω.2 k).1) ω.1
    · have hev : (fun p ↦ b ω.1 p ↔ SecondPreimage (fun k ↦ (ω.2 k).1) ω.1) = b ω.1 := by
        funext p; simp [hsp]
      rw [noSPw_of_SP hsp, hev, zero_mul, zero_mul, add_zero]
    · have hev : (fun p ↦ b ω.1 p ↔ SecondPreimage (fun k ↦ (ω.2 k).1) ω.1) =
          fun p ↦ ¬ b ω.1 p := by
        funext p; simp [hsp]
      rw [noSPw_of_not_SP hsp, hev, one_mul, one_mul]
      exact add_comm _ _
  have hsum : Hy + γ * A1 = A1 + γ * A0 := by
    rw [hA1, hA0, hγdef, ← dspr_noSP_indep κ P1, ← dspr_noSP_indep κ P0, hHy,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ ↦ hterm ω
  have hA : A1 + A0 ≤ 1 := by
    rw [hA1, hA0, ← Finset.sum_add_distrib]
    calc ∑ ω : X × (X → Y × NZ Y),
          (κ * P1 (ω.1, dsprHyb ω.1 ω.2) + κ * P0 (ω.1, dsprHyb ω.1 ω.2))
        ≤ ∑ _ω : X × (X → Y × NZ Y), κ := by
          refine Finset.sum_le_sum fun ω _ ↦ ?_
          rw [← mul_add]
          calc κ * (P1 (ω.1, dsprHyb ω.1 ω.2) + P0 (ω.1, dsprHyb ω.1 ω.2)) ≤ κ * 1 := by
                gcongr
                exact (M ω.1).prob_add_not_le_one _ _
            _ = κ := mul_one _
      _ ≤ 1 := hw
  have hsplit : A1 = (1 - γ) * A1 + γ * A1 := by
    rw [← add_mul, tsub_add_cancel_of_le hγ, one_mul]
  have hfin : γ * A1 ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (mul_le_one' hγ (le_self_add.trans hA))
  have heq : Hy = (1 - γ) * A1 + γ * A0 := by
    have h3 : Hy + γ * A1 = ((1 - γ) * A1 + γ * A0) + γ * A1 :=
      calc Hy + γ * A1 = A1 + γ * A0 := hsum
        _ = ((1 - γ) * A1 + γ * A1) + γ * A0 := by rw [← hsplit]
        _ = _ := add_right_comm _ _ _
    exact (ENNReal.add_left_inj hfin).1 h3
  calc Hy = (1 - γ) * A1 + γ * A0 := heq
    _ ≤ max (1 - γ) γ * A1 + max (1 - γ) γ * A0 :=
        add_le_add (mul_le_mul' (le_max_left _ _) le_rfl) (mul_le_mul' (le_max_right _ _) le_rfl)
    _ = max (1 - γ) γ * (A1 + A0) := (mul_add _ _ _).symm
    _ ≤ max (1 - γ) γ * 1 := mul_le_mul' le_rfl hA
    _ = _ := mul_one _

/-- **Decisional second-preimage resistance of a random function.**  Experiment: `H : X → Y`
uniform, `x : X` uniform; the `q`-query algorithm `M x` gets `x` and quantum access to `H` and
outputs a bit `b x p`; it wins iff the bit says correctly whether `x` has a second preimage under
`H`.  With `1 - p = (1 - 1/|Y|)^(|X|-1)` the exact probability of having no second preimage
(`dspr_prob_noSP`), the winning probability is at most `max (p, 1 - p) + 4 q / √|Y|`, i.e. at
most the trivial guessing probability plus a one-way-to-hiding term.  (Not claimed tight.) -/
theorem dspr_le (M : X → HybridModel X Y Leaf q) (b : X → Leaf → Prop) :
    ∑ H : X → Y, ∑ x : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          (M x).prob H (fun p ↦ b x p ↔ SecondPreimage H x) ≤
      max (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1))
          ((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1)) +
        4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp
  have hle1 : ∑ H : X → Y, ∑ x : X,
      ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
        (M x).prob H (fun p ↦ b x p ↔ SecondPreimage H x) ≤ 1 :=
    calc ∑ H : X → Y, ∑ x : X,
          ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
            (M x).prob H (fun p ↦ b x p ↔ SecondPreimage H x)
        ≤ ∑ _H : X → Y, ∑ _x : X,
          ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) * 1 := by
          gcongr with H _ x _
          exact (M x).prob_le_one _ _
      _ = ((Fintype.card (X → Y) : ℝ≥0∞) * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹) *
            ((Fintype.card X : ℝ≥0∞) * (Fintype.card X : ℝ≥0∞)⁻¹) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          ring
      _ = 1 := by rw [card_mul_inv_cancel, card_mul_inv_cancel, one_mul]
  by_cases hY1 : Fintype.card Y = 1
  · refine hle1.trans (le_add_right (le_of_eq ?_))
    rw [hY1]
    rcases Nat.eq_zero_or_pos (Fintype.card X - 1) with h0 | h0
    · simp [h0]
    · simp [h0.ne']
  by_cases hX1 : Fintype.card X = 1
  · refine hle1.trans (le_add_right (le_of_eq ?_))
    simp [hX1]
  have hYnt : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.1
    (by have := Fintype.card_pos (α := Y); omega)
  have hXnt : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.1
    (by have := Fintype.card_pos (α := X); omega)
  obtain ⟨e1, e2⟩ := dspr_coupling (X := X) (Y := Y)
    fun x H ↦ (M x).prob H (fun p ↦ b x p ↔ SecondPreimage H x)
  have hyb := (dspr_hidden (X := X) (Y := Y) _).real_le_hyb_add_world (le_of_eq e2)
    (fun v ↦ M v.1) (fun ω k ↦ (ω.2 k).1) (fun v ↦ v.2) dspr_differ
    (fun ω p ↦ b ω.1 p ↔ SecondPreimage (fun k ↦ (ω.2 k).1) ω.1)
  rw [← e1]
  exact hyb.trans (add_le_add (dspr_hyb_le _ (le_of_eq e2) M b) le_rfl)

section Program

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Decisional second-preimage resistance, program level.**  The program `x k`, its initial
state `ρ k` and the bit decoding `b k` may depend on the challenge point `k`. -/
theorem dspr_qprob_le (I : L.Interp) (x : X → QuantumComp L (qromSpec X Y) W A)
    (ρ : X → SubState A) (q : ℕ) (hx : ∀ k, QueryBounded (x k) q)
    (b : X → (Σ u, W u) → Prop) :
    ∑ H : X → Y, ∑ k : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          qprob I H (x k) (ρ k) (fun p ↦ b k p ↔ SecondPreimage H k) ≤
      max (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1))
          ((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1)) +
        4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  dspr_le (fun k ↦ HybridModel.ofProgram I (x k) (ρ k) q (hx k) (b k)) fun _ leaf ↦ leaf

end Program

end DSPR

end PQ.QROM

#print axioms PQ.QROM.prf_real_le_ideal_add
#print axioms PQ.QROM.prf_ideal_le_real_add
#print axioms PQ.QROM.prf_qprob_real_le_ideal_add
#print axioms PQ.QROM.prf_qprob_ideal_le_real_add
#print axioms PQ.QROM.ud_real_le_ideal_add
#print axioms PQ.QROM.ud_ideal_le_real_add
#print axioms PQ.QROM.ud_qprob_real_le_ideal_add
#print axioms PQ.QROM.ud_qprob_ideal_le_real_add
#print axioms PQ.QROM.Hidden.real_le_hyb_add_world
#print axioms PQ.QROM.Hidden.hyb_le_real_add_world
#print axioms PQ.QROM.dspr_prob_noSP
#print axioms PQ.QROM.dspr_le
#print axioms PQ.QROM.dspr_qprob_le
