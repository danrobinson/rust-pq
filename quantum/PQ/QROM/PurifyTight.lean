import PQ.QROM.PurifyProgram

/-!
# The tight hidden-set bound for ALL VCVio programs

`qprob_tight_avg`: for every program `x : QuantumComp L (qromSpec X Y) W A` with
`QueryBounded x q` (adaptive, arbitrary local instruments under any interpretation `I`, mixed
input `ρ`, any leaf event `E`), weights `w s ≥ 0`, functions `Hs s` differing from `G` only on
marked sets `S s` with `∑_{s : k ∈ S s} w s ≤ ε` for every `k`:

`|∑ s, w s * (qprob I (Hs s) x ρ E).toReal - (∑ s, w s) * (qprob I G x ρ E).toReal| ≤ 8 q² ε`.

Proof.  By `PQ/QROM/PurifyProgram.lean` the run of a program on a pure vector is a branch sum:
local operations split the vector into Kraus images (not depending on the oracle), oracle calls
apply the oracle `oracleUnitary H ⊗ 1` of the vector model between two fixed isometries.  The
invariant `pv_tight` is proved by induction on the program: for a reference vector `ψ` (run
against `G`) and deviations `δ s` (run against `Hs s` from `ψ + δ s`), with
`‖ψ‖ ≤ m`, `∑ s, w s ‖δ s‖² ≤ a²`, `‖∑ s, w s • δ s‖ ≤ d`, the weighted difference of the event
weights is at most `Fq r n m a d = 2 m d + a² + 8 n r m a + 8 n² r² m²` (`r = √ε`, `n` the
remaining query budget).  `Fq` is subadditive under Kraus splittings (Cauchy–Schwarz,
`Fq_sum_le`) and absorbs one oracle call exactly (`Fq_query`), using the averaged operator bounds
of `PQ/QROM/TightCore.lean`.  No purification, dilation or padding is needed.
-/

open Quantum Matrix Finset

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM.Purify

open PQ.QROM.Tight

/-- The potential of the induction. -/
def Fq (r : ℝ) (n : ℕ) (m a d : ℝ) : ℝ :=
  2 * m * d + a ^ 2 + 8 * n * r * m * a + 8 * (n : ℝ) ^ 2 * r ^ 2 * m ^ 2

theorem Fq_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) {m a d : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a)
    (hd : 0 ≤ d) : 0 ≤ Fq r n m a d := by
  unfold Fq
  positivity

/-- One oracle call is absorbed exactly. -/
theorem Fq_query (r : ℝ) (n : ℕ) (m a d : ℝ) :
    Fq r n m (a + 2 * r * m) (d + 2 * r ^ 2 * m + 2 * r * a) = Fq r (n + 1) m a d := by
  unfold Fq
  push_cast
  ring

theorem sum_mul_le_of_sq {J : Type*} (t : Finset J) (f g : J → ℝ) {F G : ℝ} (hF : 0 ≤ F)
    (hG : 0 ≤ G) (hf : ∑ j ∈ t, f j ^ 2 ≤ F ^ 2) (hg : ∑ j ∈ t, g j ^ 2 ≤ G ^ 2) :
    ∑ j ∈ t, f j * g j ≤ F * G := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq t f g
  have h2 : (∑ j ∈ t, f j * g j) ^ 2 ≤ (F * G) ^ 2 := by
    rw [mul_pow]
    exact h.trans (mul_le_mul hf hg (Finset.sum_nonneg fun j _ ↦ sq_nonneg _) (sq_nonneg _))
  exact le_of_sq_le_sq h2 (mul_nonneg hF hG)

/-- The potential is subadditive under splittings (Cauchy–Schwarz). -/
theorem Fq_sum_le {J : Type*} (t : Finset J) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (mi ai di : J → ℝ)
    {m a d : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hmi : ∑ j ∈ t, mi j ^ 2 ≤ m ^ 2) (hai : ∑ j ∈ t, ai j ^ 2 ≤ a ^ 2)
    (hdi : ∑ j ∈ t, di j ^ 2 ≤ d ^ 2) :
    ∑ j ∈ t, Fq r n (mi j) (ai j) (di j) ≤ Fq r n m a d := by
  have e : ∑ j ∈ t, Fq r n (mi j) (ai j) (di j) =
      2 * ∑ j ∈ t, mi j * di j + ∑ j ∈ t, ai j ^ 2 + 8 * n * r * ∑ j ∈ t, mi j * ai j +
        8 * (n : ℝ) ^ 2 * r ^ 2 * ∑ j ∈ t, mi j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by unfold Fq; ring
  have h1 := sum_mul_le_of_sq t mi di hm hd hmi hdi
  have h2 := sum_mul_le_of_sq t mi ai hm ha hmi hai
  have c1 : (0 : ℝ) ≤ 8 * n * r := by positivity
  have c2 : (0 : ℝ) ≤ 8 * (n : ℝ) ^ 2 * r ^ 2 := by positivity
  rw [e]
  unfold Fq
  nlinarith [mul_le_mul_of_nonneg_left h2 c1, mul_le_mul_of_nonneg_left hmi c2]

theorem abs_tsum_le {β : Type*} (f : β → ℝ) (C : ℝ) (h : ∀ s : Finset β, ∑ b ∈ s, |f b| ≤ C) :
    |∑' b, f b| ≤ C := by
  have hs : Summable fun b ↦ ‖f b‖ := summable_of_sum_le (fun _ ↦ abs_nonneg _) h
  exact (norm_tsum_le_tsum_norm hs).trans (Real.tsum_le_of_sum_le (fun _ ↦ abs_nonneg _) h)

/-- Weighted Minkowski inequality in the form needed. -/
theorem sum_mul_add_sq_le {ι : Type*} [Fintype ι] (w x y : ι → ℝ) (hw : ∀ s, 0 ≤ w s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : ∑ s, w s * x s ^ 2 ≤ a ^ 2)
    (hy : ∑ s, w s * y s ^ 2 ≤ b ^ 2) : ∑ s, w s * (x s + y s) ^ 2 ≤ (a + b) ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset ι)
    (r := fun s ↦ w s * x s * y s) (f := fun s ↦ w s * x s ^ 2) (g := fun s ↦ w s * y s ^ 2)
    (fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _)) (fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _))
    (fun s _ ↦ le_of_eq (by ring))
  have h2 : (∑ s, w s * x s * y s) ^ 2 ≤ (a * b) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (mul_le_mul hx hy (Finset.sum_nonneg fun s _ ↦
      mul_nonneg (hw s) (sq_nonneg _)) (sq_nonneg _))
  have h3 := le_of_sq_le_sq h2 (mul_nonneg ha hb)
  have e : ∑ s, w s * (x s + y s) ^ 2 =
      ∑ s, w s * x s ^ 2 + 2 * ∑ s, w s * x s * y s + ∑ s, w s * y s ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  rw [e]
  nlinarith

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w}

section Main

variable {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (Hs : ι → X → Y) (G : X → Y)
  (S : ι → Finset X) (hS : ∀ s k, Hs s k ≠ G k → k ∈ S s) (r : ℝ) (hr : 0 ≤ r)
  (hε : ∀ k, ∑ s with k ∈ S s, w s ≤ r ^ 2)

include hw hS hr hε

/-- `∑_s w_s ‖(O_{H_s} - O_G) φ‖² ≤ 4 r² ‖φ‖²`. -/
theorem sum_norm_D_sq_le {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀]
    (Iq : OracleInterface X Y E₀) (φ : E₀) :
    ∑ s, w s * ‖Iq.D (Hs s) G φ‖ ^ 2 ≤ (2 * r * ‖φ‖) ^ 2 := by
  have h1 := sum_marked_mass_le Iq w hw Hs G S hS (r ^ 2) (sq_nonneg r) hε φ
  calc ∑ s, w s * ‖Iq.D (Hs s) G φ‖ ^ 2
      ≤ ∑ s, w s * (4 * ∑ k ∈ S s, ‖Iq.P k φ‖ ^ 2) :=
        Finset.sum_le_sum fun s _ ↦
          mul_le_mul_of_nonneg_left (Iq.norm_D_sq_le (Hs s) G (S s) (hS s) φ) (hw s)
    _ = 4 * ∑ s, w s * ∑ k ∈ S s, ‖Iq.P k φ‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ ↦ by ring
    _ ≤ 4 * (r ^ 2 * ‖φ‖ ^ 2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

/-- **One oracle call, abstractly.**  `ψ ↦ T' (O_G (T ψ))` on the reference vector and
`ψ + δ s ↦ T' (O_{H_s} (T (ψ + δ s)))` on the deviated ones, for isometries `T`, `T'`: the three
tracked quantities change by at most `m ↦ m`, `a ↦ a + 2 r m`, `d ↦ d + 2 r² m + 2 r a`. -/
theorem query_step {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [NormedAddCommGroup E₃]
    [InnerProductSpace ℂ E₃] (Iq : OracleInterface X Y E₂) (T : E₁ ≃ₗᵢ[ℂ] E₂)
    (T' : E₂ ≃ₗᵢ[ℂ] E₃) (ψ : E₁) (δ : ι → E₁) (m a d : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (_hd : 0 ≤ d) (hψ : ‖ψ‖ ≤ m) (hδ : ∑ s, w s * ‖δ s‖ ^ 2 ≤ a ^ 2)
    (hδbar : ‖∑ s, (w s : ℂ) • δ s‖ ≤ d) :
    ‖T' (Iq.O G (T ψ))‖ ≤ m ∧
    ∑ s, w s * ‖T' (Iq.O (Hs s) (T (ψ + δ s))) - T' (Iq.O G (T ψ))‖ ^ 2 ≤
      (a + 2 * r * m) ^ 2 ∧
    ‖∑ s, (w s : ℂ) • (T' (Iq.O (Hs s) (T (ψ + δ s))) - T' (Iq.O G (T ψ)))‖ ≤
      d + 2 * r ^ 2 * m + 2 * r * a := by
  have key : ∀ s, T' (Iq.O (Hs s) (T (ψ + δ s))) - T' (Iq.O G (T ψ)) =
      T' (Iq.O (Hs s) (T (δ s)) + Iq.D (Hs s) G (T ψ)) := by
    intro s
    simp only [OracleInterface.D, map_add, map_sub]
    abel
  have hTψ : ‖T ψ‖ ≤ m := by rw [LinearIsometryEquiv.norm_map]; exact hψ
  have hD : ∑ s, w s * ‖Iq.D (Hs s) G (T ψ)‖ ^ 2 ≤ (2 * r * m) ^ 2 :=
    (sum_norm_D_sq_le w hw Hs G S hS r hr hε Iq (T ψ)).trans
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hTψ (by positivity)) 2)
  simp only [key]
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact (Iq.O_le G _).trans hTψ
  · refine le_trans (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (hw s))
      (sum_mul_add_sq_le w (fun s ↦ ‖δ s‖) (fun s ↦ ‖Iq.D (Hs s) G (T ψ)‖) hw ha
        (by positivity) hδ hD)
    rw [LinearIsometryEquiv.norm_map]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (Iq.O_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
  · have e : ∑ s, (w s : ℂ) • T' (Iq.O (Hs s) (T (δ s)) + Iq.D (Hs s) G (T ψ)) =
        T' (Iq.O G (T (∑ s, (w s : ℂ) • δ s)) + ∑ s, (w s : ℂ) • Iq.D (Hs s) G (T (δ s)) +
          ∑ s, (w s : ℂ) • Iq.D (Hs s) G (T ψ)) := by
      rw [map_add, map_add, map_sum, map_sum, map_sum, map_sum, map_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      simp only [map_smul, map_add, OracleInterface.D, map_sub, smul_add, smul_sub]
      abel
    rw [e, LinearIsometryEquiv.norm_map]
    have h1 : ‖Iq.O G (T (∑ s, (w s : ℂ) • δ s))‖ ≤ d := by
      refine (Iq.O_le G _).trans ?_
      rw [LinearIsometryEquiv.norm_map]
      exact hδbar
    have h2 : ‖∑ s, (w s : ℂ) • Iq.D (Hs s) G (T (δ s))‖ ≤ 2 * r * a := by
      have h := norm_avg_D_sq_le_var Iq w hw Hs G S hS (r ^ 2) (sq_nonneg r) hε fun s ↦ T (δ s)
      simp only [LinearIsometryEquiv.norm_map] at h
      have h' : ‖∑ s, (w s : ℂ) • Iq.D (Hs s) G (T (δ s))‖ ^ 2 ≤ (2 * r * a) ^ 2 := by
        calc _ ≤ _ := h
          _ ≤ 4 * r ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left hδ (by positivity)
          _ = _ := by ring
      exact le_of_sq_le_sq h' (by positivity)
    have h3 : ‖∑ s, (w s : ℂ) • Iq.D (Hs s) G (T ψ)‖ ≤ 2 * r ^ 2 * m :=
      (norm_avg_D_le_fixed Iq w hw Hs G S hS (r ^ 2) (sq_nonneg r) hε (T ψ)).trans
        (mul_le_mul_of_nonneg_left hTψ (by positivity))
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (Iq.O G (T (∑ s, (w s : ℂ) • δ s)))
      (∑ s, (w s : ℂ) • Iq.D (Hs s) G (T (δ s)))
    linarith

/-- **The invariant of the induction over the program.** -/
theorem pv_tight (I : L.Interp) (E : (Σ u, W u) → Prop) {A : QReg}
    (x : QuantumComp L (qromSpec X Y) W A) :
    ∀ n : ℕ, QueryBounded x n → ∀ (ψ : EuclideanSpace ℂ (A × Unit))
      (δ : ι → EuclideanSpace ℂ (A × Unit)) (m a d : ℝ), 0 ≤ m → 0 ≤ a → 0 ≤ d → ‖ψ‖ ≤ m →
      ∑ s, w s * ‖δ s‖ ^ 2 ≤ a ^ 2 → ‖∑ s, (w s : ℂ) • δ s‖ ≤ d →
      |∑ s, w s * pv I (Hs s) x E (ψ + δ s) - (∑ s, w s) * pv I G x E ψ| ≤ Fq r n m a d := by
  classical
  refine QuantumComp.inductionOn (motive := fun A x ↦ ∀ n : ℕ, QueryBounded x n →
    ∀ (ψ : EuclideanSpace ℂ (A × Unit)) (δ : ι → EuclideanSpace ℂ (A × Unit)) (m a d : ℝ),
      0 ≤ m → 0 ≤ a → 0 ≤ d → ‖ψ‖ ≤ m → ∑ s, w s * ‖δ s‖ ^ 2 ≤ a ^ 2 →
      ‖∑ s, (w s : ℂ) • δ s‖ ≤ d →
      |∑ s, w s * pv I (Hs s) x E (ψ + δ s) - (∑ s, w s) * pv I G x E ψ| ≤ Fq r n m a d)
    ?_ ?_ ?_ x
  · -- leaf
    intro A y n _ ψ δ m a d hm ha hd hψ hδ hδbar
    simp only [pv_pure]
    by_cases hE : E ⟨A, y⟩
    · simp only [hE, ite_true]
      have hterm : ∀ s, w s * ‖ψ + δ s‖ ^ 2 =
          w s * ‖ψ‖ ^ 2 + (2 * (w s * (inner ℂ ψ (δ s)).re) + w s * ‖δ s‖ ^ 2) := fun s ↦ by
        have h := norm_add_sq (𝕜 := ℂ) ψ (δ s)
        simp only [RCLike.re_to_complex] at h
        rw [h]
        ring
      have hre : ∑ s, w s * (inner ℂ ψ (δ s)).re =
          (inner ℂ ψ (∑ s, (w s : ℂ) • δ s)).re := by
        rw [inner_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [inner_smul_right, Complex.re_ofReal_mul]
      have hsum : ∑ s, w s * ‖ψ + δ s‖ ^ 2 - (∑ s, w s) * ‖ψ‖ ^ 2 =
          2 * (inner ℂ ψ (∑ s, (w s : ℂ) • δ s)).re + ∑ s, w s * ‖δ s‖ ^ 2 := by
        simp only [hterm]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          hre]
        ring
      have h1 : |(inner ℂ ψ (∑ s, (w s : ℂ) • δ s)).re| ≤ m * d :=
        (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
          (mul_le_mul hψ hδbar (norm_nonneg _) hm))
      have h2 : 0 ≤ ∑ s, w s * ‖δ s‖ ^ 2 :=
        Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _)
      have c1 : (0 : ℝ) ≤ 8 * n * r * m * a := by positivity
      have c2 : (0 : ℝ) ≤ 8 * (n : ℝ) ^ 2 * r ^ 2 * m ^ 2 := by positivity
      rw [hsum, abs_le]
      have := abs_le.1 h1
      unfold Fq
      constructor <;> nlinarith
    · simp only [hE, ite_false, mul_zero, Finset.sum_const_zero, sub_zero, abs_zero]
      exact Fq_nonneg hr n hm ha hd
  · -- local operation
    intro A o k ih n hq ψ δ m a d hm ha hd hψ hδ hδbar
    have hq' : ∀ b, QueryBounded (k b) n := (QuantumComp.isQueryBound_primBind_iff o k _).1 hq
    obtain ⟨sG, eG⟩ := pv_primBind I G o k E ψ
    have hG := eG ▸ sG.hasSum
    have hs : ∀ s, HasSum (fun b ↦ ∑ c, pv I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)))
        (pv I (Hs s) (QuantumComp.primBind o k) E (ψ + δ s)) := fun s ↦ by
      obtain ⟨ss, es⟩ := pv_primBind I (Hs s) o k E (ψ + δ s)
      exact es ▸ ss.hasSum
    have hT := (hasSum_sum (s := (univ : Finset ι)) fun s _ ↦ (hs s).mul_left (w s)).sub
      (hG.mul_left (∑ s, w s))
    rw [← hT.tsum_eq]
    refine abs_tsum_le _ _ fun t ↦ ?_
    -- per Kraus branch
    let mi : (Σ b : L.Outcome o, (L.next o b × Unit) × (A × Unit)) → ℝ :=
      fun j ↦ ‖primKraus I o j.1 j.2 ψ‖
    let ai : (Σ b : L.Outcome o, (L.next o b × Unit) × (A × Unit)) → ℝ :=
      fun j ↦ Real.sqrt (∑ s, w s * ‖primKraus I o j.1 j.2 (δ s)‖ ^ 2)
    let di : (Σ b : L.Outcome o, (L.next o b × Unit) × (A × Unit)) → ℝ :=
      fun j ↦ ‖primKraus I o j.1 j.2 (∑ s, (w s : ℂ) • δ s)‖
    have hbr : ∀ (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit)),
        |∑ s, w s * pv I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
          (∑ s, w s) * pv I G (k b) E (primKraus I o b c ψ)| ≤
        Fq r n (mi ⟨b, c⟩) (ai ⟨b, c⟩) (di ⟨b, c⟩) := by
      intro b c
      have h := ih b n (hq' b) (primKraus I o b c ψ) (fun s ↦ primKraus I o b c (δ s))
        (mi ⟨b, c⟩) (ai ⟨b, c⟩) (di ⟨b, c⟩) (norm_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _)
        le_rfl
        (le_of_eq (Real.sq_sqrt (Finset.sum_nonneg fun s _ ↦
          mul_nonneg (hw s) (sq_nonneg _))).symm)
        (le_of_eq (by
          simp only [di, map_sum, map_smul]))
      simpa only [map_add] using h
    have hTb : ∀ b, |∑ s, w s * ∑ c, pv I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
        (∑ s, w s) * ∑ c, pv I G (k b) E (primKraus I o b c ψ)| ≤
        ∑ c, Fq r n (mi ⟨b, c⟩) (ai ⟨b, c⟩) (di ⟨b, c⟩) := by
      intro b
      have e : ∑ s, w s * ∑ c, pv I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
          (∑ s, w s) * ∑ c, pv I G (k b) E (primKraus I o b c ψ) =
          ∑ c, (∑ s, w s * pv I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
            (∑ s, w s) * pv I G (k b) E (primKraus I o b c ψ)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.mul_sum]
        simp only [Finset.mul_sum]
      rw [e]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ hbr b c)
    have hsum : ∑ b ∈ t, |(∑ s, w s * ∑ c, pv I (Hs s) (k b) E (primKraus I o b c (ψ + δ s))) -
        (∑ s, w s) * ∑ c, pv I G (k b) E (primKraus I o b c ψ)| ≤
        ∑ j ∈ t.sigma fun _ ↦ univ, Fq r n (mi j) (ai j) (di j) := by
      rw [Finset.sum_sigma]
      exact Finset.sum_le_sum fun b _ ↦ hTb b
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ ↦ ?_)) (hsum.trans ?_)
    · rfl
    refine Fq_sum_le _ hr n mi ai di hm ha hd ?_ ?_ ?_
    · rw [Finset.sum_sigma]
      exact (prim_kraus_sum_le I o t ψ).trans (pow_le_pow_left₀ (norm_nonneg _) hψ 2)
    · rw [Finset.sum_sigma]
      have e1 : ∀ (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit)),
          ai ⟨b, c⟩ ^ 2 = ∑ s, w s * ‖primKraus I o b c (δ s)‖ ^ 2 := fun b c ↦
        Real.sq_sqrt (Finset.sum_nonneg fun s _ ↦ mul_nonneg (hw s) (sq_nonneg _))
      have e : ∑ b ∈ t, ∑ c, ai ⟨b, c⟩ ^ 2 =
          ∑ s, w s * ∑ b ∈ t, ∑ c, ‖primKraus I o b c (δ s)‖ ^ 2 := by
        simp only [e1]
        rw [Finset.sum_congr rfl fun b _ ↦ Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ ↦ by rw [Finset.mul_sum]
      rw [e]
      exact (Finset.sum_le_sum fun s _ ↦
        mul_le_mul_of_nonneg_left (prim_kraus_sum_le I o t (δ s)) (hw s)).trans hδ
    · rw [Finset.sum_sigma]
      exact (prim_kraus_sum_le I o t _).trans (pow_le_pow_left₀ (norm_nonneg _) hδbar 2)
  · -- oracle call
    intro A i E' ℓ k ih n hq ψ δ m a d hm ha hd hψ hδ hδbar
    cases i
    obtain ⟨hn, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff (L := L) (spec := qromSpec X Y) PUnit.unit E' ℓ k
      (fun _ ↦ n)).1 hq
    have hn' : 0 < n := hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hq' : QueryBounded (k ()) n := (hk ()).mono fun j ↦ by
      rw [Subsingleton.elim j ()]
      simp
    simp only [pv_queryBind]
    obtain ⟨c1, c2, c3⟩ := query_step w hw Hs G S hS r hr hε (stdOracle X Y (E' × Unit))
      (splitIso ℓ) (joinIso X Y E') ψ δ m a d hm ha hd hψ hδ hδbar
    have h := ih () n hq' (qvec ℓ G ψ) (fun s ↦ qvec ℓ (Hs s) (ψ + δ s) - qvec ℓ G ψ) m
      (a + 2 * r * m) (d + 2 * r ^ 2 * m + 2 * r * a) hm (by positivity) (by positivity)
      c1 c2 c3
    rw [Fq_query] at h
    simp only [add_sub_cancel] at h
    exact h

/-- **The tight hidden-set bound for arbitrary programs (second order).** -/
theorem qprob_tight_avg_sqrt (I : L.Interp) {A : QReg} (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (q : ℕ) (hx : QueryBounded x q) (E : (Σ u, W u) → Prop) :
    |∑ s, w s * (qprob I (Hs s) x ρ E).toReal - (∑ s, w s) * (qprob I G x ρ E).toReal| ≤
      8 * (q : ℝ) ^ 2 * r ^ 2 := by
  obtain ⟨vs, hvs, hq⟩ := qprob_toReal_eq_sum_pv (X := X) (Y := Y) I x ρ E
  have hj : ∀ j, |∑ s, w s * pv I (Hs s) x E (vs j) - (∑ s, w s) * pv I G x E (vs j)| ≤
      8 * (q : ℝ) ^ 2 * r ^ 2 * ‖vs j‖ ^ 2 := by
    intro j
    have h := pv_tight w hw Hs G S hS r hr hε I E x q hx (vs j) (fun _ ↦ 0) ‖vs j‖ 0 0
      (norm_nonneg _) le_rfl le_rfl le_rfl (by simp) (by simp)
    simp only [add_zero] at h
    refine h.trans (le_of_eq ?_)
    unfold Fq
    ring
  have e : ∑ s, w s * (qprob I (Hs s) x ρ E).toReal - (∑ s, w s) * (qprob I G x ρ E).toReal =
      ∑ j, (∑ s, w s * pv I (Hs s) x E (vs j) - (∑ s, w s) * pv I G x E (vs j)) := by
    simp only [hq]
    rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.mul_sum]
    simp only [Finset.mul_sum]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ ↦ hj j).trans ?_)
  rw [← Finset.mul_sum]
  calc 8 * (q : ℝ) ^ 2 * r ^ 2 * ∑ j, ‖vs j‖ ^ 2 ≤ 8 * (q : ℝ) ^ 2 * r ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hvs (by positivity)
    _ = _ := mul_one _

end Main

/-- **Tight hidden-set bound for every VCVio program.**  `x` is any `QuantumComp` over
`qromSpec X Y` with at most `q` oracle calls on every path (adaptive, any local signature and
interpretation, any workspace), `ρ` any initial substate, `E` any leaf event.  If the functions
`Hs s` differ from `G` only on marked sets `S s` that contain every point with total weight at
most `ε`, then the `w`-averaged probability of `E` against `Hs s` differs from the one against
`G` by at most `8 q² ε`. -/
theorem qprob_tight_avg (I : L.Interp) {A : QReg} (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (q : ℕ) (hx : QueryBounded x q) (E : (Σ u, W u) → Prop)
    {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (Hs : ι → X → Y) (G : X → Y)
    (S : ι → Finset X) (hS : ∀ s k, Hs s k ≠ G k → k ∈ S s) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ∀ k, ∑ s with k ∈ S s, w s ≤ ε) :
    |∑ s, w s * (qprob I (Hs s) x ρ E).toReal - (∑ s, w s) * (qprob I G x ρ E).toReal| ≤
      8 * (q : ℝ) ^ 2 * ε := by
  have h := qprob_tight_avg_sqrt w hw Hs G S hS (Real.sqrt ε) (Real.sqrt_nonneg ε)
    (by rw [Real.sq_sqrt hε0]; exact hε) I x ρ q hx E
  rwa [Real.sq_sqrt hε0] at h

end PQ.QROM.Purify

#print axioms PQ.QROM.Purify.pv_tight
#print axioms PQ.QROM.Purify.qprob_tight_avg
