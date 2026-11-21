import Reduction.Gen.Defs

/-!
# Derandomisation of `ds`-sampling

A program over `(ds + us) + X` is valued in a *model* (a stateful sub-stochastic interpretation of
the `us + X` queries with a final payoff), the `ds`-queries being averaged with fixed weights `w`.
A functional of forger families is *linear* (`IsLin`) if it is a weighted sum of such values.

Main result (`IsLin.derand`): an inequality `N ≤ P` between two linear functionals of finite
total weight that holds for all `ds`-free families holds for all families.  The proof fixes the
answers of the `ds`-queries one at a time (`Model.exists_resolution`), each time choosing the
answer that is at least as good as the average for `N - P`.
-/

open OracleComp OracleSpec ENNReal

namespace Reduction.Gen

variable {κ ιu ιx : Type} (ds : OracleSpec κ) [∀ d, Fintype (ds.Range d)]
  {us : OracleSpec ιu} {X : OracleSpec ιx} {α PK : Type}

/-- A stateful sub-stochastic interpretation of the queries of `us + X`, with a final payoff. -/
structure Model (us : OracleSpec ιu) (X : OracleSpec ιx) (α : Type) where
  σ : Type
  step : (t : (us + X).Domain) → σ → (us + X).Range t × σ → ℝ≥0∞
  fin : α → σ → ℝ≥0∞
  step_le : ∀ t s, ∑' x, step t s x ≤ 1
  fin_le : ∀ a s, fin a s ≤ 1

/-- Value of a program over `(ds + us) + X` in a model, `ds`-queries being averaged with
weights `w`. -/
noncomputable def Model.val (w : (d : ds.Domain) → ds.Range d → ℝ≥0∞) (𝔐 : Model us X α) :
    OracleComp ((ds + us) + X) α → 𝔐.σ → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ ↦ 𝔐.σ → ℝ≥0∞)
    (fun a s ↦ 𝔐.fin a s)
    (fun t _ ih s ↦
      match t, ih with
      | .inl (.inl d), ih => ∑ u : ds.Range d, w d u * ih u s
      | .inl (.inr n), ih => ∑' x : us.Range n × 𝔐.σ, 𝔐.step (.inl n) s x * ih x.1 x.2
      | .inr q, ih => ∑' x : X.Range q × 𝔐.σ, 𝔐.step (.inr q) s x * ih x.1 x.2)

/-- `t` is obtained from `oa` by fixing an answer at every `ds`-query. -/
inductive IsResolution : OracleComp ((ds + us) + X) α → OracleComp (us + X) α → Prop
  | pure (a : α) : IsResolution (pure a) (pure a)
  | ds (d : ds.Domain) (k) (u : ds.Range d) (t) : IsResolution (k u) t →
      IsResolution (liftM (((ds + us) + X).query (.inl (.inl d))) >>= k) t
  | us (n : us.Domain) (k) (k') : (∀ u, IsResolution (k u) (k' u)) →
      IsResolution (liftM (((ds + us) + X).query (.inl (.inr n))) >>= k)
        (liftM ((us + X).query (.inl n)) >>= k')
  | X (q : X.Domain) (k) (k') : (∀ u, IsResolution (k u) (k' u)) →
      IsResolution (liftM (((ds + us) + X).query (.inr q)) >>= k)
        (liftM ((us + X).query (.inr q)) >>= k')

/-- A functional of forger families `F : PK → OracleComp ((ds+us)+X) α` that is a weighted sum
(total weight ≤ `b`) of model values at points of the family. -/
def IsLin (w : (d : ds.Domain) → ds.Range d → ℝ≥0∞) (b : ℝ≥0∞)
    (Φ : (PK → OracleComp ((ds + us) + X) α) → ℝ≥0∞) : Prop :=
  ∃ (𝔐 : Model us X α) (I : Type) (c : I → ℝ≥0∞) (pk : I → PK) (s : I → 𝔐.σ),
    ∑' i, c i ≤ b ∧ ∀ F, Φ F = ∑' i, c i * 𝔐.val ds w (F (pk i)) (s i)

variable {w : (d : ds.Domain) → ds.Range d → ℝ≥0∞}

/-! ## Defining equations of `val` -/

@[simp] lemma Model.val_pure (𝔐 : Model us X α) (a : α) (s : 𝔐.σ) :
    𝔐.val ds w (pure a) s = 𝔐.fin a s := rfl

lemma Model.val_ds_bind (𝔐 : Model us X α) (d : ds.Domain)
    (k : ds.Range d → OracleComp ((ds + us) + X) α) (s : 𝔐.σ) :
    𝔐.val ds w (liftM (((ds + us) + X).query (.inl (.inl d))) >>= k) s =
      ∑ u, w d u * 𝔐.val ds w (k u) s := rfl

lemma Model.val_us_bind (𝔐 : Model us X α) (n : us.Domain)
    (k : us.Range n → OracleComp ((ds + us) + X) α) (s : 𝔐.σ) :
    𝔐.val ds w (liftM (((ds + us) + X).query (.inl (.inr n))) >>= k) s =
      ∑' x : us.Range n × 𝔐.σ, 𝔐.step (.inl n) s x * 𝔐.val ds w (k x.1) x.2 := rfl

lemma Model.val_X_bind (𝔐 : Model us X α) (q : X.Domain)
    (k : X.Range q → OracleComp ((ds + us) + X) α) (s : 𝔐.σ) :
    𝔐.val ds w (liftM (((ds + us) + X).query (.inr q)) >>= k) s =
      ∑' x : X.Range q × 𝔐.σ, 𝔐.step (.inr q) s x * 𝔐.val ds w (k x.1) x.2 := rfl

omit [∀ d, Fintype (ds.Range d)] in
/-- Induction on programs over `(ds + us) + X`, by the kind of the first query. -/
theorem ind3 {C : OracleComp ((ds + us) + X) α → Prop}
    (pure : ∀ a, C (pure a))
    (hds : ∀ (d : ds.Domain) (k : ds.Range d → OracleComp ((ds + us) + X) α),
      (∀ u, C (k u)) → C (liftM (((ds + us) + X).query (.inl (.inl d))) >>= k))
    (hus : ∀ (n : us.Domain) (k : us.Range n → OracleComp ((ds + us) + X) α),
      (∀ u, C (k u)) → C (liftM (((ds + us) + X).query (.inl (.inr n))) >>= k))
    (hX : ∀ (q : X.Domain) (k : X.Range q → OracleComp ((ds + us) + X) α),
      (∀ u, C (k u)) → C (liftM (((ds + us) + X).query (.inr q)) >>= k))
    (oa : OracleComp ((ds + us) + X) α) : C oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact pure a
  | query_bind t k ih =>
    match t, k, ih with
    | .inl (.inl d), k, ih => exact hds d k ih
    | .inl (.inr n), k, ih => exact hus n k ih
    | .inr q, k, ih => exact hX q k ih

theorem Model.val_le_one (hw : ∀ d, ∑ u, w d u = 1) (𝔐 : Model us X α)
    (oa : OracleComp ((ds + us) + X) α) (s : 𝔐.σ) : 𝔐.val ds w oa s ≤ 1 := by
  induction oa using ind3 (ds := ds) generalizing s with
  | pure a => exact 𝔐.fin_le a s
  | hds d k ih =>
    rw [Model.val_ds_bind, ← hw d]
    exact Finset.sum_le_sum fun u _ ↦ by simpa using mul_le_mul' (le_refl (w d u)) (ih u s)
  | hus n k ih =>
    rw [Model.val_us_bind]
    refine le_trans (_root_.tsum_le_tsum fun x ↦ ?_) (𝔐.step_le (.inl n) s)
    simpa using mul_le_mul' (le_refl (𝔐.step (.inl n) s x)) (ih x.1 x.2)
  | hX q k ih =>
    rw [Model.val_X_bind]
    refine le_trans (_root_.tsum_le_tsum fun x ↦ ?_) (𝔐.step_le (.inr q) s)
    simpa using mul_le_mul' (le_refl (𝔐.step (.inr q) s x)) (ih x.1 x.2)

/-! ## The disjoint union of a family of models -/

private lemma tsum_sigma_aux {Y R : Type} {σ : Y → Type} (y : Y)
    (f : R × (Σ y, σ y) → ℝ≥0∞) (g : R × σ y → ℝ≥0∞)
    (h1 : ∀ u s, f (u, ⟨y, s⟩) = g (u, s))
    (h0 : ∀ u y' s, y' ≠ y → f (u, ⟨y', s⟩) = 0) : ∑' x, f x = ∑' x, g x := by
  rw [_root_.tsum_prod', _root_.tsum_prod']
  congr 1; funext u
  rw [_root_.tsum_sigma', tsum_eq_single y]
  · simp [h1]
  · intro y' hy
    simp [h0 _ _ _ hy]

open Classical in
/-- The disjoint union of a family of models: the state remembers its component. -/
noncomputable def Model.sigma {Y : Type} (𝔐 : Y → Model us X α) : Model us X α where
  σ := Σ y, (𝔐 y).σ
  step t s x := if h : x.2.1 = s.1 then (𝔐 s.1).step t s.2 (x.1, h ▸ x.2.2) else 0
  fin a s := (𝔐 s.1).fin a s.2
  step_le t s := by
    rw [tsum_sigma_aux s.1 _ ((𝔐 s.1).step t s.2) (fun u s' ↦ by simp)
      (fun u y' s' hy ↦ by simp [hy])]
    exact (𝔐 s.1).step_le t s.2
  fin_le a s := (𝔐 s.1).fin_le a s.2

theorem Model.val_sigma {Y : Type} (𝔐 : Y → Model us X α)
    (oa : OracleComp ((ds + us) + X) α) (y : Y) (s : (𝔐 y).σ) :
    (Model.sigma 𝔐).val ds w oa ⟨y, s⟩ = (𝔐 y).val ds w oa s := by
  induction oa using ind3 (ds := ds) generalizing s with
  | pure a => rfl
  | hds d k ih =>
    refine (Model.val_ds_bind ds _ d k _).trans (Eq.trans ?_ (Model.val_ds_bind ds _ d k _).symm)
    exact Finset.sum_congr rfl fun u _ ↦ by rw [ih]
  | hus n k ih =>
    refine (Model.val_us_bind ds _ n k _).trans (Eq.trans ?_ (Model.val_us_bind ds _ n k _).symm)
    refine tsum_sigma_aux y _ _ (fun u s' ↦ ?_) (fun u y' s' hy ↦ ?_)
    · rw [ih]; simp [Model.sigma]
    · simp [Model.sigma, hy]
  | hX q k ih =>
    refine (Model.val_X_bind ds _ q k _).trans (Eq.trans ?_ (Model.val_X_bind ds _ q k _).symm)
    refine tsum_sigma_aux y _ _ (fun u s' ↦ ?_) (fun u y' s' hy ↦ ?_)
    · rw [ih]; simp [Model.sigma]
    · simp [Model.sigma, hy]

/-! ## Closure properties of `IsLin` -/

variable {b b' b₁ b₂ : ℝ≥0∞} {Φ Φ₁ Φ₂ : (PK → OracleComp ((ds + us) + X) α) → ℝ≥0∞}

theorem IsLin.mono (h : IsLin ds w b Φ) (hb : b ≤ b') : IsLin ds w b' Φ := by
  obtain ⟨𝔐, I, c, pk, s, hc, hΦ⟩ := h
  exact ⟨𝔐, I, c, pk, s, hc.trans hb, hΦ⟩

theorem IsLin.zero :
    IsLin ds w 0 (fun _ : PK → OracleComp ((ds + us) + X) α ↦ 0) :=
  ⟨⟨PUnit, fun _ _ _ ↦ 0, fun _ _ ↦ 0, by simp, by simp⟩, Empty, Empty.elim, Empty.elim,
    Empty.elim, by simp, fun F ↦ by simp⟩

theorem IsLin.add (h₁ : IsLin ds w b₁ Φ₁) (h₂ : IsLin ds w b₂ Φ₂) :
    IsLin ds w (b₁ + b₂) (fun F ↦ Φ₁ F + Φ₂ F) := by
  obtain ⟨𝔐₁, I₁, c₁, pk₁, s₁, hc₁, hΦ₁⟩ := h₁
  obtain ⟨𝔐₂, I₂, c₂, pk₂, s₂, hc₂, hΦ₂⟩ := h₂
  let 𝔐 : Bool → Model us X α := fun y ↦ bif y then 𝔐₁ else 𝔐₂
  refine ⟨Model.sigma 𝔐, I₁ ⊕ I₂, Sum.elim c₁ c₂, Sum.elim pk₁ pk₂,
    Sum.elim (fun i ↦ ⟨true, s₁ i⟩) (fun i ↦ ⟨false, s₂ i⟩), ?_, fun F ↦ ?_⟩
  · rw [Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable]
    exact add_le_add hc₁ hc₂
  · show Φ₁ F + Φ₂ F = _
    rw [Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable, hΦ₁, hΦ₂]
    simp only [Sum.elim_inl, Sum.elim_inr]
    refine congrArg₂ (· + ·) (tsum_congr fun i ↦ ?_) (tsum_congr fun i ↦ ?_)
    · exact congrArg (c₁ i * ·) (Model.val_sigma (w := w) ds 𝔐 (F (pk₁ i)) true (s₁ i)).symm
    · exact congrArg (c₂ i * ·) (Model.val_sigma (w := w) ds 𝔐 (F (pk₂ i)) false (s₂ i)).symm

theorem IsLin.const_mul (c : ℝ≥0∞) (h : IsLin ds w b Φ) :
    IsLin ds w (c * b) (fun F ↦ c * Φ F) := by
  obtain ⟨𝔐, I, c', pk, s, hc, hΦ⟩ := h
  refine ⟨𝔐, I, fun i ↦ c * c' i, pk, s, ?_, fun F ↦ ?_⟩
  · rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' (le_refl _) hc
  · show c * Φ F = _
    rw [hΦ, ← ENNReal.tsum_mul_left]
    simp only [mul_assoc]

theorem IsLin.tsum {Y : Type} (c : Y → ℝ≥0∞)
    (Φ : Y → (PK → OracleComp ((ds + us) + X) α) → ℝ≥0∞) (h : ∀ y, IsLin ds w b (Φ y)) :
    IsLin ds w ((∑' y, c y) * b) (fun F ↦ ∑' y, c y * Φ y F) := by
  unfold IsLin at h
  choose 𝔐 I c' pk s hc hΦ using h
  refine ⟨Model.sigma 𝔐, Σ y, I y, fun i ↦ c i.1 * c' i.1 i.2, fun i ↦ pk i.1 i.2,
    fun i ↦ ⟨i.1, s i.1 i.2⟩, ?_, fun F ↦ ?_⟩
  · rw [_root_.tsum_sigma', ← ENNReal.tsum_mul_right]
    refine _root_.tsum_le_tsum fun y ↦ ?_
    show ∑' j : I y, c y * c' y j ≤ c y * b
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' (le_refl _) (hc y)
  · show ∑' y, c y * Φ y F = _
    rw [_root_.tsum_sigma']
    refine tsum_congr fun y ↦ ?_
    rw [hΦ, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun i ↦ ?_
    show c y * (c' y i * _) =
      c y * c' y i * (Model.sigma 𝔐).val ds w (F (pk y i)) ⟨y, s y i⟩
    rw [mul_assoc]
    exact congrArg (fun z ↦ c y * (c' y i * z))
      (Model.val_sigma (w := w) ds 𝔐 (F (pk y i)) y (s y i)).symm

theorem IsLin.le_bound (hw : ∀ d, ∑ u, w d u = 1) (h : IsLin ds w b Φ)
    (F : PK → OracleComp ((ds + us) + X) α) : Φ F ≤ b := by
  obtain ⟨𝔐, I, c, pk, s, hc, hΦ⟩ := h
  rw [hΦ]
  refine le_trans (_root_.tsum_le_tsum fun i ↦ ?_) hc
  simpa using mul_le_mul' (le_refl (c i)) (𝔐.val_le_one ds hw (F (pk i)) (s i))

private lemma tsum_reindex {I A : Type} [DecidableEq A] (c : I → ℝ≥0∞) (p : I → A)
    (g : A → ℝ≥0∞) :
    ∑' a, (∑' i, if p i = a then c i else 0) * g a = ∑' i, c i * g (p i) := by
  simp_rw [← ENNReal.tsum_mul_right]
  rw [_root_.tsum_comm]
  congr 1; funext i
  rw [tsum_eq_single (p i)]
  · simp
  · intro a ha
    simp [Ne.symm ha]

/-- Normal form of a linear functional: a mass distribution on states for every key. -/
theorem IsLin.exists_mass (h : IsLin ds w b Φ) :
    ∃ (𝔐 : Model us X α) (m : PK → 𝔐.σ → ℝ≥0∞), ∑' x, ∑' s, m x s ≤ b ∧
      ∀ F, Φ F = ∑' x, ∑' s, m x s * 𝔐.val ds w (F x) s := by
  classical
  obtain ⟨𝔐, I, c, pk, s, hc, hΦ⟩ := h
  refine ⟨𝔐, fun x s₀ ↦ ∑' i, if (pk i, s i) = (x, s₀) then c i else 0, ?_, fun F ↦ ?_⟩
  · have := tsum_reindex c (fun i ↦ (pk i, s i)) (fun _ ↦ 1)
    simp only [mul_one] at this
    rw [_root_.tsum_prod'] at this
    rw [this]
    exact hc
  · have := tsum_reindex c (fun i ↦ (pk i, s i)) (fun a ↦ 𝔐.val ds w (F a.1) a.2)
    rw [_root_.tsum_prod'] at this
    rw [hΦ]
    exact this.symm

/-! ## The core: fixing the `ds`-answers -/

/-- Selection: some index is at least as good as the average. -/
theorem exists_sel {ι : Type} [Fintype ι] (p a b : ι → ℝ≥0∞) (hp : ∑ j, p j = 1)
    (ha : ∀ i, a i ≠ ⊤) (hb : ∀ i, b i ≠ ⊤) :
    ∃ i, (∑ j, p j * a j) + b i ≤ (∑ j, p j * b j) + a i := by
  by_contra hcon
  push Not at hcon
  have hp1 : ∀ j, p j ≠ ⊤ := fun j ↦ ne_top_of_le_ne_top one_ne_top
    (hp ▸ Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ j))
  have hA : ∑ j, p j * a j ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun j _ ↦ ENNReal.mul_ne_top (hp1 j) (ha j)
  have hB : ∑ j, p j * b j ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun j _ ↦ ENNReal.mul_ne_top (hp1 j) (hb j)
  have hr : ∀ i, (∑ j, (p j).toReal * (b j).toReal) + (a i).toReal <
      (∑ j, (p j).toReal * (a j).toReal) + (b i).toReal := by
    intro i
    have := (ENNReal.toReal_lt_toReal (ENNReal.add_ne_top.2 ⟨hB, ha i⟩)
      (ENNReal.add_ne_top.2 ⟨hA, hb i⟩)).2 (hcon i)
    rw [ENNReal.toReal_add hB (ha i), ENNReal.toReal_add hA (hb i),
      ENNReal.toReal_sum fun j _ ↦ ENNReal.mul_ne_top (hp1 j) (hb j),
      ENNReal.toReal_sum fun j _ ↦ ENNReal.mul_ne_top (hp1 j) (ha j)] at this
    simpa only [ENNReal.toReal_mul] using this
  have hpr : ∑ j, (p j).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun j _ ↦ hp1 j, hp]; simp
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hp
  set A := ∑ j, (p j).toReal * (a j).toReal
  set B := ∑ j, (p j).toReal * (b j).toReal
  have : ∑ i, (p i).toReal * (B + (a i).toReal) < ∑ i, (p i).toReal * (A + (b i).toReal) :=
    Finset.sum_lt_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hr i).le ENNReal.toReal_nonneg)
      ⟨i, Finset.mem_univ _,
        mul_lt_mul_of_pos_left (hr i) (ENNReal.toReal_pos hi (hp1 i))⟩
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hpr, one_mul] at this
  linarith

theorem Model.avg_le (hw : ∀ d, ∑ u, w d u = 1) (𝔐 : Model us X α) (μ : 𝔐.σ → ℝ≥0∞)
    (oa : OracleComp ((ds + us) + X) α) : ∑' s, μ s * 𝔐.val ds w oa s ≤ ∑' s, μ s :=
  _root_.tsum_le_tsum fun s ↦ by simpa using mul_le_mul' (le_refl (μ s)) (𝔐.val_le_one ds hw oa s)

theorem Model.avg_ds (𝔐 : Model us X α) (μ : 𝔐.σ → ℝ≥0∞) (d : ds.Domain)
    (k : ds.Range d → OracleComp ((ds + us) + X) α) :
    ∑' s, μ s * 𝔐.val ds w (liftM (((ds + us) + X).query (.inl (.inl d))) >>= k) s =
      ∑ u, w d u * ∑' s, μ s * 𝔐.val ds w (k u) s := by
  simp_rw [Model.val_ds_bind, Finset.mul_sum, ← ENNReal.tsum_mul_left]
  rw [Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  congr 1; funext s
  exact mul_left_comm _ _ _

omit [∀ d, Fintype (ds.Range d)] in
theorem Model.avg_step (𝔐 : Model us X α) (μ : 𝔐.σ → ℝ≥0∞) (t : (us + X).Domain)
    (f : (us + X).Range t → 𝔐.σ → ℝ≥0∞) :
    ∑' s, μ s * ∑' x : (us + X).Range t × 𝔐.σ, 𝔐.step t s x * f x.1 x.2 =
      ∑' u, ∑' s', (∑' s, μ s * 𝔐.step t s (u, s')) * f u s' := by
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, _root_.tsum_prod']
  rw [_root_.tsum_comm]
  congr 1; funext u
  rw [_root_.tsum_comm]
  simp_rw [mul_assoc]

omit [∀ d, Fintype (ds.Range d)] in
theorem Model.push_le (𝔐 : Model us X α) (μ : 𝔐.σ → ℝ≥0∞) (t : (us + X).Domain)
    (u : (us + X).Range t) : ∑' s', ∑' s, μ s * 𝔐.step t s (u, s') ≤ ∑' s, μ s := by
  calc ∑' s', ∑' s, μ s * 𝔐.step t s (u, s')
      ≤ ∑' u, ∑' s', ∑' s, μ s * 𝔐.step t s (u, s') :=
        _root_.le_tsum (f := fun u ↦ ∑' s', ∑' s, μ s * 𝔐.step t s (u, s')) u
    _ = ∑' s, μ s * ∑' x, 𝔐.step t s x := by
        have := 𝔐.avg_step μ t (fun _ _ ↦ 1)
        simpa using this.symm
    _ ≤ ∑' s, μ s :=
        _root_.tsum_le_tsum fun s ↦ by simpa using mul_le_mul' (le_refl (μ s)) (𝔐.step_le t s)

private lemma core_step (𝔐 𝔑 : Model us X α) (t : (us + X).Domain)
    (A B : (us + X).Range t → OracleComp ((ds + us) + X) α)
    (oa ob : OracleComp ((ds + us) + X) α)
    (hA : ∀ (𝔏 : Model us X α) (s : 𝔏.σ), 𝔏.val ds w oa s =
      ∑' x : (us + X).Range t × 𝔏.σ, 𝔏.step t s x * 𝔏.val ds w (A x.1) x.2)
    (hB : ∀ (𝔏 : Model us X α) (s : 𝔏.σ), 𝔏.val ds w ob s =
      ∑' x : (us + X).Range t × 𝔏.σ, 𝔏.step t s x * 𝔏.val ds w (B x.1) x.2)
    (μ : 𝔐.σ → ℝ≥0∞) (ν : 𝔑.σ → ℝ≥0∞)
    (IH : ∀ u,
      (∑' s', (∑' s, ν s * 𝔑.step t s (u, s')) * 𝔑.val ds w (A u) s') +
        (∑' s', (∑' s, μ s * 𝔐.step t s (u, s')) * 𝔐.val ds w (B u) s') ≤
      (∑' s', (∑' s, μ s * 𝔐.step t s (u, s')) * 𝔐.val ds w (A u) s') +
        (∑' s', (∑' s, ν s * 𝔑.step t s (u, s')) * 𝔑.val ds w (B u) s')) :
    (∑' s, ν s * 𝔑.val ds w oa s) + (∑' s, μ s * 𝔐.val ds w ob s) ≤
      (∑' s, μ s * 𝔐.val ds w oa s) + (∑' s, ν s * 𝔑.val ds w ob s) := by
  simp only [hA, hB]
  rw [𝔑.avg_step ν t (fun u s' ↦ 𝔑.val ds w (A u) s'),
    𝔐.avg_step μ t (fun u s' ↦ 𝔐.val ds w (B u) s'),
    𝔐.avg_step μ t (fun u s' ↦ 𝔐.val ds w (A u) s'),
    𝔑.avg_step ν t (fun u s' ↦ 𝔑.val ds w (B u) s'),
    ← _root_.tsum_add, ← _root_.tsum_add]
  exact _root_.tsum_le_tsum IH

theorem Model.exists_resolution (hw : ∀ d, ∑ u, w d u = 1) (𝔐 𝔑 : Model us X α)
    (oa : OracleComp ((ds + us) + X) α) (μ : 𝔐.σ → ℝ≥0∞) (ν : 𝔑.σ → ℝ≥0∞)
    (hμ : ∑' s, μ s ≠ ⊤) (hν : ∑' s, ν s ≠ ⊤) :
    ∃ t : OracleComp (us + X) α, IsResolution ds oa t ∧
      (∑' s, ν s * 𝔑.val ds w oa s) + (∑' s, μ s * 𝔐.val ds w (embed ds t) s) ≤
      (∑' s, μ s * 𝔐.val ds w oa s) + (∑' s, ν s * 𝔑.val ds w (embed ds t) s) := by
  induction oa using ind3 (ds := ds) generalizing μ ν with
  | pure a =>
    refine ⟨pure a, .pure a, ?_⟩
    rw [embed_pure]
    exact (add_comm _ _).le
  | hds d k ih =>
    have hP : ∀ ob, ∑' s, μ s * 𝔐.val ds w ob s ≠ ⊤ := fun ob ↦
      ne_top_of_le_ne_top hμ (𝔐.avg_le ds hw μ ob)
    have hN : ∀ ob, ∑' s, ν s * 𝔑.val ds w ob s ≠ ⊤ := fun ob ↦
      ne_top_of_le_ne_top hν (𝔑.avg_le ds hw ν ob)
    obtain ⟨u, hu⟩ := exists_sel (w d) (fun u ↦ ∑' s, ν s * 𝔑.val ds w (k u) s)
      (fun u ↦ ∑' s, μ s * 𝔐.val ds w (k u) s) (hw d) (fun u ↦ hN _) (fun u ↦ hP _)
    obtain ⟨t, ht, hineq⟩ := ih u μ ν hμ hν
    refine ⟨t, .ds d k u t ht, ?_⟩
    rw [Model.avg_ds, Model.avg_ds]
    have h := add_le_add hu hineq
    refine (ENNReal.add_le_add_iff_right
      (ENNReal.add_ne_top.2 ⟨hP (k u), hN (k u)⟩)).1 ?_
    calc _ = _ := by ring
      _ ≤ _ := h
      _ = _ := by ring
  | hus n k ih =>
    choose t ht hineq using fun u ↦ ih u
      (fun s' ↦ ∑' s, μ s * 𝔐.step (.inl n) s (u, s'))
      (fun s' ↦ ∑' s, ν s * 𝔑.step (.inl n) s (u, s'))
      (ne_top_of_le_ne_top hμ (𝔐.push_le μ (.inl n) u))
      (ne_top_of_le_ne_top hν (𝔑.push_le ν (.inl n) u))
    refine ⟨liftM ((us + X).query (.inl n)) >>= t, .us n k t ht, ?_⟩
    exact core_step ds 𝔐 𝔑 (.inl n) k (fun u ↦ embed ds (t u)) _ _
      (fun 𝔏 s ↦ 𝔏.val_us_bind ds n k s)
      (fun 𝔏 s ↦ by rw [embed_bind, embed_query_inl]; exact 𝔏.val_us_bind ds n _ s)
      μ ν hineq
  | hX q k ih =>
    choose t ht hineq using fun u ↦ ih u
      (fun s' ↦ ∑' s, μ s * 𝔐.step (.inr q) s (u, s'))
      (fun s' ↦ ∑' s, ν s * 𝔑.step (.inr q) s (u, s'))
      (ne_top_of_le_ne_top hμ (𝔐.push_le μ (.inr q) u))
      (ne_top_of_le_ne_top hν (𝔑.push_le ν (.inr q) u))
    refine ⟨liftM ((us + X).query (.inr q)) >>= t, .X q k t ht, ?_⟩
    exact core_step ds 𝔐 𝔑 (.inr q) k (fun u ↦ embed ds (t u)) _ _
      (fun 𝔏 s ↦ 𝔏.val_X_bind ds q k s)
      (fun 𝔏 s ↦ by rw [embed_bind, embed_query_inr]; exact 𝔏.val_X_bind ds q _ s)
      μ ν hineq

/-! ## Families -/

theorem IsLin.exists_resolution (hw : ∀ d, ∑ u, w d u = 1)
    {N P : (PK → OracleComp ((ds + us) + X) α) → ℝ≥0∞} {bN bP : ℝ≥0∞}
    (hbN : bN ≠ ⊤) (hbP : bP ≠ ⊤)
    (hN : IsLin ds w bN N) (hP : IsLin ds w bP P) (F : PK → OracleComp ((ds + us) + X) α) :
    ∃ F₀ : PK → OracleComp (us + X) α, (∀ pk, IsResolution ds (F pk) (F₀ pk)) ∧
      N F + P (fun pk ↦ embed ds (F₀ pk)) ≤ P F + N (fun pk ↦ embed ds (F₀ pk)) := by
  obtain ⟨𝔑, n, hn, hNF⟩ := IsLin.exists_mass ds hN
  obtain ⟨𝔐, m, hm, hPF⟩ := IsLin.exists_mass ds hP
  have hfm : ∀ x, ∑' s, m x s ≠ ⊤ := fun x ↦ ne_top_of_le_ne_top hbP
    ((_root_.le_tsum (f := fun x ↦ ∑' s, m x s) x).trans hm)
  have hfn : ∀ x, ∑' s, n x s ≠ ⊤ := fun x ↦ ne_top_of_le_ne_top hbN
    ((_root_.le_tsum (f := fun x ↦ ∑' s, n x s) x).trans hn)
  choose F₀ hres hineq using fun x ↦
    Model.exists_resolution ds hw 𝔐 𝔑 (F x) (m x) (n x) (hfm x) (hfn x)
  refine ⟨F₀, hres, ?_⟩
  rw [hNF, hNF, hPF, hPF, ← _root_.tsum_add, ← _root_.tsum_add]
  exact _root_.tsum_le_tsum hineq

/-- **Derandomisation.** A linear inequality between two such functionals that holds for all
`ds`-free families holds for all families. -/
theorem IsLin.derand (hw : ∀ d, ∑ u, w d u = 1)
    {N P : (PK → OracleComp ((ds + us) + X) α) → ℝ≥0∞} {bN bP : ℝ≥0∞}
    (hbN : bN ≠ ⊤) (hbP : bP ≠ ⊤)
    (hN : IsLin ds w bN N) (hP : IsLin ds w bP P)
    (h : ∀ F₀ : PK → OracleComp (us + X) α,
      N (fun pk ↦ embed ds (F₀ pk)) ≤ P (fun pk ↦ embed ds (F₀ pk))) :
    ∀ F, N F ≤ P F := by
  intro F
  obtain ⟨F₀, -, h1⟩ := IsLin.exists_resolution ds hw hbN hbP hN hP F
  have hfin : P (fun pk ↦ embed ds (F₀ pk)) ≠ ⊤ :=
    ne_top_of_le_ne_top hbP (IsLin.le_bound ds hw hP _)
  exact (ENNReal.add_le_add_iff_right hfin).1 (h1.trans (add_le_add le_rfl (h F₀)))

theorem IsLin.le_resolution (hw : ∀ d, ∑ u, w d u = 1)
    {N : (PK → OracleComp ((ds + us) + X) α) → ℝ≥0∞} {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hN : IsLin ds w b N) (F : PK → OracleComp ((ds + us) + X) α) :
    ∃ F₀ : PK → OracleComp (us + X) α, (∀ pk, IsResolution ds (F pk) (F₀ pk)) ∧
      N F ≤ N (fun pk ↦ embed ds (F₀ pk)) := by
  obtain ⟨F₀, hres, h⟩ :=
    IsLin.exists_resolution ds hw hb ENNReal.zero_ne_top hN (IsLin.zero ds) F
  exact ⟨F₀, hres, by simpa using h⟩

end Reduction.Gen

#print axioms Reduction.Gen.Model.val_le_one
#print axioms Reduction.Gen.IsLin.mono
#print axioms Reduction.Gen.IsLin.zero
#print axioms Reduction.Gen.IsLin.add
#print axioms Reduction.Gen.IsLin.const_mul
#print axioms Reduction.Gen.IsLin.tsum
#print axioms Reduction.Gen.Model.exists_resolution
#print axioms Reduction.Gen.IsLin.exists_resolution
#print axioms Reduction.Gen.IsLin.derand
#print axioms Reduction.Gen.IsLin.le_resolution
