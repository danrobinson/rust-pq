import PQ.QROM.ExactPrfTight

/-!
# The exact PRF game for a structured oracle

The keyed function `g : K × Dm → R` is uniform, but the quantum oracle the adversary queries is
a function `Hf g : X → Y` built from `g` (and from anything independent of `g`): e.g. `g` is one
of several hash components presented through one oracle port.  The only requirement is locality:
there is `loc : X → Option (K × Dm)` such that `Hf g x` depends on `g` only at the point `loc x`.

`prfStruct_real_le_ideal_add`: for a family of query programs `x f` indexed by the classical
PRF-oracle answers `f : Dm → R`, each making at most `q` oracle calls,

  `E_{k,g} Pr[x (g(k,·)) with oracle Hf g] ≤ E_{g,R'} Pr[x R' with oracle Hf g] + 8 q² / |K|`.

The proof is that of `prfExact_tight_abs_of_programReal` (`ExactPrf.lean`) with the marked set
`{x | loc x = some (k, _)}`: it uses `tight_view_of` through `prfExactTightProgramReal`.
-/

open MeasureTheory ENNReal Finset Quantum

universe u v w

namespace PQ.QROM

section Struct

variable {K Dm R X Y : Type} [Fintype K] [DecidableEq K] [Fintype Dm] [DecidableEq Dm]
  [Fintype R] [DecidableEq R] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The coupling of the real PRF world with the hybrid world, for an arbitrary functional. -/
theorem prfStruct_coupling [Nonempty K] [Nonempty Dm] [Nonempty R]
    (Φ : (K × Dm → R) → (Dm → R) → ℝ≥0∞) :
    (∑ ω : K × ((K × Dm → R) × (Dm → R)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹)) * Φ (prfSwapRow ω.1 ω.2.1 ω.2.2) ω.2.2 =
      ∑ k : K, ∑ g : K × Dm → R,
        ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹) *
          Φ g fun d ↦ g (k, d)) ∧
    (∑ ω : K × ((K × Dm → R) × (Dm → R)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹)) * Φ ω.2.1 ω.2.2 =
      ∑ g : K × Dm → R, ∑ R' : Dm → R,
        ((Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ * (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹) * Φ g R') ∧
    ∑ _ω : K × ((K × Dm → R) × (Dm → R)),
        ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹)) = 1 := by
  have iK := card_mul_inv_cancel K
  have iF := card_mul_inv_cancel (K × Dm → R)
  have iR := card_mul_inv_cancel (Dm → R)
  set cK : ℝ≥0∞ := (Fintype.card K : ℝ≥0∞)
  set cF : ℝ≥0∞ := (Fintype.card (K × Dm → R) : ℝ≥0∞)
  set cR : ℝ≥0∞ := (Fintype.card (Dm → R) : ℝ≥0∞)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hrow : ∀ v : (K × Dm → R) × (Dm → R),
        (fun d ↦ prfSwapRow k v.1 v.2 (k, d)) = v.2 := fun v ↦ by
      funext d
      simp [prfSwapRow]
    have h := sum_prfSwapRow (D := Dm) k fun F ↦ (cK⁻¹ * (cF⁻¹ * cR⁻¹)) *
      Φ F fun d ↦ F (k, d)
    simp only [hrow] at h
    refine h.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    calc cR * (cK⁻¹ * (cF⁻¹ * cR⁻¹) * Φ F fun d ↦ F (k, d))
        = (cR * cR⁻¹) * (cK⁻¹ * cF⁻¹ * Φ F fun d ↦ F (k, d)) := by ring
      _ = _ := by rw [iR, one_mul]
  · rw [Fintype.sum_prod_type]
    dsimp only
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R' _ ↦ ?_
    calc cK * (cK⁻¹ * (cF⁻¹ * cR⁻¹) * Φ F R')
        = (cK * cK⁻¹) * (cF⁻¹ * cR⁻¹ * Φ F R') := by ring
      _ = _ := by rw [iK, one_mul]
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    calc cK * (cF * cR * (cK⁻¹ * (cF⁻¹ * cR⁻¹)))
        = (cK * cK⁻¹) * (cF * cF⁻¹) * (cR * cR⁻¹) := by ring
      _ = 1 := by rw [iK, iF, iR]; simp

theorem sum_mul_le_one_of_le_one {Ω : Type} [Fintype Ω] (w p : Ω → ℝ≥0∞) (hw : ∑ ω, w ω = 1)
    (hp : ∀ ω, p ω ≤ 1) : ∑ ω, w ω * p ω ≤ 1 :=
  calc ∑ ω, w ω * p ω ≤ ∑ ω, w ω * 1 := Finset.sum_le_sum fun ω _ ↦ by gcongr; exact hp ω
    _ = 1 := by simp [hw]

/-- **Exact PRF game for a structured oracle, tight.** -/
theorem prfStruct_real_le_ideal_add [Nonempty K] [Nonempty Dm] [Nonempty R] [Nonempty X]
    (I : L.Interp)
    (ρ : SubState A) (q : ℕ) (Hf : (K × Dm → R) → X → Y) (loc : X → Option (K × Dm))
    (hloc : ∀ g g' x, (∀ p, loc x = some p → g p = g' p) → Hf g x = Hf g' x)
    (x : (Dm → R) → QuantumComp L (qromSpec X Y) W A) (hx : ∀ f, QueryBounded (x f) q)
    (E : (Σ u, W u) → Prop) :
    (∑ k : K, ∑ g : K × Dm → R,
        ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹) *
          qprob I (Hf g) (x fun d ↦ g (k, d)) ρ E) ≤
      (∑ g : K × Dm → R, ∑ R' : Dm → R,
        ((Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ * (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹) *
          qprob I (Hf g) (x R') ρ E) +
        ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card K) := by
  classical
  obtain ⟨e1, e2, hsum1⟩ := prfStruct_coupling (K := K) (Dm := Dm) (R := R)
    fun g f ↦ qprob I (Hf g) (x f) ρ E
  have hle : ∀ (H : X → Y) (f : Dm → R), qprob I H (x f) ρ E ≤ 1 := fun H f ↦
    (HybridModel.ofProgram I (x f) ρ q (hx f) E).prob_le_one H id
  have hfin : ∀ (H : X → Y) (f : Dm → R), qprob I H (x f) ρ E ≠ ⊤ := fun H f ↦
    ne_top_of_le_ne_top one_ne_top (hle H f)
  have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < Fintype.card (K × Dm → R) := by exact_mod_cast Fintype.card_pos
  have hR : (0 : ℝ) < Fintype.card (Dm → R) := by exact_mod_cast Fintype.card_pos
  set κ : ℝ := (Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × Dm → R) : ℝ)⁻¹ *
    (Fintype.card (Dm → R) : ℝ)⁻¹) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκt : ((Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹)).toReal = κ := by
    simp [hκ, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hκfin : (Fintype.card K : ℝ≥0∞)⁻¹ * ((Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹) ≠ ⊤ := by
    simp [ENNReal.mul_eq_top, Fintype.card_ne_zero]
  rw [← e1, ← e2]
  refine le_add_ofReal_of_abs_toReal
    (sum_mul_le_one_of_le_one _ _ hsum1 fun ω ↦ hle _ _)
    (sum_mul_le_one_of_le_one _ _ hsum1 fun ω ↦ hle _ _) ?_
  rw [ENNReal.toReal_sum fun ω _ ↦ mul_ne_top hκfin (hfin _ _),
    ENNReal.toReal_sum fun ω _ ↦ mul_ne_top hκfin (hfin _ _)]
  simp only [ENNReal.toReal_mul, hκt]
  let S : K → Finset X := fun k ↦ univ.filter fun z ↦ (loc z).map Prod.fst = some k
  have hS : ∀ (k : K) (z : X), z ∈ S k ↔ (loc z).map Prod.fst = some k := fun k z ↦ by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hH : ∀ (v : (K × Dm → R) × (Dm → R)) (z : X),
      ∑ ω : K × ((K × Dm → R) × (Dm → R)) with ω.2 = v ∧ z ∈ S ω.1, κ ≤
        (Fintype.card K : ℝ)⁻¹ * ∑ ω : K × ((K × Dm → R) × (Dm → R)) with ω.2 = v, κ := by
    intro v z
    rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    rcases hko : (loc z).map Prod.fst with _ | k0
    · have hm : ∀ k : K, z ∉ S k := fun k ↦ by rw [hS, hko]; exact fun h ↦ nomatch h
      simp only [hm, and_false, ite_false, Finset.sum_const_zero]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by
        split_ifs <;> [exact hκ0; exact le_rfl])
    · have hm : ∀ k : K, z ∈ S k ↔ k = k0 := fun k ↦ by
        rw [hS, hko]
        exact ⟨fun h ↦ (Option.some.inj h).symm, fun h ↦ by rw [h]⟩
      simp only [hm, ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]
  have hdiff : ∀ (ω : K × ((K × Dm → R) × (Dm → R))) (z : X),
      Hf (prfSwapRow ω.1 ω.2.1 ω.2.2) z ≠ Hf ω.2.1 z → z ∈ S ω.1 := by
    intro ω z hne
    by_contra hz
    refine hne (hloc _ _ z fun p hp ↦ ?_)
    have hk : ¬ p.1 = ω.1 := fun hpk ↦ hz (by rw [hS, hp, Option.map_some, hpk])
    simp [prfSwapRow, hk]
  have h := prfExactTightProgramReal X Y I W ρ q
    (K × ((K × Dm → R) × (Dm → R))) ((K × Dm → R) × (Dm → R)) (fun _ ↦ κ)
    (fun _ ↦ hκ0) (fun ω ↦ ω.2) (fun ω ↦ S ω.1) (Fintype.card K : ℝ)⁻¹
    (by positivity) hH (fun v ↦ x v.2) (fun v ↦ hx v.2)
    (fun ω ↦ Hf (prfSwapRow ω.1 ω.2.1 ω.2.2)) (fun v ↦ Hf v.1) hdiff (fun _ ↦ E)
  have hsum : ∑ _ω : K × ((K × Dm → R) × (Dm → R)), κ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul,
      hκ]
    field_simp
  rw [hsum, mul_one] at h
  rwa [div_eq_mul_inv]

end Struct

end PQ.QROM

#print axioms PQ.QROM.prfStruct_coupling
#print axioms PQ.QROM.prfStruct_real_le_ideal_add
