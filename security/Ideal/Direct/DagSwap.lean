import Ideal.Direct.Engine

/-!
# Re-randomisation of an honest DAG of table cells, with collisions

The generalisation of the toy re-randomisation (`ToySwap.lean`: `Psi`, `reRand_bijective`,
`realWin_eq_Psi`) from the toy's single-block chains to an arbitrary **honest structure**: a
finite index set `I` of honest computations, each reading one table cell whose position depends
on the values of honest computations of lower rank (multi-block `T_len`/`T_k` chains: an
intermediate cell's chaining value is the full value of the previous cell) and on the table at a
set `P` of public cells (the midstate `cv = g (IV, sb PK.seed)`).

* `DagS C V I`: `rank`, `pos g s i` (the cell of honest computation `i`, given the table `g` and
  the honest values `s`), `P`, and the two dependence conditions.
* `hv D g`: the honest values of a table (by recursion on the rank); `hv_eq`:
  `hv D g i = g (pos g (hv D g) i)`.
* `Psi D g0 s`: `g0` with every honest cell overwritten by its honest value from `s`.
* `Good D g0 s`: the honest cells of `(g0, s)` are pairwise distinct and outside `P`;
  `GoodT D g`: the same for the honest cells of a table.  Unlike the toy, the honest cells need
  not be distinct for every `s` (two intermediate cells of different chains coincide when their
  chaining values do), so the map `(g0, s) ↦ (Psi g0 s, g0 ∘ pos)` is a bijection only between the
  good sets (`reRand_bij`).
* **`ex_le_Psi`**: for every `f ≤ 1` on tables,
  `E_g[f g] ≤ E_{g0, s}[f (Psi g0 s)] + Pr_{g0, s}[¬ Good g0 s]`,
  and `hv_Psi`: on the good set, the honest values of `Psi g0 s` are `s`.

Nothing here is specific to SLH-DSA.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.Direct.Dag

set_option linter.unusedSectionVars false

/-- An honest structure on a table `C → V`. -/
structure DagS (C V I : Type) where
  /-- the rank (an honest computation reads only values of lower rank) -/
  rank : I → ℕ
  /-- the cell read by honest computation `i` -/
  pos : (C → V) → (I → V) → I → C
  /-- the public cells the positions may read -/
  P : Set C
  /-- positions depend on honest values of lower rank only -/
  dep : ∀ g s s' i, (∀ j, rank j < rank i → s j = s' j) → pos g s i = pos g s' i
  /-- positions read the table only at public cells -/
  depG : ∀ g g' s i, (∀ q ∈ P, g q = g' q) → pos g s i = pos g' s i

variable {C V I : Type} (D : DagS C V I)

/-! ## Honest values of a table -/

section HV

variable [Inhabited V]

/-- Iterated honest values. -/
def hvN (g : C → V) : ℕ → I → V
  | 0 => fun _ => default
  | n + 1 => fun i => g (D.pos g (hvN g n) i)

theorem hvN_stable (g : C → V) : ∀ r, ∀ i, D.rank i < r → ∀ n m, r ≤ n → r ≤ m →
    hvN D g n i = hvN D g m i := by
  intro r
  induction r with
  | zero => intro i hi; omega
  | succ r ih =>
    intro i hi n m hn hm
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    show g (D.pos g (hvN D g n') i) = g (D.pos g (hvN D g m') i)
    rw [D.dep g (hvN D g n') (hvN D g m') i fun j hj => ih j (by omega) n' m' (by omega) (by omega)]

/-- The honest values of a table. -/
def hv (g : C → V) (i : I) : V := hvN D g (D.rank i + 1) i

theorem hv_eq_hvN (g : C → V) (i : I) (n : ℕ) (hn : D.rank i + 1 ≤ n) :
    hv D g i = hvN D g n i :=
  hvN_stable D g (D.rank i + 1) i (by omega) _ _ le_rfl hn

/-- **The honest value of `i` is the table at its cell.** -/
theorem hv_eq (g : C → V) (i : I) : hv D g i = g (D.pos g (hv D g) i) := by
  show g (D.pos g (hvN D g (D.rank i)) i) = _
  rw [D.dep g (hvN D g (D.rank i)) (hv D g) i fun j hj =>
    (hv_eq_hvN D g j (D.rank i) (by omega)).symm]

/-- Honest values are determined by the recursion. -/
theorem hv_unique (g : C → V) (s : I → V) (hs : ∀ i, s i = g (D.pos g s i)) : hv D g = s := by
  have key : ∀ r, ∀ i, D.rank i < r → hv D g i = s i := by
    intro r
    induction r with
    | zero => intro i hi; omega
    | succ r ih =>
      intro i hi
      rw [hv_eq, hs i, D.dep g (hv D g) s i fun j hj => ih j (by omega)]
  funext i
  exact key _ i (Nat.lt_succ_self _)

end HV

/-! ## The re-randomised table -/

section Psi

variable [DecidableEq C]

open Classical in
/-- `g0` with each honest cell overwritten by its honest value from `s`. -/
noncomputable def Psi (g0 : C → V) (s : I → V) (q : C) : V :=
  if h : ∃ i, D.pos g0 s i = q then s (Classical.choose h) else g0 q

/-- The good set: distinct honest cells, all outside `P`. -/
def Good (g0 : C → V) (s : I → V) : Prop :=
  Function.Injective (D.pos g0 s) ∧ ∀ i, D.pos g0 s i ∉ D.P

theorem Psi_pos (g0 : C → V) (s : I → V) (h : Good D g0 s) (i : I) :
    Psi D g0 s (D.pos g0 s i) = s i := by
  have hex : ∃ j, D.pos g0 s j = D.pos g0 s i := ⟨i, rfl⟩
  unfold Psi
  rw [dif_pos hex, h.1 (Classical.choose_spec hex)]

theorem Psi_of_not (g0 : C → V) (s : I → V) (q : C) (hq : ∀ i, D.pos g0 s i ≠ q) :
    Psi D g0 s q = g0 q := by
  unfold Psi
  rw [dif_neg (fun ⟨i, hi⟩ => hq i hi)]

theorem Psi_P (g0 : C → V) (s : I → V) (h : Good D g0 s) (q : C) (hq : q ∈ D.P) :
    Psi D g0 s q = g0 q :=
  Psi_of_not D g0 s q fun i hi => h.2 i (hi ▸ hq)

theorem pos_Psi (g0 : C → V) (s : I → V) (h : Good D g0 s) (i : I) :
    D.pos (Psi D g0 s) s i = D.pos g0 s i :=
  D.depG _ _ s i fun q hq => Psi_P D g0 s h q hq

variable [Inhabited V]

/-- **On the good set the honest values of the re-randomised table are `s`.** -/
theorem hv_Psi (g0 : C → V) (s : I → V) (h : Good D g0 s) : hv D (Psi D g0 s) = s :=
  hv_unique D _ s fun i => by rw [pos_Psi D g0 s h, Psi_pos D g0 s h]

/-- The good set of a table. -/
def GoodT (g : C → V) : Prop :=
  Function.Injective (D.pos g (hv D g)) ∧ ∀ i, D.pos g (hv D g) i ∉ D.P

/-- The re-randomisation map. -/
noncomputable def reRand (p : (C → V) × (I → V)) : (C → V) × (I → V) :=
  (Psi D p.1 p.2, fun i => p.1 (D.pos p.1 p.2 i))

open Classical in
/-- Its inverse on the good set. -/
noncomputable def unRand (p : (C → V) × (I → V)) : (C → V) × (I → V) :=
  (fun q => if h : ∃ i, D.pos p.1 (hv D p.1) i = q then p.2 (Classical.choose h) else p.1 q,
    hv D p.1)

theorem goodT_reRand (p : (C → V) × (I → V)) (h : Good D p.1 p.2) : GoodT D (reRand D p).1 := by
  show GoodT D (Psi D p.1 p.2)
  unfold GoodT
  rw [hv_Psi D p.1 p.2 h]
  have e : D.pos (Psi D p.1 p.2) p.2 = D.pos p.1 p.2 := funext (pos_Psi D p.1 p.2 h)
  rw [e]
  exact h

theorem unRand_reRand (p : (C → V) × (I → V)) (h : Good D p.1 p.2) :
    unRand D (reRand D p) = p := by
  classical
  obtain ⟨g0, s⟩ := p
  have hv' := hv_Psi D g0 s h
  have e : D.pos (Psi D g0 s) s = D.pos g0 s := funext (pos_Psi D g0 s h)
  refine Prod.ext ?_ hv'
  funext q
  show (if h' : ∃ i, D.pos (Psi D g0 s) (hv D (Psi D g0 s)) i = q then
      g0 (D.pos g0 s (Classical.choose h')) else Psi D g0 s q) = g0 q
  by_cases hq : ∃ i, D.pos g0 s i = q
  · have hq' : ∃ i, D.pos (Psi D g0 s) (hv D (Psi D g0 s)) i = q := by rw [hv', e]; exact hq
    rw [dif_pos hq']
    have hs := Classical.choose_spec hq'
    have e2 : D.pos (Psi D g0 s) (hv D (Psi D g0 s)) = D.pos g0 s := by rw [hv', e]
    rw [(congrFun e2 _).symm.trans hs]
  · have hq' : ¬ ∃ i, D.pos (Psi D g0 s) (hv D (Psi D g0 s)) i = q := by rw [hv', e]; exact hq
    rw [dif_neg hq']
    exact Psi_of_not D g0 s q fun i hi => hq ⟨i, hi⟩

theorem unRand_P (p : (C → V) × (I → V)) (h : GoodT D p.1) (q : C) (hq : q ∈ D.P) :
    (unRand D p).1 q = p.1 q := by
  classical
  show (if h' : ∃ i, D.pos p.1 (hv D p.1) i = q then _ else _) = _
  rw [dif_neg (fun ⟨i, hi⟩ => h.2 i (hi ▸ hq))]

theorem pos_unRand (p : (C → V) × (I → V)) (h : GoodT D p.1) (i : I) :
    D.pos (unRand D p).1 (hv D p.1) i = D.pos p.1 (hv D p.1) i :=
  D.depG _ _ _ i fun q hq => unRand_P D p h q hq

theorem good_unRand (p : (C → V) × (I → V)) (h : GoodT D p.1) :
    Good D (unRand D p).1 (unRand D p).2 := by
  show Good D (unRand D p).1 (hv D p.1)
  have e : D.pos (unRand D p).1 (hv D p.1) = D.pos p.1 (hv D p.1) :=
    funext (pos_unRand D p h)
  unfold Good
  rw [e]
  exact h

theorem reRand_unRand (p : (C → V) × (I → V)) (h : GoodT D p.1) :
    reRand D (unRand D p) = p := by
  classical
  obtain ⟨g, t⟩ := p
  have e : D.pos (unRand D (g, t)).1 (hv D g) = D.pos g (hv D g) :=
    funext (pos_unRand D (g, t) h)
  have hU : ∀ i, (unRand D (g, t)).1 (D.pos g (hv D g) i) = t i := by
    intro i
    have hex : ∃ j, D.pos g (hv D g) j = D.pos g (hv D g) i := ⟨i, rfl⟩
    show (if h' : ∃ j, D.pos g (hv D g) j = D.pos g (hv D g) i then _ else _) = _
    rw [dif_pos hex, h.1 (Classical.choose_spec hex)]
  refine Prod.ext ?_ ?_
  · funext q
    show Psi D (unRand D (g, t)).1 (hv D g) q = g q
    by_cases hq : ∃ i, D.pos g (hv D g) i = q
    · obtain ⟨i, rfl⟩ := hq
      rw [← e, Psi_pos D (unRand D (g, t)).1 (hv D g) (good_unRand D (g, t) h) i, e]
      exact hv_eq D g i
    · rw [Psi_of_not D _ _ q (by rw [e]; exact fun i hi => hq ⟨i, hi⟩)]
      show (if h' : ∃ i, D.pos g (hv D g) i = q then _ else _) = _
      rw [dif_neg hq]
  · funext i
    show (unRand D (g, t)).1 (D.pos (unRand D (g, t)).1 (hv D g) i) = t i
    rw [e, hU]

end Psi

/-! ## The expectation inequality -/

section Ex

variable [DecidableEq C] [Inhabited V] [Fintype C] [Fintype V] [Fintype I] [DecidableEq I]
  [DecidableEq V] [SampleableType (C → V)] [SampleableType (I → V)]

theorem ex_uniform {X : Type} [SampleableType X] [Fintype X] (F : X → ℝ≥0∞) :
    ex ($ᵗ X) F = (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ x, F x := by
  unfold ex
  rw [tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton]

open Classical in
/-- The sum over the good set is the sum over the good tables. -/
theorem sum_good (F : (C → V) × (I → V) → ℝ≥0∞) :
    ∑ p ∈ (Finset.univ.filter fun p : (C → V) × (I → V) => Good D p.1 p.2), F (reRand D p) =
      ∑ p ∈ (Finset.univ.filter fun p : (C → V) × (I → V) => GoodT D p.1), F p := by
  refine Finset.sum_nbij' (reRand D) (unRand D) (fun p hp => ?_) (fun p hp => ?_)
    (fun p hp => ?_) (fun p hp => ?_) (fun p hp => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact goodT_reRand D p hp
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact good_unRand D p hp
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact unRand_reRand D p hp
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact reRand_unRand D p hp

open Classical in
/-- **Re-randomisation with collisions.**  For every `f ≤ 1` on tables, the expectation over a
uniform table is at most the expectation at the re-randomised table plus the probability that
the honest cells of `(g0, s)` collide or meet `P`. -/
theorem ex_le_Psi (f : (C → V) → ℝ≥0∞) (hf : ∀ g, f g ≤ 1) :
    ex ($ᵗ (C → V)) f ≤
      ex ($ᵗ (C → V)) (fun g0 => ex ($ᵗ (I → V)) fun s => f (Psi D g0 s)) +
        ex ($ᵗ (C → V)) (fun g0 => ex ($ᵗ (I → V)) fun s => propInd (¬ Good D g0 s)) := by
  classical
  rw [← ex_add]
  simp only [← ex_add]
  set N1 := (Fintype.card (C → V) : ℝ≥0∞)⁻¹
  set N2 := (Fintype.card (I → V) : ℝ≥0∞)⁻¹
  have hN2 : N2 * (Fintype.card (I → V) : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by simp) (by simp)
  -- both sides as sums over pairs
  have hL : ex ($ᵗ (C → V)) f = N1 * N2 * ∑ p : (C → V) × (I → V), f p.1 := by
    rw [ex_uniform, Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← mul_assoc, hN2, one_mul]
  have hR : ex ($ᵗ (C → V)) (fun g0 => ex ($ᵗ (I → V)) fun s =>
      f (Psi D g0 s) + propInd (¬ Good D g0 s)) =
      N1 * N2 * ∑ p : (C → V) × (I → V), (f (Psi D p.1 p.2) + propInd (¬ Good D p.1 p.2)) := by
    rw [ex_uniform, Fintype.sum_prod_type, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g0 _ => ?_
    rw [ex_uniform]
  rw [hL, hR]
  refine mul_le_mul' le_rfl ?_
  -- split both sums by goodness
  have e1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ((C → V) × (I → V)))
    (fun p => GoodT D p.1) (fun p => f p.1)
  have e2 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ((C → V) × (I → V)))
    (fun p => Good D p.1 p.2) (fun p => f (Psi D p.1 p.2) + propInd (¬ Good D p.1 p.2))
  have hg := sum_good D (fun p => f p.1)
  have hc := sum_good D (fun _ => (1 : ℝ≥0∞))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  rw [← e1, ← e2]
  -- the good parts
  have hgood : ∑ p ∈ Finset.univ.filter (fun p : (C → V) × (I → V) => GoodT D p.1), f p.1 ≤
      ∑ p ∈ Finset.univ.filter (fun p : (C → V) × (I → V) => Good D p.1 p.2),
        (f (Psi D p.1 p.2) + propInd (¬ Good D p.1 p.2)) := by
    rw [← hg]
    exact Finset.sum_le_sum fun p _ => le_self_add
  -- the bad parts
  have hbad : ∑ p ∈ Finset.univ.filter (fun p : (C → V) × (I → V) => ¬ GoodT D p.1), f p.1 ≤
      ∑ p ∈ Finset.univ.filter (fun p : (C → V) × (I → V) => ¬ Good D p.1 p.2),
        (f (Psi D p.1 p.2) + propInd (¬ Good D p.1 p.2)) := by
    have hcard : (Finset.univ.filter (fun p : (C → V) × (I → V) => ¬ GoodT D p.1)).card =
        (Finset.univ.filter (fun p : (C → V) × (I → V) => ¬ Good D p.1 p.2)).card := by
      have a1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ :
        Finset ((C → V) × (I → V)))) (fun p => GoodT D p.1)
      have a2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ :
        Finset ((C → V) × (I → V)))) (fun p => Good D p.1 p.2)
      have hc' : (Finset.univ.filter (fun p : (C → V) × (I → V) => Good D p.1 p.2)).card =
          (Finset.univ.filter (fun p : (C → V) × (I → V) => GoodT D p.1)).card := by
        exact_mod_cast hc
      omega
    calc _ ≤ ∑ p ∈ Finset.univ.filter (fun p : (C → V) × (I → V) => ¬ GoodT D p.1),
          (1 : ℝ≥0∞) := Finset.sum_le_sum fun p _ => hf _
      _ = ∑ p ∈ Finset.univ.filter (fun p : (C → V) × (I → V) => ¬ Good D p.1 p.2),
          (1 : ℝ≥0∞) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
      _ ≤ _ := Finset.sum_le_sum fun p hp => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rw [(propInd_eq_one_iff).2 hp]
          exact le_add_self
  exact add_le_add hgood hbad

end Ex

end Ideal.Direct.Dag

#print axioms Ideal.Direct.Dag.hv_eq
#print axioms Ideal.Direct.Dag.hv_Psi
#print axioms Ideal.Direct.Dag.sum_good
#print axioms Ideal.Direct.Dag.ex_le_Psi
