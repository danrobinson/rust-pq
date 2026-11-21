import PQ.QROM.ExactUdClosed
import PQ.QROM.DsprGiven

/-!
# The exact SM-DT-DSPR game (source final validity) in the QROM, closed

`PQ/QROM/ExactUd.lean` reduces the advantage `dsprSucc − dsprSP` of the exact two-phase
SM-DT-DSPR game to the advantage in the hybrid world (`dspr_adv_le_hyb_add`).  This file bounds
the hybrid-world advantage and closes the game:

* `HybridModel.ofSecondPort_additive`, `HybridModel.ofProgram_additive`: the models of quantum
  query programs are additive (`HybridModel.Additive`, the hypothesis of
  `dspr_embedded_weighted_le`).
* `dsprSuccHyb_le_SPHyb_add`: `dsprSuccHyb ≤ dsprSPHyb + max 0 (2γ − 1) + 8 q₂ / √|Y|`,
  `γ = (1 − 1/|Y|)^(|Msg| − 1)` (second preimages are within the row of a tweak, of size
  `|Msg|`).
* `dspr_exact_adv_le`: `dsprSucc − dsprSP ≤ max 0 (2γ − 1) + 8 q₂ / √|Y| + 2 · seedLoss Sd q₁`.
* `dspr_exact_adv_le_of_card`: for `|Y| < |Msg|` (compressing), `γ ≤ 1/2` and
  `dsprSucc − dsprSP ≤ 8 q₂ / √|Y| + 2 · seedLoss Sd q₁`.

Proof: decomposition over the leaves `p` of phase 1.  A leaf with an invalid history contributes
nothing to success.  For a valid leaf the targets are `fvC p.2.2` (one per target tweak), the
post-state depends on the row only through `fvSeen p.2.2` (the row at the targets and at the
collection queries, which are on other tweaks), and phase 2 is a `q₂`-query algorithm against the
row; `dspr_embedded_weighted_le` bounds success minus baseline by the bound times the weight of
the leaf.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v u₁ v₁ w

set_option linter.unusedSectionVars false

namespace PQ.QROM

/-! ## Additivity of the models of programs -/

theorem ind_or_of_disjoint {P Q : Prop} (h : ¬ (P ∧ Q)) : ind (P ∨ Q) = ind P + ind Q := by
  by_cases hp : P
  · have hq : ¬ Q := fun hq ↦ h ⟨hp, hq⟩
    rw [ind_of_true (Or.inl hp), ind_of_true hp, ind_of_false hq, add_zero]
  · by_cases hq : Q
    · rw [ind_of_true (Or.inr hq), ind_of_false hp, ind_of_true hq, zero_add]
    · rw [ind_of_false (fun h' ↦ h'.elim hp hq), ind_of_false hp, ind_of_false hq, add_zero]

theorem leafProb_or {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)
    {L : LocalSig.{u, v}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L spec W A) (σ : Matrix (A × R.D) (A × R.D) ℂ)
    (E E' : (Σ u, W u) → Prop) (h : ∀ p, ¬ (E p ∧ E' p)) :
    leafProb R I x σ (fun p ↦ E p ∨ E' p) = leafProb R I x σ E + leafProb R I x σ E' := by
  unfold leafProb
  rw [← tsum_add]
  refine tsum_congr fun p ↦ ?_
  rw [ind_or_of_disjoint (h p), mul_add]

/-- The model of a second-port program is additive. -/
theorem HybridModel.ofSecondPort_additive {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
    (I : L.Interp) (F : X → Y) (x : QuantumComp L (qrom2Spec X Y) W A)
    (σ : Matrix (A × Unit) (A × Unit) ℂ) (hσ : σ.PosSemidef) (q : ℕ)
    (hx : x.IsQueryBound (secondBudget q)) {Leaf : Type} (dec : (Σ u, W u) → Leaf) :
    (HybridModel.ofSecondPort I F x σ hσ q hx dec).Additive := by
  intro H E E' h
  change leafProb (twoRuntime (ports F H)) I x σ (fun p ↦ E (dec p) ∨ E' (dec p)) *
      (ENNReal.ofReal σ.trace.re)⁻¹ =
    leafProb (twoRuntime (ports F H)) I x σ (fun p ↦ E (dec p)) * (ENNReal.ofReal σ.trace.re)⁻¹ +
      leafProb (twoRuntime (ports F H)) I x σ (fun p ↦ E' (dec p)) *
        (ENNReal.ofReal σ.trace.re)⁻¹
  rw [leafProb_or _ _ _ _ _ _ fun p ↦ h (dec p), add_mul]

/-- The model of a quantum query program is additive. -/
theorem HybridModel.ofProgram_additive {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
    (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (q : ℕ)
    (hx : QueryBounded x q) {Leaf : Type} (dec : (Σ u, W u) → Leaf) :
    (HybridModel.ofProgram I x ρ q hx dec).Additive := by
  intro H E E' h
  change qprob I H x ρ (fun p ↦ E (dec p) ∨ E' (dec p)) =
    qprob I H x ρ (fun p ↦ E (dec p)) + qprob I H x ρ (fun p ↦ E' (dec p))
  simp only [qprob_eq_tsum]
  rw [← tsum_add]
  refine tsum_congr fun p ↦ ?_
  rw [← mul_add]
  congr 1
  exact ind_or_of_disjoint (h (dec p))

/-! ## The numeric condition -/

/-- `(1 - 1/N)^k ≤ 1/2` for `1 ≤ N ≤ k`. -/
theorem one_sub_inv_pow_le_half (N k : ℕ) (hN : 0 < N) (hk : N ≤ k) :
    (1 - (N : ℝ≥0∞)⁻¹) ^ k ≤ 2⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
  have h0 : (0 : ℝ) ≤ 1 - (N : ℝ)⁻¹ := by linarith
  have h1 : 1 - (N : ℝ)⁻¹ ≤ 1 := by linarith [inv_nonneg.2 hN'.le]
  have hexp : 1 - (N : ℝ)⁻¹ ≤ Real.exp (-(N : ℝ)⁻¹) := by
    have := Real.add_one_le_exp (-(N : ℝ)⁻¹)
    linarith
  have he : Real.exp (-1) ≤ 2⁻¹ := by
    rw [Real.exp_neg]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    exact inv_anti₀ (by norm_num) h2
  have hreal : (1 - (N : ℝ)⁻¹) ^ k ≤ 2⁻¹ :=
    calc (1 - (N : ℝ)⁻¹) ^ k ≤ (1 - (N : ℝ)⁻¹) ^ N := pow_le_pow_of_le_one h0 h1 hk
      _ ≤ Real.exp (-(N : ℝ)⁻¹) ^ N := pow_le_pow_left₀ h0 hexp _
      _ = Real.exp (-1) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
      _ ≤ 2⁻¹ := he
  have hconv : (1 : ℝ≥0∞) - (N : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - (N : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_sub _ (inv_nonneg.2 hN'.le), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos hN', ENNReal.ofReal_natCast]
  rw [hconv, ← ENNReal.ofReal_pow h0]
  refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-! ## The game -/

variable {Sd Tw Msg Y : Type}

section

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Bool) u}

/-- The no-second-preimage probability of a row: `γ = (1 − 1/|Y|)^(|Msg| − 1)`, and the trivial
term `max 0 (2γ − 1)`. -/
noncomputable def dsprTrivial (Msg Y : Type) [Fintype Msg] [Fintype Y] : ℝ≥0∞ :=
  (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1) -
    (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1))

/-- **One leaf of phase 1.** -/
theorem dspr_leaf_le [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (P : Sd) (F : Dom Sd Tw Msg → Y) (p : Σ u, Out u × FvState Tw Msg) :
    (avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprWin cap R l.2 p.2.2)) ≤
      (avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprSPWin cap R l.2 p.2.2)) +
        (dsprTrivial Msg Y + 8 * q₂ * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) *
          avg fun R : Tw × Msg → Y ↦
            ENNReal.ofReal (postOf I ρ fvCh fvInit n x F R p).trace.re := by
  by_cases hv : FvValid cap p.2.2
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    have h0 : ∀ R : Tw × Msg → Y,
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprWin cap R l.2 p.2.2) = 0 := fun R ↦ by
      unfold leafProb
      simp only [tsum_eq_zero_iff]
      intro l
      rw [ind_of_false fun h ↦ hv h.1, mul_zero]
    simp only [h0]
    exact le_antisymm (avg_le fun _ ↦ le_rfl) zero_le
  let τ : (Tw × Msg → Y) → Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
    fun a ↦ postOf I ρ fvCh fvInit n x F a p
  have hτ : ∀ a, (τ a).PosSemidef := fun a ↦ postOf_posSemidef F a p
  let M : (Tw × Msg → Y) → HybridModel (Dom Sd Tw Msg) Y (ℕ × Bool) q₂ := fun a ↦
    HybridModel.ofSecondPort I F (ph2 P p.1 p.2.1) (τ a) (hτ a) q₂ (h2 P p.1 p.2.1) Sigma.snd
  have hpost : ∀ R : Tw × Msg → Y, postOf I ρ fvCh fvInit n x F R p = τ (fvSeen p.2.2 R) :=
    fun R ↦ postOf_eq_fvSeen F R p
  let V : (Tw × Msg → Y) → ℕ × Bool → Prop := fun _ l ↦ (p.2.2.chal[l.1]?).isSome
  let tw : (Tw × Msg → Y) → ℕ × Bool → Tw := fun _ l ↦
    ((p.2.2.chal[l.1]?).map Prod.fst).getD default
  let b : (Tw × Msg → Y) → ℕ × Bool → Prop := fun _ l ↦ l.2 = true
  have hget : ∀ (j : ℕ) (t : Tw) (m : Msg), p.2.2.chal[j]? = some (t, m) →
      fvC p.2.2 t = some m := fun j t m h ↦ find_of_mem hv.2.1 (List.mem_of_getElem? h)
  have hV : ∀ (a : Tw × Msg → Y) (l : ℕ × Bool), V a l → ∃ m, fvC p.2.2 (tw a l) = some m := by
    intro a l hl
    obtain ⟨⟨t, m⟩, htm⟩ := Option.isSome_iff_exists.1 hl
    refine ⟨m, ?_⟩
    simp only [tw, htm, Option.map_some, Option.getD_some]
    exact hget _ _ _ htm
  have hsp : ∀ (R : Tw × Msg → Y) (t : Tw) (m : Msg), fvC p.2.2 t = some m →
      (rowSP (fvC p.2.2) R t ↔ HasSecondPreimage R t m) := by
    intro R t m hc
    constructor
    · rintro ⟨m₁, h1, m', hne, heq⟩
      have : m₁ = m := Option.some.inj (h1.symm.trans hc)
      subst this
      exact ⟨m', fun h ↦ hne h.symm, heq.symm⟩
    · rintro ⟨m', hne, heq⟩
      exact ⟨m, hc, m', fun h ↦ hne h.symm, heq.symm⟩
  have hevS : ∀ R : Tw × Msg → Y, (fun l : Σ _ : QReg, ℕ × Bool ↦ dsprWin cap R l.2 p.2.2) =
      fun l ↦ dsprEvS (fvC p.2.2) (fvSeen p.2.2) V tw b R (Sigma.snd l) := by
    intro R
    funext l
    apply propext
    constructor
    · rintro ⟨-, t, m, htm, hb⟩
      refine ⟨by show (p.2.2.chal[l.2.1]?).isSome = true; rw [htm]; rfl, ?_⟩
      have htw : tw (fvSeen p.2.2 R) l.2 = t := by simp [tw, htm]
      rw [htw, hsp R t m (hget _ _ _ htm)]
      exact hb
    · rintro ⟨hl, hb⟩
      obtain ⟨⟨t, m⟩, htm⟩ := Option.isSome_iff_exists.1 hl
      have htw : tw (fvSeen p.2.2 R) l.2 = t := by simp [tw, htm]
      rw [htw, hsp R t m (hget _ _ _ htm)] at hb
      exact ⟨hv, t, m, htm, hb⟩
  have hevP : ∀ R : Tw × Msg → Y, (fun l : Σ _ : QReg, ℕ × Bool ↦ dsprSPWin cap R l.2 p.2.2) =
      fun l ↦ dsprEvP (fvC p.2.2) (fvSeen p.2.2) V tw R (Sigma.snd l) := by
    intro R
    funext l
    apply propext
    constructor
    · rintro ⟨-, t, m, htm, hb⟩
      refine ⟨by show (p.2.2.chal[l.2.1]?).isSome = true; rw [htm]; rfl, ?_⟩
      have htw : tw (fvSeen p.2.2 R) l.2 = t := by simp [tw, htm]
      rw [htw, hsp R t m (hget _ _ _ htm)]
      exact hb
    · rintro ⟨hl, hb⟩
      obtain ⟨⟨t, m⟩, htm⟩ := Option.isSome_iff_exists.1 hl
      have htw : tw (fvSeen p.2.2 R) l.2 = t := by simp [tw, htm]
      rw [htw, hsp R t m (hget _ _ _ htm)] at hb
      exact ⟨hv, t, m, htm, hb⟩
  have : Nonempty (Dom Sd Tw Msg) := ⟨(P, (default, Classical.arbitrary Msg))⟩
  have h := dspr_embedded_weighted_le (rowEmb P) F (fvC p.2.2) (fvSeen p.2.2)
    (fun k m hc hk R v ↦ fvSeen_update cap p.2.2 hv k m hc hk R v) M
    (fun a ↦ HybridModel.ofSecondPort_additive I F _ _ _ _ _ _) V tw b hV
    (fun a ↦ ENNReal.ofReal (τ a).trace.re) (fun _ ↦ ENNReal.ofReal_ne_top)
  have hS : (avg fun R : Tw × Msg → Y ↦
      leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprWin cap R l.2 p.2.2)) =
      dsprEmbSucc (rowEmb P) F (fvC p.2.2) (fvSeen p.2.2) M V tw b
        (fun a ↦ ENNReal.ofReal (τ a).trace.re) := by
    unfold avg dsprEmbSucc
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    beta_reduce
    rw [HybridModel.ofSecondPort_prob, hpost R, ← patchRow_eq_patch, hevS R]
  have hP : (avg fun R : Tw × Msg → Y ↦
      leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprSPWin cap R l.2 p.2.2)) =
      dsprEmbSP (rowEmb P) F (fvC p.2.2) (fvSeen p.2.2) M V tw
        (fun a ↦ ENNReal.ofReal (τ a).trace.re) := by
    unfold avg dsprEmbSP
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    beta_reduce
    rw [HybridModel.ofSecondPort_prob, hpost R, ← patchRow_eq_patch, hevP R]
  have hWt : (avg fun R : Tw × Msg → Y ↦
      ENNReal.ofReal (postOf I ρ fvCh fvInit n x F R p).trace.re) =
      dsprEmbWeight (fvSeen p.2.2) (fun a ↦ ENNReal.ofReal (τ a).trace.re) := by
    unfold avg dsprEmbWeight
    exact Finset.sum_congr rfl fun R _ ↦ by beta_reduce; rw [hpost R]
  rw [hS, hP, hWt]
  exact h

/-- **SM-DT-DSPR, hybrid world**: success exceeds the baseline by at most
`max 0 (2γ − 1) + 8 q₂ / √|Y|`. -/
theorem dsprSuccHyb_le_SPHyb_add [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSuccHyb I ρ cap n x ph2 ≤ dsprSPHyb I ρ cap n x ph2 +
      (dsprTrivial Msg Y + 8 * q₂ * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) := by
  unfold dsprSuccHyb dsprSPHyb twoPhaseHyb
  refine avg_le_avg_add fun P ↦ avg_le_avg_add fun F ↦ ?_
  simp only [hybProb_eq_tsum hx, avg_tsum]
  refine (tsum_le_tsum fun p ↦ dspr_leaf_le h2 P F p).trans ?_
  rw [tsum_add, ENNReal.tsum_mul_left]
  refine add_le_add le_rfl ((mul_le_mul' le_rfl ?_).trans (mul_one _).le)
  simp only [← avg_tsum]
  refine avg_le fun R ↦ ?_
  exact (tsum_leaf_le (R := twoRuntime fun _ ↦ F) (I := I)
    (phase1 (fvCh R) fvInit n x) (joint_posSemidef ρ)).trans (ofReal_trace_joint_le_one ρ)

/-- **SM-DT-DSPR (source final validity) in the QROM, exact adaptive two-phase game**:
`Success − SPprob ≤ max 0 (2γ − 1) + 8 q₂ / √|Y| + 2 · (4 q₁ / √|Sd|)`,
`γ = (1 − 1/|Y|)^(|Msg| − 1)`. -/
theorem dspr_exact_adv_le [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      (dsprTrivial Msg Y + 8 * q₂ * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) +
        2 * seedLoss Sd q₁ :=
  (dspr_adv_le_hyb_add hx h2).trans
    (add_le_add (tsub_le_iff_left.2 (dsprSuccHyb_le_SPHyb_add hx h2)) le_rfl)

/-- For a compressing hash (`|Y| < |Msg|`) the trivial term vanishes. -/
theorem dsprTrivial_eq_zero [Nonempty Y] (hcard : Fintype.card Y < Fintype.card Msg) :
    dsprTrivial Msg Y = 0 := by
  unfold dsprTrivial
  have h := one_sub_inv_pow_le_half (Fintype.card Y) (Fintype.card Msg - 1) Fintype.card_pos
    (by omega)
  refine tsub_eq_zero_of_le (h.trans ?_)
  calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ _ := tsub_le_tsub_left h 1

/-- **SM-DT-DSPR in the QROM, exact game, compressing hash**: for `|Y| < |Msg|`,
`Success − SPprob ≤ 8 q₂ / √|Y| + 2 · (4 q₁ / √|Sd|)`. -/
theorem dspr_exact_adv_le_of_card [Inhabited Tw] [Nontrivial Y]
    (hcard : Fintype.card Y < Fintype.card Msg)
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      8 * q₂ * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) + 2 * seedLoss Sd q₁ := by
  have : Nonempty Msg := Fintype.card_pos_iff.1 (by omega)
  have h := dspr_exact_adv_le (I := I) (ρ := ρ) (cap := cap) hx h2
  rwa [dsprTrivial_eq_zero hcard, zero_add] at h

end

end PQ.QROM

#print axioms PQ.QROM.HybridModel.ofSecondPort_additive
#print axioms PQ.QROM.HybridModel.ofProgram_additive
#print axioms PQ.QROM.dsprSuccHyb_le_SPHyb_add
#print axioms PQ.QROM.dspr_exact_adv_le
#print axioms PQ.QROM.dspr_exact_adv_le_of_card
