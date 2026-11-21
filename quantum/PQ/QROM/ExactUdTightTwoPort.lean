import PQ.QROM.PurifyInstances
import PQ.QROM.TwoPhaseGame

/-!
# The tight hidden-set bound for the two-port hash oracle

`PQ/QROM/PurifyTight.lean` proves the tight bound `8 q² ε` for programs over the single-port
signature `qromSpec X Y`.  The exact two-phase games (`PQ/QROM/TwoPhaseGame.lean`) run programs
over the two-port signature `qrom2Spec X Y` against `twoRuntime fun _ ↦ H` (both ports answered
by the same function).  This file repeats the induction for that runtime:

* `leafProb2_tight_avg`, `leafProb2_tightAvgBound`: for every program `x` over `qrom2Spec X Y`
  with `x.IsQueryBound bud`, every substate `ρ` and leaf event `E`, the functional
  `H ↦ (leafProb (twoRuntime fun _ ↦ H) I x (joint ρ) E).toReal` satisfies the tight hidden-set
  bound with `q = bud false + bud true` (the TOTAL number of calls, over both ports).
-/

open Quantum Matrix Finset MeasureTheory ENNReal
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM.Purify

open PQ.QROM.Tight

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The run of a two-port program against the same function on both ports. -/
noncomputable def run2 (I : L.Interp) (H : X → Y) (x : QuantumComp L (qrom2Spec X Y) W A) :
    DSubInstrument (A × Unit) (Σ u, W u) fun p ↦ p.1 × Unit :=
  (twoRuntime fun _ ↦ H).run I x

/-- Weight of the leaf event `E` of the two-port program `x` run against `H` (on both ports)
from the pure joint state `|v⟩⟨v|`. -/
noncomputable def pv2 (I : L.Interp) (H : X → Y) (x : QuantumComp L (qrom2Spec X Y) W A)
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) : ℝ :=
  gv (run2 I H x) E v

open Classical in
theorem pv2_pure (I : L.Interp) (H : X → Y) (y : W A) (E : (Σ u, W u) → Prop)
    (v : EuclideanSpace ℂ (A × Unit)) :
    pv2 I H (QuantumComp.pure (L := L) (spec := qrom2Spec X Y) y) E v =
      if E ⟨A, y⟩ then ‖v‖ ^ 2 else 0 :=
  gv_ret (B := fun p : Σ u, W u ↦ p.1 × Unit) ⟨A, y⟩ E v

theorem pv2_primBind (I : L.Interp) (H : X → Y) (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (qrom2Spec X Y) W (L.next o b))
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) :
    Summable (fun b ↦ ∑ c, pv2 I H (k b) E (primKraus I o b c v)) ∧
      pv2 I H (QuantumComp.primBind o k) E v =
        ∑' b, ∑ c, pv2 I H (k b) E (primKraus I o b c v) :=
  gv_bind (primInstr I o) (fun b ↦ run2 I H (k b)) E v

variable {E' : QReg}

theorem queryStep2_branch_entry (i : Bool) (ℓ : A ≃ (X × Y) × E') (H : X → Y)
    (ρ : Matrix (A × (twoRuntime fun _ : Bool ↦ H).D) (A × (twoRuntime fun _ : Bool ↦ H).D) ℂ)
    (x : X) (y : Y) (e : E') (u : Unit) (x' : X) (y' : Y) (e' : E') (u' : Unit) :
    ((twoRuntime fun _ : Bool ↦ H).queryStep (A := A) i E' ℓ).branch () ρ
        (((x, y), e), u) (((x', y'), e'), u') =
      ρ (ℓ.symm ((x, y - H x), e), u) (ℓ.symm ((x', y' - H x'), e'), u') := by
  rw [QuantumRuntime.queryStep_branch_apply]
  simp only [SubInstrument.relabel_branch_apply, Matrix.submatrix_apply]
  change (((oracleQuery H).branch ()).amplify Unit).amplify E'
    (ρ.submatrix
      (QuantumRuntime.queryEquivIn ℓ Unit).symm (QuantumRuntime.queryEquivIn ℓ Unit).symm)
    (((x, y), u), e) (((x', y'), u'), e') = _
  rw [MatrixMap.amplify_apply, MatrixMap.amplify_apply, branch_oracleQuery_apply,
    conj_oracleUnitary_apply]
  rfl

theorem queryStep2_branch_ketBra (i : Bool) (ℓ : A ≃ (X × Y) × E') (H : X → Y)
    (v : EuclideanSpace ℂ (A × Unit)) :
    ((twoRuntime fun _ : Bool ↦ H).queryStep (A := A) i E' ℓ).branch ()
        (ketBra v v : Matrix (A × Unit) (A × Unit) ℂ) =
      ketBra (qvec ℓ H v) (qvec ℓ H v) := by
  ext m m'
  obtain ⟨⟨⟨x, y⟩, e⟩, u⟩ := m
  obtain ⟨⟨⟨x', y'⟩, e'⟩, u'⟩ := m'
  refine (queryStep2_branch_entry i ℓ H _ x y e u x' y' e' u').trans ?_
  exact congrArg₂ (fun a b : ℂ ↦ a * star b) (qvec_apply ℓ H v x y e u).symm
    (qvec_apply ℓ H v x' y' e' u').symm

theorem pv2_queryBind (I : L.Interp) (H : X → Y) (i : Bool) (ℓ : A ≃ (X × Y) × E')
    (k : Unit → QuantumComp L (qrom2Spec X Y) W (QReg.of ((X × Y) × E')))
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) :
    pv2 I H (QuantumComp.queryBind (spec := qrom2Spec X Y) i E' ℓ k) E v =
      pv2 I H (k ()) E (qvec ℓ H v) := by
  have h := (DW_bind_re ((twoRuntime fun _ : Bool ↦ H).queryStep (A := A) i E' ℓ)
    (fun r ↦ run2 I H (k r)) E (posSemidef_ketBra_self v)).2
  rw [tsum_fintype, Fintype.sum_unique] at h
  refine h.trans ?_
  change (DW (run2 I H (k ())) E
    (((twoRuntime fun _ : Bool ↦ H).queryStep (A := A) i E' ℓ).branch ()
      (ketBra v v : Matrix (A × Unit) (A × Unit) ℂ))).re = _
  rw [queryStep2_branch_ketBra]
  rfl

/-- `leafProb` is the event weight of the run. -/
theorem leafProb2_toReal_eq_DW (I : L.Interp) (H : X → Y) (x : QuantumComp L (qrom2Spec X Y) W A)
    {σ : Matrix (A × Unit) (A × Unit) ℂ} (hσ : σ.PosSemidef) (E : (Σ u, W u) → Prop) :
    (leafProb (twoRuntime fun _ ↦ H) I x σ E).toReal = (DW (run2 I H x) E σ).re := by
  rw [leafProb, ENNReal.tsum_toReal_eq (fun p ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      by_cases h : E p <;> simp [ind, Set.indicator, h])), DW_re]
  refine Eq.trans (tsum_congr fun p ↦ ?_)
    (tsum_subtype {p : Σ u, W u | E p}
      (fun p ↦ ((run2 I H x).branch p σ).trace.re)).symm
  have hnn : 0 ≤ ((run2 I H x).branch p σ).trace.re :=
    (run2 I H x).trace_re_branch_apply_nonneg p hσ
  by_cases h : E p
  · simp only [ind, Set.indicator, Set.mem_singleton_iff, h, Set.mem_ofPred_eq, ite_true,
      Pi.one_apply, mul_one]
    exact ENNReal.toReal_ofReal hnn
  · simp [ind, Set.indicator, h]

section Main

variable {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (Hs : ι → X → Y) (G : X → Y)
  (S : ι → Finset X) (hS : ∀ s k, Hs s k ≠ G k → k ∈ S s) (r : ℝ) (hr : 0 ≤ r)
  (hε : ∀ k, ∑ s with k ∈ S s, w s ≤ r ^ 2)

include hw hS hr hε

/-- The invariant of the induction, two-port version; the budget is the total number of calls. -/
theorem pv2_tight (I : L.Interp) (E : (Σ u, W u) → Prop) {A : QReg}
    (x : QuantumComp L (qrom2Spec X Y) W A) :
    ∀ bud : Bool → ℕ, x.IsQueryBound bud → ∀ (ψ : EuclideanSpace ℂ (A × Unit))
      (δ : ι → EuclideanSpace ℂ (A × Unit)) (m a d : ℝ), 0 ≤ m → 0 ≤ a → 0 ≤ d → ‖ψ‖ ≤ m →
      ∑ s, w s * ‖δ s‖ ^ 2 ≤ a ^ 2 → ‖∑ s, (w s : ℂ) • δ s‖ ≤ d →
      |∑ s, w s * pv2 I (Hs s) x E (ψ + δ s) - (∑ s, w s) * pv2 I G x E ψ| ≤
        Fq r (bud false + bud true) m a d := by
  classical
  refine QuantumComp.inductionOn (motive := fun A x ↦ ∀ bud : Bool → ℕ, x.IsQueryBound bud →
    ∀ (ψ : EuclideanSpace ℂ (A × Unit)) (δ : ι → EuclideanSpace ℂ (A × Unit)) (m a d : ℝ),
      0 ≤ m → 0 ≤ a → 0 ≤ d → ‖ψ‖ ≤ m → ∑ s, w s * ‖δ s‖ ^ 2 ≤ a ^ 2 →
      ‖∑ s, (w s : ℂ) • δ s‖ ≤ d →
      |∑ s, w s * pv2 I (Hs s) x E (ψ + δ s) - (∑ s, w s) * pv2 I G x E ψ| ≤
        Fq r (bud false + bud true) m a d)
    ?_ ?_ ?_ x
  · -- leaf
    intro A y bud _ ψ δ m a d hm ha hd hψ hδ hδbar
    obtain ⟨n, hn⟩ : ∃ n, n = bud false + bud true := ⟨_, rfl⟩
    rw [← hn]
    simp only [pv2_pure]
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
    intro A o k ih bud hq ψ δ m a d hm ha hd hψ hδ hδbar
    obtain ⟨n, hn⟩ : ∃ n, n = bud false + bud true := ⟨_, rfl⟩
    rw [← hn]
    have hq' : ∀ b, (k b).IsQueryBound bud := (QuantumComp.isQueryBound_primBind_iff o k _).1 hq
    obtain ⟨sG, eG⟩ := pv2_primBind I G o k E ψ
    have hG := eG ▸ sG.hasSum
    have hs : ∀ s, HasSum (fun b ↦ ∑ c, pv2 I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)))
        (pv2 I (Hs s) (QuantumComp.primBind o k) E (ψ + δ s)) := fun s ↦ by
      obtain ⟨ss, es⟩ := pv2_primBind I (Hs s) o k E (ψ + δ s)
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
        |∑ s, w s * pv2 I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
          (∑ s, w s) * pv2 I G (k b) E (primKraus I o b c ψ)| ≤
        Fq r n (mi ⟨b, c⟩) (ai ⟨b, c⟩) (di ⟨b, c⟩) := by
      intro b c
      have h := ih b bud (hq' b) (primKraus I o b c ψ) (fun s ↦ primKraus I o b c (δ s))
        (mi ⟨b, c⟩) (ai ⟨b, c⟩) (di ⟨b, c⟩) (norm_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _)
        le_rfl
        (le_of_eq (Real.sq_sqrt (Finset.sum_nonneg fun s _ ↦
          mul_nonneg (hw s) (sq_nonneg _))).symm)
        (le_of_eq (by
          simp only [di, map_sum, map_smul]))
      rw [← hn] at h
      simpa only [map_add] using h
    have hTb : ∀ b, |∑ s, w s * ∑ c, pv2 I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
        (∑ s, w s) * ∑ c, pv2 I G (k b) E (primKraus I o b c ψ)| ≤
        ∑ c, Fq r n (mi ⟨b, c⟩) (ai ⟨b, c⟩) (di ⟨b, c⟩) := by
      intro b
      have e : ∑ s, w s * ∑ c, pv2 I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
          (∑ s, w s) * ∑ c, pv2 I G (k b) E (primKraus I o b c ψ) =
          ∑ c, (∑ s, w s * pv2 I (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
            (∑ s, w s) * pv2 I G (k b) E (primKraus I o b c ψ)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.mul_sum]
        simp only [Finset.mul_sum]
      rw [e]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ hbr b c)
    have hsum : ∑ b ∈ t, |(∑ s, w s * ∑ c, pv2 I (Hs s) (k b) E (primKraus I o b c (ψ + δ s))) -
        (∑ s, w s) * ∑ c, pv2 I G (k b) E (primKraus I o b c ψ)| ≤
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
    intro A i E' ℓ k ih bud hq ψ δ m a d hm ha hd hψ hδ hδbar
    obtain ⟨hn, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff (L := L) (spec := qrom2Spec X Y)
      i E' ℓ k bud).1 hq
    have htot : Function.update bud i (bud i - 1) false + Function.update bud i (bud i - 1) true
        + 1 = bud false + bud true := by
      cases i <;> simp [Function.update] <;> omega
    simp only [pv2_queryBind]
    obtain ⟨c1, c2, c3⟩ := query_step w hw Hs G S hS r hr hε (stdOracle X Y (E' × Unit))
      (splitIso ℓ) (joinIso X Y E') ψ δ m a d hm ha hd hψ hδ hδbar
    have h := ih () _ (hk ()) (qvec ℓ G ψ) (fun s ↦ qvec ℓ (Hs s) (ψ + δ s) - qvec ℓ G ψ) m
      (a + 2 * r * m) (d + 2 * r ^ 2 * m + 2 * r * a) hm (by positivity) (by positivity)
      c1 c2 c3
    rw [Fq_query, htot] at h
    simp only [add_sub_cancel] at h
    exact h

/-- The tight bound for a two-port program, `r = √ε` form. -/
theorem leafProb2_tight_avg_sqrt (I : L.Interp) {A : QReg}
    (x : QuantumComp L (qrom2Spec X Y) W A) (ρ : SubState A) (bud : Bool → ℕ)
    (hx : x.IsQueryBound bud) (E : (Σ u, W u) → Prop) :
    |∑ s, w s * (leafProb (twoRuntime fun _ ↦ Hs s) I x (joint ρ) E).toReal -
        (∑ s, w s) * (leafProb (twoRuntime fun _ ↦ G) I x (joint ρ) E).toReal| ≤
      8 * ((bud false + bud true : ℕ) : ℝ) ^ 2 * r ^ 2 := by
  obtain ⟨vs, hvs⟩ := exists_ketBra_sum (joint_posSemidef ρ)
  have hnorm : ∑ j, ‖vs j‖ ^ 2 ≤ 1 := by
    have h := (ρ.prod (SubState.basis ())).trace_re_le_one
    change (joint ρ).trace.re ≤ 1 at h
    rw [hvs, Matrix.trace_sum, Complex.re_sum] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_)) h
    exact (trace_re_ketBra_self _).symm
  have hq : ∀ H : X → Y, (leafProb (twoRuntime fun _ ↦ H) I x (joint ρ) E).toReal =
      ∑ j, pv2 I H x E (vs j) := fun H ↦ by
    rw [leafProb2_toReal_eq_DW I H x (joint_posSemidef ρ), hvs, map_sum, Complex.re_sum]
    rfl
  have hj : ∀ j, |∑ s, w s * pv2 I (Hs s) x E (vs j) - (∑ s, w s) * pv2 I G x E (vs j)| ≤
      8 * ((bud false + bud true : ℕ) : ℝ) ^ 2 * r ^ 2 * ‖vs j‖ ^ 2 := by
    intro j
    have h := pv2_tight w hw Hs G S hS r hr hε I E x bud hx (vs j) (fun _ ↦ 0) ‖vs j‖ 0 0
      (norm_nonneg _) le_rfl le_rfl le_rfl (by simp) (by simp)
    simp only [add_zero] at h
    refine h.trans (le_of_eq ?_)
    unfold Fq
    ring
  have e : ∑ s, w s * (leafProb (twoRuntime fun _ ↦ Hs s) I x (joint ρ) E).toReal -
      (∑ s, w s) * (leafProb (twoRuntime fun _ ↦ G) I x (joint ρ) E).toReal =
      ∑ j, (∑ s, w s * pv2 I (Hs s) x E (vs j) - (∑ s, w s) * pv2 I G x E (vs j)) := by
    simp only [hq]
    rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.mul_sum]
    simp only [Finset.mul_sum]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ ↦ hj j).trans ?_)
  rw [← Finset.mul_sum]
  calc 8 * ((bud false + bud true : ℕ) : ℝ) ^ 2 * r ^ 2 * ∑ j, ‖vs j‖ ^ 2
      ≤ 8 * ((bud false + bud true : ℕ) : ℝ) ^ 2 * r ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := mul_one _

end Main

end PQ.QROM.Purify

namespace PQ.QROM.Tight

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Every two-port program satisfies the tight hidden-set bound**, with `q` the total number
of oracle calls over both ports. -/
theorem leafProb2_tightAvgBound (I : L.Interp) (x : QuantumComp L (qrom2Spec X Y) W A)
    (ρ : SubState A) (bud : Bool → ℕ) (hx : x.IsQueryBound bud) (E : (Σ u, W u) → Prop) :
    TightAvgBound (fun H ↦ (leafProb (twoRuntime fun _ ↦ H) I x (joint ρ) E).toReal)
      (bud false + bud true) := by
  intro ι _ w hw Hs G S hS ε hε0 hε
  have h := Purify.leafProb2_tight_avg_sqrt w hw Hs G S hS (Real.sqrt ε) (Real.sqrt_nonneg ε)
    (by rw [Real.sq_sqrt hε0]; exact hε) I x ρ bud hx E
  rwa [Real.sq_sqrt hε0] at h

end PQ.QROM.Tight

#print axioms PQ.QROM.Purify.pv2_tight
#print axioms PQ.QROM.Tight.leafProb2_tightAvgBound
