import PQ.QROM.ExactUdTightTwoPort

/-!
# The tight hidden-set bound for second-port programs (port `false` fixed)

The per-leaf analyses of the exact two-phase games run the second phase from an unnormalised
post-state `σ` against `twoRuntime (ports F H)`: port `false` is answered by a fixed function `F`,
port `true` by the function `H` under analysis (`HybridModel.ofSecondPort`,
`PQ/QROM/TwoPhase.lean`).  This file proves the tight hidden-set bound for that model:

* `leafProbPorts_tight_avg`: for every program `x` over `qrom2Spec X Y` with
  `x.IsQueryBound bud`, every positive semidefinite `σ` and leaf event `E`,
  `|∑ s, w s * p (Hs s) - (∑ s, w s) * p G| ≤ 8 (bud true)² ε · tr σ`,
  `p H = (leafProb (twoRuntime (ports F H)) I x σ E).toReal`; only the calls of port `true`
  count, and the bound scales with the trace of the (unnormalised) input.

It is the second-order analogue of `secondPort_hybrid`.  It is NOT used yet: the tight
`T`-independent bound for the exact DSPR-FV game is not proved (see "Status" below).

## Status of the tight DSPR-FV bound

Not proved.  The success-minus-baseline quantity is
`∑_j E_s[(u_j(s) − (1 − u_j(s))) · ‖Q_j ψ^s‖²]`, `u_j(s) = 1` iff the row of target `j` has no
second preimage in world `s`, `Q_j` the projector on "output `(j, b = 0)`".  Applying the tight
bound once per target loses a factor `T` (number of targets).  A `T`-free proof needs, beyond
this engine: (1) product structure of the coupling across target rows (the pattern of row `j` is
independent of the other rows given the view); (2) for every world `s` and row `j`, the run
`ψ^{s,[j]}` against the function with row `j` cleaned, and the deviations
`η_{s,j} = ψ^s − ψ^{s,[j]}`; the exact identities `u_j(s) = 1 → η_{s,j} = 0` and
`∑_s w_s u_j(s) ‖Q_j ψ^s‖² = γ ∑_s w_s ‖Q_j ψ^{s,[j]}‖²`; (3) the invariants
`∑_s w_s ∑_j ‖η_{s,j}‖² ≤ C t² ε` and `∑_j ‖E[η_{s,j} | rows ≠ j]‖² ≤ (C t² ε)²` along the run
(a Gronwall-type recursion, because the base function of `η_{s,j}` depends on `s`).  None of
(1)–(3) is formalised.
-/

open Quantum Matrix Finset MeasureTheory ENNReal
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM.Purify

open PQ.QROM.Tight

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The run of a two-port program against `F` on port `false` and `H` on port `true`. -/
noncomputable def runP (I : L.Interp) (F H : X → Y) (x : QuantumComp L (qrom2Spec X Y) W A) :
    DSubInstrument (A × Unit) (Σ u, W u) fun p ↦ p.1 × Unit :=
  (twoRuntime (ports F H)).run I x

/-- Weight of the leaf event `E` from the pure joint state `|v⟩⟨v|`. -/
noncomputable def pvP (I : L.Interp) (F H : X → Y) (x : QuantumComp L (qrom2Spec X Y) W A)
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) : ℝ :=
  gv (runP I F H x) E v

open Classical in
theorem pvP_pure (I : L.Interp) (F H : X → Y) (y : W A) (E : (Σ u, W u) → Prop)
    (v : EuclideanSpace ℂ (A × Unit)) :
    pvP I F H (QuantumComp.pure (L := L) (spec := qrom2Spec X Y) y) E v =
      if E ⟨A, y⟩ then ‖v‖ ^ 2 else 0 :=
  gv_ret (B := fun p : Σ u, W u ↦ p.1 × Unit) ⟨A, y⟩ E v

theorem pvP_primBind (I : L.Interp) (F H : X → Y) (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (qrom2Spec X Y) W (L.next o b))
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) :
    Summable (fun b ↦ ∑ c, pvP I F H (k b) E (primKraus I o b c v)) ∧
      pvP I F H (QuantumComp.primBind o k) E v =
        ∑' b, ∑ c, pvP I F H (k b) E (primKraus I o b c v) :=
  gv_bind (primInstr I o) (fun b ↦ runP I F H (k b)) E v

variable {E' : QReg}

theorem queryStepG_branch_entry (G' : Bool → X → Y) (i : Bool) (ℓ : A ≃ (X × Y) × E')
    (ρ : Matrix (A × (twoRuntime G').D) (A × (twoRuntime G').D) ℂ)
    (x : X) (y : Y) (e : E') (u : Unit) (x' : X) (y' : Y) (e' : E') (u' : Unit) :
    ((twoRuntime G').queryStep (A := A) i E' ℓ).branch () ρ
        (((x, y), e), u) (((x', y'), e'), u') =
      ρ (ℓ.symm ((x, y - G' i x), e), u) (ℓ.symm ((x', y' - G' i x'), e'), u') := by
  rw [QuantumRuntime.queryStep_branch_apply]
  simp only [SubInstrument.relabel_branch_apply, Matrix.submatrix_apply]
  change (((oracleQuery (G' i)).branch ()).amplify Unit).amplify E'
    (ρ.submatrix
      (QuantumRuntime.queryEquivIn ℓ Unit).symm (QuantumRuntime.queryEquivIn ℓ Unit).symm)
    (((x, y), u), e) (((x', y'), u'), e') = _
  rw [MatrixMap.amplify_apply, MatrixMap.amplify_apply, branch_oracleQuery_apply,
    conj_oracleUnitary_apply]
  rfl

theorem queryStepG_branch_ketBra (G' : Bool → X → Y) (i : Bool) (ℓ : A ≃ (X × Y) × E')
    (v : EuclideanSpace ℂ (A × Unit)) :
    ((twoRuntime G').queryStep (A := A) i E' ℓ).branch ()
        (ketBra v v : Matrix (A × Unit) (A × Unit) ℂ) =
      ketBra (qvec ℓ (G' i) v) (qvec ℓ (G' i) v) := by
  ext m m'
  obtain ⟨⟨⟨x, y⟩, e⟩, u⟩ := m
  obtain ⟨⟨⟨x', y'⟩, e'⟩, u'⟩ := m'
  refine (queryStepG_branch_entry G' i ℓ _ x y e u x' y' e' u').trans ?_
  exact congrArg₂ (fun a b : ℂ ↦ a * star b) (qvec_apply ℓ (G' i) v x y e u).symm
    (qvec_apply ℓ (G' i) v x' y' e' u').symm

theorem pvP_queryBind (I : L.Interp) (F H : X → Y) (i : Bool) (ℓ : A ≃ (X × Y) × E')
    (k : Unit → QuantumComp L (qrom2Spec X Y) W (QReg.of ((X × Y) × E')))
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) :
    pvP I F H (QuantumComp.queryBind (spec := qrom2Spec X Y) i E' ℓ k) E v =
      pvP I F H (k ()) E (qvec ℓ (ports F H i) v) := by
  have h := (DW_bind_re ((twoRuntime (ports F H)).queryStep (A := A) i E' ℓ)
    (fun r ↦ runP I F H (k r)) E (posSemidef_ketBra_self v)).2
  rw [tsum_fintype, Fintype.sum_unique] at h
  refine h.trans ?_
  change (DW (runP I F H (k ())) E
    (((twoRuntime (ports F H)).queryStep (A := A) i E' ℓ).branch ()
      (ketBra v v : Matrix (A × Unit) (A × Unit) ℂ))).re = _
  rw [queryStepG_branch_ketBra]
  rfl

/-- `leafProb` is the event weight of the run. -/
theorem leafProbPorts_toReal_eq_DW (I : L.Interp) (F H : X → Y)
    (x : QuantumComp L (qrom2Spec X Y) W A)
    {σ : Matrix (A × Unit) (A × Unit) ℂ} (hσ : σ.PosSemidef) (E : (Σ u, W u) → Prop) :
    (leafProb (twoRuntime (ports F H)) I x σ E).toReal = (DW (runP I F H x) E σ).re := by
  rw [leafProb, ENNReal.tsum_toReal_eq (fun p ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      by_cases h : E p <;> simp [ind, Set.indicator, h])), DW_re]
  refine Eq.trans (tsum_congr fun p ↦ ?_)
    (tsum_subtype {p : Σ u, W u | E p}
      (fun p ↦ ((runP I F H x).branch p σ).trace.re)).symm
  have hnn : 0 ≤ ((runP I F H x).branch p σ).trace.re :=
    (runP I F H x).trace_re_branch_apply_nonneg p hσ
  by_cases h : E p
  · simp only [ind, Set.indicator, Set.mem_singleton_iff, h, Set.mem_ofPred_eq, ite_true,
      Pi.one_apply, mul_one]
    exact ENNReal.toReal_ofReal hnn
  · simp [ind, Set.indicator, h]

theorem norm_qvec_le (ℓ : A ≃ (X × Y) × E') (H : X → Y) (v : EuclideanSpace ℂ (A × Unit)) :
    ‖qvec ℓ H v‖ ≤ ‖v‖ := by
  rw [qvec, LinearIsometryEquiv.norm_map]
  refine ((stdOracle X Y (E' × Unit)).O_le H _).trans ?_
  rw [LinearIsometryEquiv.norm_map]

section Main

variable {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (Hs : ι → X → Y) (G : X → Y)
  (S : ι → Finset X) (hS : ∀ s k, Hs s k ≠ G k → k ∈ S s) (r : ℝ) (hr : 0 ≤ r)
  (hε : ∀ k, ∑ s with k ∈ S s, w s ≤ r ^ 2)

include hw hS hr hε

/-- The invariant of the induction, second-port version: only calls of port `true` count. -/
theorem pvP_tight (I : L.Interp) (F : X → Y) (E : (Σ u, W u) → Prop) {A : QReg}
    (x : QuantumComp L (qrom2Spec X Y) W A) :
    ∀ bud : Bool → ℕ, x.IsQueryBound bud → ∀ (ψ : EuclideanSpace ℂ (A × Unit))
      (δ : ι → EuclideanSpace ℂ (A × Unit)) (m a d : ℝ), 0 ≤ m → 0 ≤ a → 0 ≤ d → ‖ψ‖ ≤ m →
      ∑ s, w s * ‖δ s‖ ^ 2 ≤ a ^ 2 → ‖∑ s, (w s : ℂ) • δ s‖ ≤ d →
      |∑ s, w s * pvP I F (Hs s) x E (ψ + δ s) - (∑ s, w s) * pvP I F G x E ψ| ≤
        Fq r (bud true) m a d := by
  classical
  refine QuantumComp.inductionOn (motive := fun A x ↦ ∀ bud : Bool → ℕ, x.IsQueryBound bud →
    ∀ (ψ : EuclideanSpace ℂ (A × Unit)) (δ : ι → EuclideanSpace ℂ (A × Unit)) (m a d : ℝ),
      0 ≤ m → 0 ≤ a → 0 ≤ d → ‖ψ‖ ≤ m → ∑ s, w s * ‖δ s‖ ^ 2 ≤ a ^ 2 →
      ‖∑ s, (w s : ℂ) • δ s‖ ≤ d →
      |∑ s, w s * pvP I F (Hs s) x E (ψ + δ s) - (∑ s, w s) * pvP I F G x E ψ| ≤
        Fq r (bud true) m a d)
    ?_ ?_ ?_ x
  · -- leaf
    intro A y bud _ ψ δ m a d hm ha hd hψ hδ hδbar
    obtain ⟨n, hn⟩ : ∃ n, n = bud true := ⟨_, rfl⟩
    rw [← hn]
    simp only [pvP_pure]
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
    obtain ⟨n, hn⟩ : ∃ n, n = bud true := ⟨_, rfl⟩
    rw [← hn]
    have hq' : ∀ b, (k b).IsQueryBound bud := (QuantumComp.isQueryBound_primBind_iff o k _).1 hq
    obtain ⟨sG, eG⟩ := pvP_primBind I F G o k E ψ
    have hG := eG ▸ sG.hasSum
    have hs : ∀ s, HasSum (fun b ↦ ∑ c, pvP I F (Hs s) (k b) E (primKraus I o b c (ψ + δ s)))
        (pvP I F (Hs s) (QuantumComp.primBind o k) E (ψ + δ s)) := fun s ↦ by
      obtain ⟨ss, es⟩ := pvP_primBind I F (Hs s) o k E (ψ + δ s)
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
        |∑ s, w s * pvP I F (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
          (∑ s, w s) * pvP I F G (k b) E (primKraus I o b c ψ)| ≤
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
    have hTb : ∀ b, |∑ s, w s * ∑ c, pvP I F (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
        (∑ s, w s) * ∑ c, pvP I F G (k b) E (primKraus I o b c ψ)| ≤
        ∑ c, Fq r n (mi ⟨b, c⟩) (ai ⟨b, c⟩) (di ⟨b, c⟩) := by
      intro b
      have e : ∑ s, w s * ∑ c, pvP I F (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
          (∑ s, w s) * ∑ c, pvP I F G (k b) E (primKraus I o b c ψ) =
          ∑ c, (∑ s, w s * pvP I F (Hs s) (k b) E (primKraus I o b c (ψ + δ s)) -
            (∑ s, w s) * pvP I F G (k b) E (primKraus I o b c ψ)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.mul_sum]
        simp only [Finset.mul_sum]
      rw [e]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ hbr b c)
    have hsum : ∑ b ∈ t, |(∑ s, w s * ∑ c, pvP I F (Hs s) (k b) E (primKraus I o b c (ψ + δ s))) -
        (∑ s, w s) * ∑ c, pvP I F G (k b) E (primKraus I o b c ψ)| ≤
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
    simp only [pvP_queryBind]
    cases i with
    | false =>
      -- port `false`: the same contraction in every world, no budget spent
      have hb : Function.update bud false (bud false - 1) true = bud true := by simp
      have hlin : ∀ s, qvec ℓ F (ψ + δ s) = qvec ℓ F ψ + qvec ℓ F (δ s) := fun s ↦ by
        simp only [qvec, map_add]
      have hsum : ∑ s, (w s : ℂ) • qvec ℓ F (δ s) = qvec ℓ F (∑ s, (w s : ℂ) • δ s) := by
        simp only [qvec, map_sum, map_smul]
      have h := ih () _ (hk ()) (qvec ℓ F ψ) (fun s ↦ qvec ℓ F (δ s)) m a d hm ha hd
        ((norm_qvec_le ℓ F ψ).trans hψ)
        ((Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_qvec_le ℓ F (δ s)) 2) (hw s)).trans hδ)
        (by rw [hsum]; exact (norm_qvec_le ℓ F _).trans hδbar)
      rw [hb] at h
      simpa only [ports, hlin, Bool.false_eq_true, ite_false] using h
    | true =>
      have htot : Function.update bud true (bud true - 1) true + 1 = bud true := by
        simp only [Function.update_self]
        omega
      obtain ⟨c1, c2, c3⟩ := query_step w hw Hs G S hS r hr hε (stdOracle X Y (E' × Unit))
        (splitIso ℓ) (joinIso X Y E') ψ δ m a d hm ha hd hψ hδ hδbar
      have h := ih () _ (hk ()) (qvec ℓ G ψ) (fun s ↦ qvec ℓ (Hs s) (ψ + δ s) - qvec ℓ G ψ) m
        (a + 2 * r * m) (d + 2 * r ^ 2 * m + 2 * r * a) hm (by positivity) (by positivity)
        c1 c2 c3
      rw [Fq_query, htot] at h
      simp only [add_sub_cancel] at h
      simpa only [ports, ite_true] using h

/-- The tight bound for a second-port program from an unnormalised operator, `r = √ε` form. -/
theorem leafProbPorts_tight_avg_sqrt (I : L.Interp) (F : X → Y) {A : QReg}
    (x : QuantumComp L (qrom2Spec X Y) W A) {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) (bud : Bool → ℕ) (hx : x.IsQueryBound bud) (E : (Σ u, W u) → Prop) :
    |∑ s, w s * (leafProb (twoRuntime (ports F (Hs s))) I x σ E).toReal -
        (∑ s, w s) * (leafProb (twoRuntime (ports F G)) I x σ E).toReal| ≤
      8 * ((bud true : ℕ) : ℝ) ^ 2 * r ^ 2 * σ.trace.re := by
  obtain ⟨vs, hvs⟩ := exists_ketBra_sum hσ
  have hnorm : ∑ j, ‖vs j‖ ^ 2 = σ.trace.re := by
    conv_rhs => rw [hvs]
    rw [Matrix.trace_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ ↦ (trace_re_ketBra_self _).symm
  have hq : ∀ H : X → Y, (leafProb (twoRuntime (ports F H)) I x σ E).toReal =
      ∑ j, pvP I F H x E (vs j) := fun H ↦ by
    rw [leafProbPorts_toReal_eq_DW I F H x hσ]
    conv_lhs => rw [hvs]
    rw [map_sum, Complex.re_sum]
    rfl
  have hj : ∀ j, |∑ s, w s * pvP I F (Hs s) x E (vs j) - (∑ s, w s) * pvP I F G x E (vs j)| ≤
      8 * ((bud true : ℕ) : ℝ) ^ 2 * r ^ 2 * ‖vs j‖ ^ 2 := by
    intro j
    have h := pvP_tight w hw Hs G S hS r hr hε I F E x bud hx (vs j) (fun _ ↦ 0) ‖vs j‖ 0 0
      (norm_nonneg _) le_rfl le_rfl le_rfl (by simp) (by simp)
    simp only [add_zero] at h
    refine h.trans (le_of_eq ?_)
    unfold Fq
    ring
  have e : ∑ s, w s * (leafProb (twoRuntime (ports F (Hs s))) I x σ E).toReal -
      (∑ s, w s) * (leafProb (twoRuntime (ports F G)) I x σ E).toReal =
      ∑ j, (∑ s, w s * pvP I F (Hs s) x E (vs j) - (∑ s, w s) * pvP I F G x E (vs j)) := by
    simp only [hq]
    rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.mul_sum]
    simp only [Finset.mul_sum]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ ↦ hj j).trans ?_)
  rw [← Finset.mul_sum, hnorm]

end Main

/-- **Tight hidden-set bound for second-port programs.**  `x` any program over the two-port
signature with `x.IsQueryBound bud`, port `false` answered by the fixed `F`, `σ` any positive
semidefinite (unnormalised) joint operator, `E` any leaf event.  If the functions `Hs s` on port
`true` differ from `G` only on marked sets `S s` that contain every point with total weight at
most `ε`, the weighted probability of `E` changes by at most `8 (bud true)² ε · tr σ`. -/
theorem leafProbPorts_tight_avg (I : L.Interp) (F : X → Y) {A : QReg}
    (x : QuantumComp L (qrom2Spec X Y) W A) {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) (bud : Bool → ℕ) (hx : x.IsQueryBound bud) (E : (Σ u, W u) → Prop)
    {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (Hs : ι → X → Y) (G : X → Y)
    (S : ι → Finset X) (hS : ∀ s k, Hs s k ≠ G k → k ∈ S s) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ∀ k, ∑ s with k ∈ S s, w s ≤ ε) :
    |∑ s, w s * (leafProb (twoRuntime (ports F (Hs s))) I x σ E).toReal -
        (∑ s, w s) * (leafProb (twoRuntime (ports F G)) I x σ E).toReal| ≤
      8 * ((bud true : ℕ) : ℝ) ^ 2 * ε * σ.trace.re := by
  have h := leafProbPorts_tight_avg_sqrt w hw Hs G S hS (Real.sqrt ε) (Real.sqrt_nonneg ε)
    (by rw [Real.sq_sqrt hε0]; exact hε) I F x hσ bud hx E
  rwa [Real.sq_sqrt hε0] at h

end PQ.QROM.Purify

namespace PQ.QROM.Tight

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The per-leaf model of a second phase satisfies the tight hidden-set bound**: for the
`HybridModel` of a second-port program (`HybridModel.ofSecondPort`, probabilities normalised by
the trace of the post-state), every event probability, as a function of the function on port
`true`, satisfies `TightAvgBound` with the phase-2 budget `q`. -/
theorem ofSecondPort_tightAvgBound (I : L.Interp) (F : X → Y)
    (x : QuantumComp L (qrom2Spec X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ)
    (hσ : σ.PosSemidef) (q : ℕ) (hx : x.IsQueryBound (secondBudget q)) {Leaf : Type}
    (dec : (Σ u, W u) → Leaf) (E : Leaf → Prop) :
    TightAvgBound
      (fun H ↦ ((HybridModel.ofSecondPort I F x σ hσ q hx dec).prob H E).toReal) q := by
  intro ι _ w hw Hs G S hS ε hε0 hε
  have h := Purify.leafProbPorts_tight_avg I F x hσ (secondBudget q) hx (fun p ↦ E (dec p))
    w hw Hs G S hS ε hε0 hε
  have hq : secondBudget q true = q := by simp [secondBudget]
  rw [hq] at h
  have htr : 0 ≤ σ.trace.re := hσ.trace_re_nonneg
  have hp : ∀ H : X → Y, ((HybridModel.ofSecondPort I F x σ hσ q hx dec).prob H E).toReal =
      (leafProb (twoRuntime (ports F H)) I x σ (fun p ↦ E (dec p))).toReal * (σ.trace.re)⁻¹ := by
    intro H
    change (leafProb (twoRuntime (ports F H)) I x σ (fun p ↦ E (dec p)) *
      (ENNReal.ofReal σ.trace.re)⁻¹).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal htr]
  simp only [hp]
  have e : ∑ s, w s * ((leafProb (twoRuntime (ports F (Hs s))) I x σ
        (fun p ↦ E (dec p))).toReal * (σ.trace.re)⁻¹) -
      (∑ s, w s) * ((leafProb (twoRuntime (ports F G)) I x σ
        (fun p ↦ E (dec p))).toReal * (σ.trace.re)⁻¹) =
      (∑ s, w s * (leafProb (twoRuntime (ports F (Hs s))) I x σ (fun p ↦ E (dec p))).toReal -
        (∑ s, w s) * (leafProb (twoRuntime (ports F G)) I x σ (fun p ↦ E (dec p))).toReal) *
        (σ.trace.re)⁻¹ := by
    simp only [sub_mul, Finset.sum_mul, mul_assoc]
  rw [e, abs_mul, abs_of_nonneg (inv_nonneg.2 htr)]
  rcases htr.eq_or_lt with h0 | hpos
  · rw [← h0, _root_.inv_zero, mul_zero]
    positivity
  · calc _ ≤ 8 * (q : ℝ) ^ 2 * ε * σ.trace.re * (σ.trace.re)⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.2 htr)
      _ = _ := by field_simp

end PQ.QROM.Tight

#print axioms PQ.QROM.Purify.pvP_tight
#print axioms PQ.QROM.Purify.leafProbPorts_tight_avg
#print axioms PQ.QROM.Tight.ofSecondPort_tightAvgBound
