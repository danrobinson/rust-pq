import PQ.QROM.PurifyWeight
import PQ.QROM.TightOracle
import PQ.QROM.Defs

/-!
# Every VCVio program is a branch sum of vector-model runs

For a program `x : QuantumComp L (qromSpec X Y) W A`, an interpretation `I`, a function `H` and a
leaf event `E`, `pv I H x E v` is the probability weight of `E` when `x` is run against the
oracle unitary of `H` from the pure (unnormalised) joint state `|v⟩⟨v|` of the program register
and the oracle's trivial private register.  It satisfies

* `pv_pure`: a leaf has weight `‖v‖²` or `0`;
* `pv_primBind`: a local operation is a branch sum over its outcomes and Kraus operators, which
  do not depend on `H`, with `prim_kraus_sum_le`;
* `pv_queryBind`: an oracle call is the vector map `qvec ℓ H = T' ∘ O_H ∘ T`, where `T`, `T'` are
  reindexing isometries not depending on `H` and `O_H = (stdOracle X Y (E × Unit)).O H` is the
  oracle `oracleUnitary H ⊗ 1` of the vector model;
* `qprob_toReal_eq_sum_pv`: `qprob` on an arbitrary (mixed) substate is a finite sum of `pv` over
  vectors that do not depend on `H`.
-/

open Quantum Matrix MeasureTheory ENNReal
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM.Purify

open PQ.QROM.Tight

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The run of a program against the oracle of `H`, on the register `A × Unit`. -/
noncomputable def runH (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A) :
    DSubInstrument (A × Unit) (Σ u, W u) fun p ↦ p.1 × Unit :=
  (additiveOracleRuntime H).run I x

/-- Weight of the leaf event `E` of the program `x` run against `H` from the pure joint state
`|v⟩⟨v|`. -/
noncomputable def pv (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) : ℝ :=
  gv (runH I H x) E v

theorem pv_nonneg (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) : 0 ≤ pv I H x E v :=
  gv_nonneg _ _ _

theorem pv_le (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) : pv I H x E v ≤ ‖v‖ ^ 2 :=
  gv_le _ _ _

open Classical in
theorem pv_pure (I : L.Interp) (H : X → Y) (y : W A) (E : (Σ u, W u) → Prop)
    (v : EuclideanSpace ℂ (A × Unit)) :
    pv I H (QuantumComp.pure (L := L) (spec := qromSpec X Y) y) E v =
      if E ⟨A, y⟩ then ‖v‖ ^ 2 else 0 :=
  gv_ret (B := fun p : Σ u, W u ↦ p.1 × Unit) ⟨A, y⟩ E v

/-- The local operation `o`, framed by the oracle's trivial register. -/
noncomputable def primInstr (I : L.Interp) (o : L.Op A) :
    DSubInstrument (A × Unit) (L.Outcome o) fun b ↦ L.next o b × Unit :=
  (I o).frame Unit

/-- The Kraus operators of a local operation on the joint register (independent of `H`). -/
noncomputable def primKraus (I : L.Interp) (o : L.Op A) (b : L.Outcome o)
    (c : (L.next o b × Unit) × (A × Unit)) :
    EuclideanSpace ℂ (A × Unit) →ₗ[ℂ] EuclideanSpace ℂ (L.next o b × Unit) :=
  Matrix.toEuclideanLin (krausOf (primInstr I o) b c)

theorem prim_kraus_sum_le (I : L.Interp) (o : L.Op A) (s : Finset (L.Outcome o))
    (v : EuclideanSpace ℂ (A × Unit)) :
    ∑ b ∈ s, ∑ c, ‖primKraus I o b c v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
  kraus_sum_le (primInstr I o) s v

/-- **A local operation is a branch sum.** -/
theorem pv_primBind (I : L.Interp) (H : X → Y) (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (qromSpec X Y) W (L.next o b))
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) :
    Summable (fun b ↦ ∑ c, pv I H (k b) E (primKraus I o b c v)) ∧
      pv I H (QuantumComp.primBind o k) E v =
        ∑' b, ∑ c, pv I H (k b) E (primKraus I o b c v) :=
  gv_bind (primInstr I o) (fun b ↦ runH I H (k b)) E v

/-! ### Oracle calls -/

variable {E' : QReg}

/-- Reindexing of the joint register `A × Unit` as query register, workspace. -/
def splitEquiv (ℓ : A ≃ (X × Y) × E') : A × Unit ≃ Reg X Y (E' × Unit) :=
  (ℓ.prodCongr (Equiv.refl Unit)).trans (Equiv.prodAssoc (X × Y) E' Unit)

/-- Reindexing back to the joint register after the call. -/
def joinEquiv (X Y : Type) (E' : QReg) : Reg X Y (E' × Unit) ≃ ((X × Y) × E') × Unit :=
  (Equiv.prodAssoc (X × Y) E' Unit).symm

/-- The (H-independent) isometry exposing the query register. -/
noncomputable def splitIso (ℓ : A ≃ (X × Y) × E') :
    EuclideanSpace ℂ (A × Unit) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Reg X Y (E' × Unit)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv ℓ)

/-- The (H-independent) isometry back to the joint register. -/
noncomputable def joinIso (X Y : Type) [Fintype X] [Fintype Y] (E' : QReg) :
    EuclideanSpace ℂ (Reg X Y (E' × Unit)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (((X × Y) × E') × Unit) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (joinEquiv X Y E')

/-- An oracle call on vectors: expose the query register, apply `oracleUnitary H ⊗ 1` (the
oracle of the vector model), and return. -/
noncomputable def qvec (ℓ : A ≃ (X × Y) × E') (H : X → Y) (v : EuclideanSpace ℂ (A × Unit)) :
    EuclideanSpace ℂ (((X × Y) × E') × Unit) :=
  joinIso X Y E' ((stdOracle X Y (E' × Unit)).O H (splitIso ℓ v))

theorem qvec_apply (ℓ : A ≃ (X × Y) × E') (H : X → Y) (v : EuclideanSpace ℂ (A × Unit))
    (x : X) (y : Y) (e : E') (u : Unit) :
    qvec ℓ H v (((x, y), e), u) = v (ℓ.symm ((x, y - H x), e), u) := by
  change (stdOracle X Y (E' × Unit)).O H (splitIso ℓ v) ((x, y), (e, u)) = _
  exact oracle_apply H (splitIso ℓ v) ((x, y), (e, u))

theorem queryStep_branch_entry (ℓ : A ≃ (X × Y) × E') (H : X → Y)
    (ρ : Matrix (A × (additiveOracleRuntime H).D) (A × (additiveOracleRuntime H).D) ℂ)
    (x : X) (y : Y) (e : E') (u : Unit) (x' : X) (y' : Y) (e' : E') (u' : Unit) :
    ((additiveOracleRuntime H).queryStep (A := A) () E' ℓ).branch () ρ
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

theorem queryStep_branch_ketBra (ℓ : A ≃ (X × Y) × E') (H : X → Y)
    (v : EuclideanSpace ℂ (A × Unit)) :
    ((additiveOracleRuntime H).queryStep (A := A) () E' ℓ).branch ()
        (ketBra v v : Matrix (A × Unit) (A × Unit) ℂ) =
      ketBra (qvec ℓ H v) (qvec ℓ H v) := by
  ext m m'
  obtain ⟨⟨⟨x, y⟩, e⟩, u⟩ := m
  obtain ⟨⟨⟨x', y'⟩, e'⟩, u'⟩ := m'
  refine (queryStep_branch_entry ℓ H _ x y e u x' y' e' u').trans ?_
  exact congrArg₂ (fun a b : ℂ ↦ a * star b) (qvec_apply ℓ H v x y e u).symm
    (qvec_apply ℓ H v x' y' e' u').symm

/-- **An oracle call is one application of the oracle of the vector model.** -/
theorem pv_queryBind (I : L.Interp) (H : X → Y) (ℓ : A ≃ (X × Y) × E')
    (k : Unit → QuantumComp L (qromSpec X Y) W (QReg.of ((X × Y) × E')))
    (E : (Σ u, W u) → Prop) (v : EuclideanSpace ℂ (A × Unit)) :
    pv I H (QuantumComp.queryBind (spec := qromSpec X Y) () E' ℓ k) E v =
      pv I H (k ()) E (qvec ℓ H v) := by
  have h := (DW_bind_re ((additiveOracleRuntime H).queryStep (A := A) () E' ℓ)
    (fun r ↦ runH I H (k r)) E (posSemidef_ketBra_self v)).2
  rw [tsum_fintype, Fintype.sum_unique] at h
  refine h.trans ?_
  change (DW (runH I H (k ())) E
    (((additiveOracleRuntime H).queryStep (A := A) () E' ℓ).branch ()
      (ketBra v v : Matrix (A × Unit) (A × Unit) ℂ))).re = _
  rw [queryStep_branch_ketBra]
  rfl

/-! ### Mixed inputs -/

open scoped MatrixOrder in
/-- A positive semidefinite matrix is a finite sum of rank-one operators `|v⟩⟨v|`. -/
theorem exists_ketBra_sum {n : Type} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) : ∃ vs : n → EuclideanSpace ℂ n, σ = ∑ k, ketBra (vs k) (vs k) := by
  have h0 : 0 ≤ σ := hσ.nonneg
  have hB : (CFC.sqrt σ).IsHermitian := (CFC.sqrt_nonneg σ).posSemidef.isHermitian
  have e : σ = (CFC.sqrt σ)ᴴ * CFC.sqrt σ := by
    rw [hB.eq]
    exact (CFC.sqrt_mul_sqrt_self σ h0).symm
  refine ⟨fun k ↦ WithLp.toLp 2 fun i ↦ star (CFC.sqrt σ k i), ?_⟩
  ext i j
  conv_lhs => rw [e]
  rw [Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [ketBra_apply, Matrix.conjTranspose_apply]

/-- `qprob` is the event weight of the run on `ρ ⊗ |()⟩⟨()|`. -/
theorem qprob_toReal_eq_DW (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (E : (Σ u, W u) → Prop) :
    (qprob I H x ρ E).toReal =
      (DW (runH I H x) E (ρ.prod (SubState.basis ())).matrix).re := by
  have hpsd : ((ρ.prod (SubState.basis ())).matrix).PosSemidef :=
    (ρ.prod (SubState.basis ())).posSemidef
  rw [qprob, QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True),
    ENNReal.tsum_toReal_eq (fun p ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      by_cases h : E p <;> simp [Set.indicator, h])),
    DW_re]
  refine Eq.trans (tsum_congr fun p ↦ ?_)
    (tsum_subtype {p : Σ u, W u | E p}
      (fun p ↦ ((runH I H x).branch p (ρ.prod (SubState.basis ())).matrix).trace.re)).symm
  have hnn : 0 ≤ ((runH I H x).branch p (ρ.prod (SubState.basis ())).matrix).trace.re :=
    (runH I H x).trace_re_branch_apply_nonneg p hpsd
  by_cases h : E p
  · simp only [Set.indicator, Set.mem_singleton_iff, h, Set.mem_ofPred_eq, ite_true,
      Pi.one_apply, mul_one]
    exact ENNReal.toReal_ofReal hnn
  · simp [Set.indicator, h]

/-- An event and its complement have total probability at most one. -/
theorem qprob_toReal_add_not_le_one (I : L.Interp) (H : X → Y)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (E : (Σ u, W u) → Prop) :
    (qprob I H x ρ E).toReal + (qprob I H x ρ (fun p ↦ ¬ E p)).toReal ≤ 1 := by
  rw [qprob_toReal_eq_DW, qprob_toReal_eq_DW]
  exact (DW_re_add_compl_le _ E (ρ.prod (SubState.basis ())).posSemidef).trans
    (ρ.prod (SubState.basis ())).trace_re_le_one

/-- **`qprob` of an arbitrary program on an arbitrary substate is a finite sum of pure-vector
weights**, over vectors that do not depend on `H` and whose squared norms sum to at most one. -/
theorem qprob_toReal_eq_sum_pv (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (E : (Σ u, W u) → Prop) :
    ∃ vs : A × Unit → EuclideanSpace ℂ (A × Unit), ∑ j, ‖vs j‖ ^ 2 ≤ 1 ∧
      ∀ H : X → Y, (qprob I H x ρ E).toReal = ∑ j, pv I H x E (vs j) := by
  obtain ⟨vs, hvs⟩ := exists_ketBra_sum (ρ.prod (SubState.basis ())).posSemidef
  refine ⟨vs, ?_, fun H ↦ ?_⟩
  · have h := (ρ.prod (SubState.basis ())).trace_re_le_one
    rw [hvs, Matrix.trace_sum, Complex.re_sum] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_)) h
    exact (trace_re_ketBra_self _).symm
  · rw [qprob_toReal_eq_DW, hvs, map_sum, Complex.re_sum]
    rfl

end PQ.QROM.Purify

#print axioms PQ.QROM.Purify.pv_primBind
#print axioms PQ.QROM.Purify.pv_queryBind
#print axioms PQ.QROM.Purify.qprob_toReal_eq_sum_pv
#print axioms PQ.QROM.Purify.qprob_toReal_add_not_le_one
