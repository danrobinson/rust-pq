import PQ.Interactive.QromBridgeUnif
import VCVio.Quantum.Oracle.ClassicalCalls

/-!
# A classical evaluation of the oracle beside a held register

`run₂_callBasis_branch`: against VCVio's additive oracle `U_H` (`oracleRt H`), the
computational-basis call `QComp.callBasis () B (x, 0) (fun o _ ↦ o.2)` on ANY held register `B`
returns `H x` with certainty and leaves the register untouched: its branch at `y` is the identity
map if `H x = y` and `0` otherwise.

Route: `oracleRt H` is the runtime of the emulated oracle `addEmu H` (trivial private register,
unitary `U_H ⊗ 1`), and VCVio's `EmulatedOracle.branch_run₂_callBasis` computes the branch from
the blocks `⟨o|U|a⟩`.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The additive oracle of `H` as an emulated oracle with a trivial private register. -/
@[reducible] noncomputable def addEmu (H : X → Y) : EmulatedOracle Unit (fun _ ↦ QReg.of (X × Y)) where
  S := QReg.of Unit
  init := SubState.basis ()
  U _ := oracleUnitary H ⊗ₖ (1 : Matrix Unit Unit ℂ)
  unitary _ := kronecker_mem_unitary (oracleUnitary_mem_unitaryGroup H) (one_mem _)

lemma dsub_ext {A ι : Type*} [Fintype A] {B : ι → Type*} [∀ i, Fintype (B i)]
    (p q : DSubInstrument A ι B) (h : p.branch = q.branch) : p = q := by
  cases p; cases q; cases h; rfl

/-- The steps of the runtime of `addEmu H` are those of VCVio's additive oracle runtime. -/
theorem addEmu_step (H : X → Y) : (addEmu H).toRuntime.step = (oracleRt H).step := by
  funext i
  refine dsub_ext _ _ (funext fun u ↦ ?_)
  change (SubInstrument.ofIsometry (oracleUnitary H ⊗ₖ (1 : Matrix Unit Unit ℂ))
    ((addEmu H).conjTranspose_mul_self i)).branch u = ((oracleQuery H).frame Unit).branch u
  refine LinearMap.ext fun ρ ↦ ?_
  rw [SubInstrument.branch_ofIsometry_apply, DSubInstrument.branch_frame_apply,
    branch_oracleQuery_apply, MatrixMap.amplify_conj]

/-- The blocks of the additive oracle. -/
lemma addEmu_block (H : X → Y) (o a : X × Y) :
    (addEmu H).block () o a = if o = (a.1, a.2 + H a.1) then 1 else 0 := by
  ext d d'
  rw [EmulatedOracle.block_apply]
  change (oracleUnitary H ⊗ₖ (1 : Matrix Unit Unit ℂ)) (o, d) (a, d') = _
  rw [Matrix.kroneckerMap_apply, oracleUnitary_apply]
  cases d; cases d'
  by_cases h : o = (a.1, a.2 + H a.1) <;> simp [h]

/-- **Branch law of a classical evaluation of the oracle on a general register.** -/
theorem run₂_callBasis_branch (B : QReg) (H : X → Y) (x : X) (y : Y)
    (M : Matrix (B × Unit) (B × Unit) ℂ) :
    ((oracleRt H).run₂ .instruments
      (QComp.callBasis (spec := qromSpec X Y) () B (x, (0 : Y)) (fun o _ ↦ o.2))).branch y M =
      if H x = y then M else 0 := by
  have h := (addEmu H).branch_run₂_callBasis () B (x, (0 : Y)) (fun o _ ↦ o.2) y
  have aux : ∀ s s' : (∀ i, SubInstrument ((qromSpec X Y).In i × Unit)
      ((qromSpec X Y).Out i × Unit) ((qromSpec X Y).Result i)), s = s' →
      ((⟨QReg.of Unit, SubState.basis (), s'⟩ : QuantumRuntime (qromSpec X Y)).run₂ .instruments
        (QComp.callBasis (spec := qromSpec X Y) () B (x, (0 : Y)) (fun o _ ↦ o.2))).branch y M =
      ((⟨QReg.of Unit, SubState.basis (), s⟩ : QuantumRuntime (qromSpec X Y)).run₂ .instruments
        (QComp.callBasis (spec := qromSpec X Y) () B (x, (0 : Y)) (fun o _ ↦ o.2))).branch y M := by
    rintro s _ rfl
    rfl
  refine (aux _ _ (addEmu_step H)).trans ?_
  refine (congrArg (fun f : MatrixMap _ _ ↦ f M) h).trans ?_
  simp only [addEmu_block, zero_add]
  rw [Finset.sum_eq_single (x, H x)]
  · by_cases hy : H x = y
    · simp [hy]
    · simp [hy]
  · intro o _ ho
    by_cases hr : o.2 = y
    · simp [hr, ho]
    · simp [hr]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

end PQ.Interactive

open PQ.Interactive in
#print axioms run₂_callBasis_branch
