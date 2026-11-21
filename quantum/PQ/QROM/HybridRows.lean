import PQ.QROM.ExactDsprTightGame

/-!
# The rows bound for the hybrid model of a one-port program

`PQ.QROM.Rows.RowsBound` (the target-count-free second-order bound behind the tight DSPR term) is
proved in `ExactDsprTightGame.lean` for `HybridModel.ofSecondPort` models of two-port programs.
This file proves it for `HybridModel.ofProgram` models of ONE-port programs:

* `toSecond x`: the one-port program `x` over `qromSpec X Y` as a two-port program over
  `qrom2Spec X Y` that calls only port `true` (same local operations, same registers);
* `toSecond_isQueryBound`: `q` calls of `x` give the budget `secondBudget q`;
* `run_toSecond`: against `twoRuntime (ports F H)` the relabelled program runs exactly as `x`
  against `additiveOracleRuntime H` (both runtimes have the private register `Unit` and the step
  `(oracleQuery H).frame Unit` on the used port);
* **`ofProgram_rowsBound`**: `RowsBound` for `ofProgram I x ρ q hx dec`, by `rows_adv_le` on
  `toSecond x` and `tr (ρ ⊗ |()⟩⟨()|) ≤ 1`.
-/

open Quantum Matrix Finset MeasureTheory ENNReal
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM.Rows

open PQ.QROM.Tight PQ.QROM.Purify

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w}

/-- A one-port program as a two-port program calling only port `true`. -/
noncomputable def toSecond : {A : QReg} → QuantumComp L (qromSpec X Y) W A →
    QuantumComp L (qrom2Spec X Y) W A :=
  fun {_} x ↦ IPFunctor.IFreeM.fold (P := QuantumComp.toIPFunctor L (qromSpec X Y))
    (D := fun A ↦ QuantumComp L (qrom2Spec X Y) W A)
    (fun _ y ↦ QuantumComp.pure y)
    (fun _ cmd next ↦ match cmd with
      | .prim o => QuantumComp.primBind o fun b ↦ next (ULift.up b)
      | .query _ E ℓ => QuantumComp.queryBind (spec := qrom2Spec X Y) true E ℓ
          fun r ↦ next (ULift.up r)) x

theorem toSecond_pure {A : QReg} (y : W A) :
    toSecond (X := X) (Y := Y) (QuantumComp.pure (L := L) (spec := qromSpec X Y) y) =
      QuantumComp.pure y := rfl

theorem toSecond_primBind {A : QReg} (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (qromSpec X Y) W (L.next o b)) :
    toSecond (QuantumComp.primBind o k) = QuantumComp.primBind o fun b ↦ toSecond (k b) := rfl

theorem toSecond_queryBind {A : QReg} (i : Unit) (E : QReg) (ℓ : A ≃ (qromSpec X Y).In i × E)
    (k : Unit → QuantumComp L (qromSpec X Y) W (QReg.of ((qromSpec X Y).Out i × E))) :
    toSecond (QuantumComp.queryBind i E ℓ k) =
      QuantumComp.queryBind (spec := qrom2Spec X Y) true E ℓ fun r ↦ toSecond (k r) := rfl

theorem toSecond_isQueryBoundAt {A : QReg} (x : QuantumComp L (qromSpec X Y) W A) :
    (∀ n, x.IsQueryBoundAt () n → (toSecond x).IsQueryBoundAt true n) ∧
      (toSecond x).IsQueryBoundAt false 0 := by
  induction x using QuantumComp.inductionOn with
  | pure A y => exact ⟨fun _ _ ↦ trivial, trivial⟩
  | primBind A o k ih =>
    rw [toSecond_primBind]
    refine ⟨fun n h ↦ ?_, ?_⟩
    · rw [QuantumComp.isQueryBoundAt_primBind_iff] at h ⊢
      exact fun b ↦ (ih b).1 n (h b)
    · rw [QuantumComp.isQueryBoundAt_primBind_iff]
      exact fun b ↦ (ih b).2
  | queryBind A i E ℓ k ih =>
    rw [toSecond_queryBind]
    refine ⟨fun n h ↦ ?_, ?_⟩
    · rw [QuantumComp.isQueryBoundAt_queryBind_iff] at h ⊢
      have h1 := h.1 rfl
      exact ⟨fun _ ↦ ⟨h1.1, fun r ↦ (ih r).1 _ (h1.2 r)⟩, fun hne ↦ absurd rfl hne⟩
    · rw [QuantumComp.isQueryBoundAt_queryBind_iff]
      exact ⟨fun h ↦ Bool.noConfusion h, fun _ r ↦ (ih r).2⟩

theorem toSecond_isQueryBound {A : QReg} {x : QuantumComp L (qromSpec X Y) W A} {q : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) : (toSecond x).IsQueryBound (secondBudget q) := by
  intro b
  cases b
  · simpa [secondBudget] using (toSecond_isQueryBoundAt x).2
  · simpa [secondBudget] using (toSecond_isQueryBoundAt x).1 q (hx ())

theorem run_toSecond (I : L.Interp) (F H : X → Y) {A : QReg}
    (x : QuantumComp L (qromSpec X Y) W A) :
    (twoRuntime (ports F H)).run I (toSecond x) = (additiveOracleRuntime H).run I x := by
  induction x using QuantumComp.inductionOn with
  | pure A y =>
    rw [toSecond_pure, QuantumRuntime.run_pure, QuantumRuntime.run_pure]
    rfl
  | primBind A o k ih =>
    rw [toSecond_primBind, QuantumRuntime.run_primBind, QuantumRuntime.run_primBind]
    simp only [ih]
    rfl
  | queryBind A i E ℓ k ih =>
    rw [toSecond_queryBind, QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
    simp only [ih]
    rfl

theorem leafProb_toSecond (I : L.Interp) (F H : X → Y) {A : QReg}
    (x : QuantumComp L (qromSpec X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ)
    (E : (Σ u, W u) → Prop) :
    leafProb (twoRuntime (ports F H)) I (toSecond x) σ E =
      leafProb (additiveOracleRuntime H) I x σ E := by
  unfold leafProb
  rw [run_toSecond]
  rfl

/-- **The rows bound for the model of a one-port program.** -/
theorem ofProgram_rowsBound (I : L.Interp) {A : QReg} (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (q : ℕ) (hx : QueryBounded x q) {Leaf : Type} (dec : (Σ u, W u) → Leaf) :
    RowsBound (fun H E ↦ ((HybridModel.ofProgram I x ρ q hx dec).prob H E).toReal) q := by
  intro J _ _ p r row G h Ev hp0 hp1 hr hpr hdisj g hg0 hg
  set σ : Matrix (A × Unit) (A × Unit) ℂ := ρ.matrix ⊗ₖ (SubState.basis ()).matrix with hσdef
  have hσ : σ.PosSemidef := (ρ.prod (SubState.basis ())).posSemidef
  have htr1 : σ.trace.re ≤ 1 := (ρ.prod (SubState.basis ())).trace_re_le_one
  have htr0 : 0 ≤ σ.trace.re := hσ.trace_re_nonneg
  have hmain := rows_adv_le p hp0 hp1 r hr hpr row G h G I (fun j l ↦ Ev j (dec l))
    (fun i j l hi hj ↦ hdisj i j (dec l) hi hj) (toSecond x) (secondBudget q)
    (toSecond_isQueryBound hx) hσ g hg0 (fun j ⟨l, hl⟩ ↦ hg j ⟨dec l, hl⟩)
  have hq : secondBudget q true = q := by simp [secondBudget]
  rw [hq] at hmain
  have hp : ∀ (H : X → Y) (E : Leaf → Prop),
      ((HybridModel.ofProgram I x ρ q hx dec).prob H E).toReal =
        (leafProb (twoRuntime (ports G H)) I (toSecond x) σ (fun l ↦ E (dec l))).toReal := by
    intro H E
    rw [HybridModel.ofProgram_prob, leafProb_toSecond]
    unfold qprob
    rw [evalDistMap_eq_leafProb]
    rfl
  simp only [hp]
  have hR : 0 ≤ g + 168 * (q : ℝ) ^ 2 * r ^ 2 := by positivity
  calc _ ≤ (g + 168 * (q : ℝ) ^ 2 * r ^ 2) * σ.trace.re := hmain
    _ ≤ (g + 168 * (q : ℝ) ^ 2 * r ^ 2) * 1 := mul_le_mul_of_nonneg_left htr1 hR
    _ = _ := mul_one _

end PQ.QROM.Rows

#print axioms PQ.QROM.Rows.run_toSecond
#print axioms PQ.QROM.Rows.toSecond_isQueryBound
#print axioms PQ.QROM.Rows.ofProgram_rowsBound
