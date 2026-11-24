import Integration.SlhDsaShakePermutationAbsorb
import VCVio.OracleComp.Constructions.RandomPermutation.Conditioning

/-! Classical two-way lazy sampling. A trace records constraints in the
forward direction even for inverse queries. The transition law disintegrates
the uniform permutation over extensions of the enlarged trace. -/

namespace Reduction.ShakePermutation.Classic
open OracleComp OracleSpec PermutationConditioning
open SetOracle (uniformMean)
open scoped ENNReal
open Classical
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A]
abbrev EdgeTrace (A : Type) := List (A × A)

theorem mean_equiv {B C : Type} [Fintype B] [Fintype C] (e : B ≃ C) (f : C → ℝ≥0∞) :
    uniformMean (fun x => f (e x)) = uniformMean f := by
  simpa only [uniformMean,unifW,Fintype.card_congr e] using
    Equiv.sum_comp e (fun c => (Fintype.card C : ℝ≥0∞)⁻¹ * f c)

/-- A single fresh forward query. The continuation may still depend on
the entire permutation. -/
theorem fresh_forward (t : EdgeTrace A) (x : UnusedInputs t) (ok : Nonempty (Extensions t))
    (f : A → Equiv.Perm A → ℝ≥0∞) :
    uniformMean (fun p : Extensions t => f (p.val x.val) p.val) =
      uniformMean (fun y : UnusedOutputs t => uniformMean
        (fun p : Extensions ((x.val,y.val)::t) => f y.val p.val)) := by
  classical
  let E := Extensions t
  let Y := UnusedOutputs t
  let fiber (y : Y) := AnswerFiber t x y
  letI : Fintype Y := inferInstanceAs (Fintype (UnusedOutputs t))
  letI (y : Y) : Fintype (fiber y) := inferInstanceAs (Fintype (AnswerFiber t x y))
  let split : Sigma fiber ≃ E := Equiv.sigmaFiberEquiv (PermutationConditioning.answer t x)
  let same (y : Y) := answerFiberEquivExtended t x y
  have sumE (g : E → ℝ≥0∞) : ∑ p, g p = ∑ y : Y, ∑ v : fiber y, g v.1 := by
    exact (Equiv.sum_comp split g).symm.trans (Fintype.sum_sigma (fun v : Sigma fiber => g v.2.1))
  unfold uniformMean
  rw [sumE]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum,← Equiv.sum_comp (same y)]
  apply Finset.sum_congr rfl
  intro v _
  have h := congrArg Subtype.val v.2
  change v.val.val x.val = y.val at h
  change unifW _ v.val * f (v.val.val x.val) v.val.val =
    unifW _ y * (unifW _ (same y v) * f y.val v.val.val)
  rw [h,← mul_assoc]
  congr 1
  unfold unifW
  rw [card_extensions_eq_mul t x y, Fintype.card_congr (same y),Nat.cast_mul,
    ENNReal.mul_inv (by simp) (by simp)]

def orient (back : Bool) (t : EdgeTrace A) := if back then t.map Prod.swap else t
def edge (back : Bool) (x y : A) := if back then (y,x) else (x,y)
def call (p : Equiv.Perm A) (back : Bool) (x : A) := if back then p.symm x else p x

private def revRest (t : EdgeTrace A) (x y : A) :
    Extensions ((x,y)::t.map Prod.swap) ≃ Extensions ((y,x)::t) :=
  (inverseExtensionsEquiv ((x,y)::t.map Prod.swap)).trans
    (extensionsEquivOfMemIff _ _ (by simp [List.map_map,Function.comp_def]))

theorem fresh_step (t : EdgeTrace A) (back : Bool) (x : UnusedInputs (orient back t)) (ok : Nonempty (Extensions t))
    (f : A → Equiv.Perm A → ℝ≥0∞) :
    uniformMean (fun p : Extensions t => f (call p.val back x.val) p.val) =
      uniformMean (fun y : UnusedOutputs (orient back t) => uniformMean
        (fun p : Extensions (edge back x.val y.val::t) => f y.val p.val)) := by
  cases back
  · exact fresh_forward t x ok f
  · let inv := inverseExtensionsEquiv t
    let cont := fun (y : A) (p : Equiv.Perm A) => f y p.symm
    change uniformMean (fun p : Extensions t => f (p.val.symm x.val) p.val) = _
    calc
      _ = uniformMean (fun p : Extensions (t.map Prod.swap) => cont (p.val x.val) p.val) :=
        mean_equiv inv _
      _ = _ := (fresh_forward _ x (ok.map inv) cont).trans (by
        apply congrArg uniformMean
        funext y
        exact mean_equiv (revRest t x.val y.val) (fun p => f y.val p.val))

def old (t : EdgeTrace A) (back : Bool) (x : A) := ∃ y, (x,y) ∈ orient back t

/-- An existing directed edge and its inverse are both answered from the trace.
Fresh responses are sampled uniformly among as yet unused targets in the
requested direction. -/
noncomputable def step (t : EdgeTrace A) (back : Bool) (x : A) (k : A → EdgeTrace A → ℝ≥0∞) : ℝ≥0∞ :=
  if h : old t back x then k h.choose t else
    uniformMean fun y : UnusedOutputs (orient back t) => k y.val (edge back x y.val::t)

omit [Fintype A] [DecidableEq A] in
private theorem old_call (t : EdgeTrace A) (d : Bool) (x : A) (h : old t d x) (p : Extensions t) :
    call p.val d x = h.choose := by
  have edgeMem := h.choose_spec
  cases d with
  | false => exact p.property _ edgeMem
  | true => exact (inverseExtensionsEquiv t p).property _ edgeMem

omit [Fintype A] [DecidableEq A] in
private theorem unused (t : EdgeTrace A) (d : Bool) (x : A) (h : ¬old t d x) :
    ∀ e ∈ orient d t, x ≠ e.1 := by
  rintro ⟨i,y⟩ he rfl
  exact h ⟨y,he⟩

theorem conditional_step (t : EdgeTrace A) (d : Bool) (x : A) (ok : Nonempty (Extensions t))
    (f : A → Equiv.Perm A → ℝ≥0∞) :
    uniformMean (fun p : Extensions t => f (call p.val d x) p.val) =
      step t d x (fun y t' => uniformMean (fun p : Extensions t' => f y p.val)) := by
  by_cases known : old t d x
  · simp only [step,dite_eq_left known,old_call t d x known]
  · exact (fresh_step t d ⟨x,unused t d x known⟩ ok f).trans (by simp only [step,dite_eq_right known])

theorem step_congr (t : EdgeTrace A) (d : Bool) (x : A) (ok : Nonempty (Extensions t))
    {f g : A → EdgeTrace A → ℝ≥0∞}
    (h : ∀ y t', Nonempty (Extensions t') → f y t' = g y t') : step t d x f = step t d x g := by
  unfold step
  split
  · exact h _ _ ok
  · rename_i fresh
    apply congrArg uniformMean
    funext y
    apply h
    let i : UnusedInputs (orient d t) := ⟨x,unused t d x fresh⟩
    cases d with
    | false => exact extensions_cons_nonempty t i y ok
    | true =>
      have ext := extensions_cons_nonempty (t.map Prod.swap) i y (ok.map (inverseExtensionsEquiv t))
      exact ext.map (revRest t x y.val)

abbrev TwoWay (A : Type) := unifSpec + ((Bool × A) →ₒ A)

/-- The acceptance weight at fixed permutation, with all adversary randomness
represented by the explicit uniform-sampling interface. -/
noncomputable def eager {Z : Type} (p : Equiv.Perm A) (ev : Z → ℝ≥0∞) (P : OracleComp (TwoWay A) Z) : ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℝ≥0∞) ev (fun i _ k => match i with
    | .inl _ => uniformMean k
    | .inr (d,x) => k (call p d x)) P

noncomputable def lazyRun {Z : Type} (ev : Z → ℝ≥0∞) (P : OracleComp (TwoWay A) Z) : EdgeTrace A → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => EdgeTrace A → ℝ≥0∞) (fun z _ => ev z) (fun i _ k t => match i with
    | .inl _ => uniformMean fun r => k r t
    | .inr (d,x) => step t d x k) P

private theorem mean_swap {B C : Type} [Fintype B] [Fintype C] (f : B → C → ℝ≥0∞) :
    uniformMean (fun b => uniformMean (f b)) = uniformMean (fun c => uniformMean (fun b => f b c)) := by
  unfold uniformMean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

theorem eager_lazy_aux {Z : Type} (ev : Z → ℝ≥0∞) (P : OracleComp (TwoWay A) Z)
    (t : EdgeTrace A) (ok : Nonempty (Extensions t)) :
    uniformMean (fun p : Extensions t => eager p.val ev P) = lazyRun ev P t := by
  induction P using OracleComp.inductionOn generalizing t with
  | pure z =>
    let _ := ok
    change ∑ p, unifW (Extensions t) p * ev z = ev z
    rw [← Finset.sum_mul,sum_unifW,one_mul]
  | query_bind i k ih =>
    rcases i with u | ⟨d,x⟩
    · change uniformMean (fun p : Extensions t => uniformMean (fun r => eager p.val ev (k r))) =
        uniformMean (fun r => lazyRun ev (k r) t)
      rw [mean_swap]
      exact congrArg uniformMean (funext fun r => ih r t ok)
    · change uniformMean (fun p : Extensions t => eager p.val ev (k (call p.val d x))) = step t d x (fun y t' => lazyRun ev (k y) t')
      exact (conditional_step t d x ok (fun y p => eager p ev (k y))).trans
        (step_congr t d x ok fun y t' ht => ih y t' ht)

theorem eager_lazy {Z : Type} (ev : Z → ℝ≥0∞) (P : OracleComp (TwoWay A) Z) :
    uniformMean (fun p : Equiv.Perm A => eager p ev P) = lazyRun ev P [] := by
  let e : Equiv.Perm A ≃ Extensions [] := ⟨fun p => ⟨p,by simp⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  exact (mean_equiv e (fun p => eager p.val ev P)).trans (eager_lazy_aux ev P [] ⟨e (Equiv.refl _)⟩)

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.fresh_step

#print axioms Reduction.ShakePermutation.Classic.eager_lazy
