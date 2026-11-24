import Integration.SlhDsaShakePermutationClassicalHidden

/-! Sample an entire finite classical decision tree's coins before running
it. The resulting deterministic tree is independent of all oracle tables. -/
namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp Classical
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section

theorem avg_const {U : Type} [Fintype U] [Nonempty U] (w : ℝ≥0∞) :
    uniformMean (fun _ : U => w) = w := by
  unfold uniformMean; rw [← Finset.sum_mul,sum_unifW,one_mul]

theorem avg_prod {U V : Type} [Fintype U] [Fintype V] (f : U × V → ℝ≥0∞) :
    uniformMean f = uniformMean (fun u => uniformMean (fun v => f (u,v))) := by
  have e := @ENNReal.mul_inv (Fintype.card U : ℝ≥0∞) (Fintype.card V : ℝ≥0∞) (by simp) (by simp)
  simp only [uniformMean,Fintype.sum_prod_type,Finset.mul_sum,unifW,Fintype.card_prod,Nat.cast_mul,e,mul_assoc]

theorem avg_apply {U : Type} [Fintype U] [DecidableEq U] (D : U → Type) [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (i : U) (f : D i → ℝ≥0∞) :
    uniformMean (fun h : (u : U) → D u => f (h i)) = uniformMean f := by
  let set (h : (u : U) → D u) (v : D i) := Function.update h i v
  have invol : Function.Involutive (fun z : ((u : U) → D u) × D i => (set z.1 z.2,z.1 i)) := by
    rintro ⟨h,v⟩
    apply Prod.ext
    · funext j; by_cases e : j=i
      · subst j; simp [set]
      · simp [set,Function.update,e]
    · simp [set]
  have res := SetOracle.avg_resample set (fun h => h i) invol (fun h => f (h i))
  change _ = uniformMean (fun h => uniformMean (fun v => f (set h v i))) at res
  exact res.trans (by simp only [set,Function.update_self,avg_const])

variable {ι Z S : Type} {sp : OracleSpec ι} [∀ i, Fintype (sp.Range i)]

def detRun (step : (i : ι) → S → sp.Range i × S) (ev : Z → S → ℝ≥0∞)
    (P : OracleComp sp Z) : S → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => S → ℝ≥0∞) ev (fun i _ k s => let z := step i s; k z.1 z.2) P

def mixedRun (step : (i : ι) → S → sp.Range i × S) (ev : Z → S → ℝ≥0∞)
    (P : OracleComp (unifSpec + sp) Z) : S → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => S → ℝ≥0∞) ev (fun i _ k s => match i with
    | .inl n => uniformMean fun r : Fin (n+1) => k r s
    | .inr i => let z := step i s; k z.1 z.2) P

structure Resolution (sp : OracleSpec ι) (Z : Type) (P : OracleComp (unifSpec + sp) Z) where
  Coins : Type
  fintype : Fintype Coins
  inhabited : Nonempty Coins
  run : Coins → OracleComp sp Z
  correct : ∀ (σ : Type) (step : (i : ι) → σ → sp.Range i × σ)
    (ev : Z → σ → ℝ≥0∞) (s : σ), mixedRun step ev P s =
      @uniformMean Coins fintype (fun h => detRun step ev (run h) s)

attribute [instance] Resolution.fintype Resolution.inhabited

def resolve (P : OracleComp (unifSpec + sp) Z) : Resolution sp Z P := by
  classical
  induction P using OracleComp.recOn with
  | pure z =>
    exact ⟨Unit,inferInstance,inferInstance,fun _ => pure z,fun σ step ev s => (avg_const (U := Unit) (ev z s)).symm⟩
  | queryBind i k ih =>
    rcases i with n|i
    · let D := fun r : Fin (n+1) => (ih r).Coins
      letI (r : Fin (n+1)) : Fintype (D r) := (ih r).fintype
      letI (r : Fin (n+1)) : Nonempty (D r) := (ih r).inhabited
      refine ⟨Fin (n+1) × ((r : Fin (n+1)) → D r),inferInstance,inferInstance,fun z => (ih z.1).run (z.2 z.1),?_⟩
      intro σ step ev s
      rw [avg_prod]
      change uniformMean (fun r : Fin (n+1) => mixedRun step ev (k r) s) = _
      apply congrArg uniformMean; funext r
      exact ((ih r).correct σ step ev s).trans (avg_apply D r _).symm
    · let D := fun r : sp.Range i => (ih r).Coins
      letI (r : sp.Range i) : Fintype (D r) := (ih r).fintype
      letI (r : sp.Range i) : Nonempty (D r) := (ih r).inhabited
      refine ⟨(r : sp.Range i) → D r,inferInstance,inferInstance,fun h => sp.query i >>= fun r => (ih r).run (h r),?_⟩
      intro σ step ev s
      exact ((ih (step i s).1).correct σ step ev (step i s).2).trans (avg_apply D (step i s).1 _).symm

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.resolve
