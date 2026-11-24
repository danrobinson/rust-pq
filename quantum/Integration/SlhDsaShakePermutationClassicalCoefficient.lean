import Integration.SlhDsaShakePermutationClassicalHidden
import Integration.SlhDsaShakePermutationClassicalForest

/-! Transcript comparison for a sponge simulator. Each private ideal-table
row carries the actual oriented permutation input needed to realize it.
Along a compatible transcript, new uniform permutation answers have at
least the mass of independent uniform words. -/
namespace Reduction.ShakePermutation.Classic
open OracleComp OracleSpec PermutationConditioning Classical
set_option maxHeartbeats 4000000
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
variable {I A Z : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]

abbrev Tagged (I A : Type) := unifSpec + ((I × Bool × A) →ₒ A)
abbrev Bank (I A : Type) := I → Option A

def forgetTag : QueryImpl (Tagged I A) (OracleComp (TwoWay A))
  | .inl n => (TwoWay A).query (.inl n)
  | .inr (_,d,x) => (TwoWay A).query (.inr (d,x))

def fill (b : Bank I A) (H : I → A) (i : I) : A := (b i).getD (H i)

def freshOut (t : EdgeTrace A) (d : Bool) (y : A) := ∀ e ∈ orient d t, y ≠ e.2

/-- Reject at the first transcript inconsistency. The real permutation
can answer all queries in every surviving branch. -/
def guarded (H : I → A) (ev : Z → ℝ≥0∞) (P : OracleComp (Tagged I A) Z) :
    Bank I A → EdgeTrace A → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => Bank I A → EdgeTrace A → ℝ≥0∞) (fun z _ _ => ev z)
    (fun i _ k b t => match i with
      | .inl _ => uniformMean fun r => k r b t
      | .inr (j,d,x) => match b j with
        | some v => if h : old t d x then if v = h.choose then k v b t else 0 else 0
        | none => if old t d x ∨ ¬freshOut t d (H j) then 0 else
            k (H j) (Function.update b j (some (H j))) (edge d x (H j)::t)) P

private theorem swap_means {U V : Type} [Fintype U] [Fintype V] (f : U → V → ℝ≥0∞) :
    uniformMean (fun u => uniformMean (f u)) = uniformMean (fun v => uniformMean (fun u => f u v)) := by
  unfold uniformMean; simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]

private theorem unfilled (b : Bank I A) (j : I) (hj : b j = none) (f : (I → A) → ℝ≥0∞) :
    uniformMean (fun H => f (fill b H)) = uniformMean (fun v : A =>
      uniformMean (fun H => f (fill (Function.update b j (some v)) H))) := by
  let sw (z : (I → A) × A) := (Function.update z.1 j z.2,z.1 j)
  have invol : Function.Involutive sw := by
    rintro ⟨H,v⟩
    apply Prod.ext
    · funext k; by_cases e : k=j <;> simp [sw,Function.update,e]
    · simp [sw]
  have rr := SetOracle.avg_resample (fun H v => Function.update H j v) (fun H => H j) invol (fun H => f (fill b H))
  change uniformMean (fun H => f (fill b H)) = uniformMean (fun H => uniformMean (fun v => f (fill b (Function.update H j v)))) at rr
  rw [rr,swap_means]
  apply congrArg uniformMean; funext v
  apply congrArg uniformMean; funext H
  apply congrArg f; funext k
  by_cases e : k=j <;> simp [fill,Function.update,e,hj]

private theorem sub_weight (t : EdgeTrace A) (d : Bool) (f : A → ℝ≥0∞) :
    uniformMean (fun y => if freshOut t d y then f y else 0) ≤
      uniformMean (fun y : UnusedOutputs (orient d t) => f y.val) := by
  classical
  unfold uniformMean
  simp only [mul_ite,mul_zero]
  rw [← Finset.sum_filter]
  let g (y : {y // freshOut t d y}) := unifW A y.val * f y.val
  have eq : ∑ y ∈ Finset.univ.filter (freshOut t d), unifW A y * f y = ∑ y : {y // freshOut t d y}, g y := by
    exact Finset.sum_subtype (Finset.univ.filter (freshOut t d)) (fun x => by simp) (fun y => unifW A y * f y)
  rw [eq]
  let e : {y // freshOut t d y} ≃ UnusedOutputs (orient d t) := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
  rw [← Equiv.sum_comp e (fun y => unifW _ y * f y.val)]
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul' _ le_rfl
  exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Fintype.card_subtype_le _))

theorem guarded_domination (ev : Z → ℝ≥0∞) (P : OracleComp (Tagged I A) Z)
    (b : Bank I A) (t : EdgeTrace A) :
    uniformMean (fun H => guarded (fill b H) ev P b t) ≤ lazyRun ev (simulateQ forgetTag P) t := by
  induction P using OracleComp.inductionOn generalizing b t with
  | pure z =>
    change ∑ H : I → A, unifW (I → A) H * ev z ≤ ev z
    rw [← Finset.sum_mul,sum_unifW,one_mul]
  | query_bind i k ih =>
    rcases i with n|⟨j,d,x⟩
    · simp only [simulateQ_bind,simulateQ_spec_query,forgetTag]
      change uniformMean (fun H => uniformMean (fun r => guarded (fill b H) ev (k r) b t)) ≤
        uniformMean (fun r => lazyRun ev (simulateQ forgetTag (k r)) t)
      rw [swap_means]
      exact Finset.sum_le_sum fun r _ => mul_le_mul' le_rfl (ih _ b t)
    · simp only [simulateQ_bind,simulateQ_spec_query,forgetTag]
      change _ ≤ step t d x (fun y t' => lazyRun ev (simulateQ forgetTag (k y)) t')
      cases hj : b j with
      | some v =>
        change uniformMean (fun H => match b j with
          | some v => if h : old t d x then if v = h.choose then guarded (fill b H) ev (k v) b t else 0 else 0
          | none => _) ≤ _
        simp only [hj,step]
        split
        · rename_i h
          by_cases same : v = h.choose
          · subst v; simp only [ite_true]; exact ih _ b t
          · simp [same,uniformMean]
        · simp [uniformMean]
      | none =>
        rw [unfilled b j hj (fun H => guarded H ev ((Tagged I A).query (.inr (j,d,x)) >>= k) b t)]
        let nxt (v : A) := Function.update b j (some v)
        change uniformMean (fun v => uniformMean (fun H => match b j with
          | some _ => _
          | none => if old t d x ∨ ¬freshOut t d (fill (nxt v) H j) then 0 else
            guarded (fill (nxt v) H) ev (k (fill (nxt v) H j))
              (Function.update b j (some (fill (nxt v) H j))) (edge d x (fill (nxt v) H j)::t))) ≤ _
        have filled (v : A) (H : I → A) : fill (nxt v) H j = v := by simp [fill,nxt]
        simp only [hj,filled,step]
        split
        · rename_i h; simp [h,uniformMean]
        · rename_i fresh
          simp only [fresh,false_or,ite_not]
          let f (y : A) := lazyRun ev (simulateQ forgetTag (k y)) (edge d x y::t)
          apply le_trans _ (sub_weight t d f)
          apply Finset.sum_le_sum
          intro y _
          apply mul_le_mul' le_rfl
          by_cases good : freshOut t d y
          · simp only [good,ite_true]; exact ih _ (nxt y) _
          · simp [good,uniformMean]

theorem transcript_coefficient (ev : Z → ℝ≥0∞) (P : OracleComp (Tagged I A) Z) :
    uniformMean (fun H => guarded H ev P (fun _ => none) []) ≤
      uniformMean (fun π : Equiv.Perm A => eager π ev (simulateQ forgetTag P)) := by
  rw [eager_lazy]
  exact guarded_domination ev P (fun _ => none) []

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.transcript_coefficient
