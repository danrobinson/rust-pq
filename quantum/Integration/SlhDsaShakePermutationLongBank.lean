import Integration.SlhDsaShakePermutationItsrReplay
import Integration.SlhDsaShakePermutationClassicalCoefficient

/-! Exact conditional private-table sampling for a classical prephase with a table-dependent quantum continuation. -/
namespace Reduction.ShakePermutation.Long.BankRun
open Classical MLink OracleSpec OracleComp PQ.Interactive ENNReal SetOracle ItsrLabel
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
abbrev Spec := unifSpec + (Addr →ₒ Words)
variable {A B : Type}

def eval (H : Table) (f : A → ℝ≥0∞) (p : OracleComp Spec A) :=
  OracleComp.construct (C:=fun _ => ℝ≥0∞) f (fun i _ k => match i with
    | .inl _ => uniformMean k | .inr x => k (H x)) p

def run (f : A → Bank → ℝ≥0∞) (p : OracleComp Spec A) :=
  OracleComp.construct (C:=fun _ => Bank → ℝ≥0∞) f (fun i _ k D => match i with
    | .inl _ => uniformMean (fun u => k u D)
    | .inr x => match D x with
      | some v => k v D
      | none => uniformMean (fun v => k v (Function.update D x (some v)))) p

private theorem swap {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (f x)) = uniformMean (fun y => uniformMean (fun x => f x y)) := by
  unfold uniformMean; simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]

theorem posterior (f : Table → A → ℝ≥0∞) (p : OracleComp Spec A) (D : Bank) :
    uniformMean (fun H => eval (Classic.fill D H) (f (Classic.fill D H)) p) =
      run (fun z D => uniformMean (fun H => f (Classic.fill D H) z)) p D := by
  induction p using OracleComp.inductionOn generalizing D with
  | pure a => rfl
  | query_bind i k ih =>
    rcases i with n|x
    · change uniformMean (fun H => uniformMean (fun v => eval (Classic.fill D H) (f (Classic.fill D H)) (k v))) = _
      rw [swap]; exact congrArg uniformMean (funext (fun v => ih v D))
    · let W := fun z D => uniformMean (fun H => f (Classic.fill D H) z)
      change uniformMean (fun H => eval (Classic.fill D H) (f (Classic.fill D H)) (k (Classic.fill D H x))) =
        (match D x with | some v => run W (k v) D | none => uniformMean fun v => run W (k v) (Function.update D x (some v)))
      cases e : D x with
      | some v =>
        have hv (H : Table) : Classic.fill D H x = v := by simp [Classic.fill,e]
        simp only [hv]; exact ih v D
      | none =>
        let step (H : Table) := eval H (f H) (k (H x))
        change uniformMean (fun H => step (Classic.fill D H)) = _
        rw [Classic.unfilled D x e step]
        have hv (H : Table) (v : Words) : Classic.fill (Function.update D x (some v)) H x = v := by simp [Classic.fill]
        simp only [step,hv]
        exact congrArg uniformMean (funext (fun v => ih v (Function.update D x (some v))))

def all (p : OracleComp Spec A) (D : Bank) (post : A → Bank → Prop) : Prop :=
  OracleComp.construct (C:=fun _ => Bank → Prop) post (fun i _ k d => match i with
    | .inl _ => ∀ r, k r d
    | .inr x => match d x with
      | some v => k v d
      | none => ∀ v, k v (Function.update d x (some v))) p D

theorem bind (p : OracleComp Spec A) (k : A → OracleComp Spec B) (D : Bank)
    (mid : A → Bank → Prop) (post : B → Bank → Prop) (first : all p D mid)
    (next : ∀ d u, mid d u → all (k d) u post) : all (p >>= k) D post := by
  induction p using OracleComp.inductionOn generalizing D with
  | pure a => simpa only [pure_bind] using next a D first
  | query_bind i f ih =>
    rw [bind_assoc]; rcases i with n|x
    · exact fun v => ih v D (first v)
    · change (match D x with | some v => _ | none => _) at first ⊢
      cases e : D x <;> simp only [e] at first ⊢
      · exact fun v => ih _ _ (first v)
      · exact ih _ _ first
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.posterior
