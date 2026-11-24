import Integration.SlhDsaShakePermutationClassicalPublicRisk

namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp Classical ENNReal
open SetOracle (uniformMean)
noncomputable section
variable {I A Z : Type} [DecidableEq I] [Fintype I] [Fintype A] [DecidableEq A] [Nonempty A]

def coherent (H : I → A) (b : Bank I A) := ∀ i v, b i = some v → H i = v

theorem coherent_write {H : I → A} {b : Bank I A} (h : coherent H b) (i : I) :
    coherent H (Function.update b i (some (H i))) := by
  intro j v e
  by_cases eq : j=i
  · subst j; simpa only [Function.update_self,Option.some.injEq] using e
  · exact h _ _ ((Function.update_of_ne eq _ _).symm.trans e)

theorem labelled_add (K : I → Bool → A → A) (f g : Z → ℝ≥0∞) (P : OracleComp (Tagged I A) Z) :
    labelled K (fun z => f z + g z) P = labelled K f P + labelled K g P := by
  induction P using OracleComp.inductionOn with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨j,d,x⟩
    · exact (congrArg uniformMean (funext ih)).trans (mean_add _ _)
    · exact ih _

theorem labelled_one (K : I → Bool → A → A) (P : OracleComp (Tagged I A) Z) :
    labelled K (fun _ => 1) P = 1 := by
  induction P using OracleComp.inductionOn with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨j,d,x⟩
    · exact (congrArg uniformMean (funext ih)).trans (avg_const (U := Fin (n+1)) _)
    · exact ih _

theorem guard_bound {f g : Z → ℝ≥0∞} (h : ∀ z, f z ≤ g z) (H : I → A) (P : OracleComp (Tagged I A) Z)
    (b : Bank I A) (t : EdgeTrace A) (c : coherent H b) : guarded H f P b t ≤ labelled (fun j _ _ => H j) g P := by
  induction P using OracleComp.inductionOn generalizing b t with
  | pure z => exact h _
  | query_bind i k ih =>
    rcases i with n|⟨j,d,x⟩
    · exact mean_mono fun r => ih r b t c
    · cases hj : b j with
      | none =>
        change (match b j with
          | some _ => _
          | none => if old t d x ∨ ¬freshOut t d (H j) then 0 else
            guarded H f (k (H j)) (Function.update b j (some (H j))) (edge d x (H j)::t)) ≤ _
        simp only [hj]
        split
        · exact zero_le
        · exact ih _ _ _ (coherent_write c j)
      | some v =>
        change (match b j with
          | some val => if known : old t d x then if val = known.choose then guarded H f (k val) b t else 0 else 0
          | none => _) ≤ labelled _ _ (k (H j))
        simp only [hj]
        split
        · split
          · rw [c j v hj]; exact ih _ _ _ c
          · exact zero_le
        · exact zero_le

theorem guarded_add (H : I → A) (f g : Z → ℝ≥0∞) (P : OracleComp (Tagged I A) Z)
    (b : Bank I A) (t : EdgeTrace A) :
    guarded H (fun z => f z + g z) P b t = guarded H f P b t + guarded H g P b t := by
  induction P using OracleComp.inductionOn generalizing b t with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨j,d,x⟩
    · exact (congrArg uniformMean (funext fun r => ih r b t)).trans (mean_add _ _)
    · simp only [guarded,OracleComp.construct_query_bind]
      cases b j <;> repeat' first | split | rfl | exact ih _ _ _ | simp

theorem compare_acceptance (P : OracleComp (Tagged I A) Bool) (loss : ℝ≥0∞)
    (coverage : 1 ≤ uniformMean (fun H => guarded H (fun _ => 1) P (fun _ => none) []) + loss) :
    uniformMean (fun π : Equiv.Perm A => eager π (fun v => hit (v=true)) (simulateQ forgetTag P)) ≤
      uniformMean (fun H : I → A => labelled (fun j _ _ => H j) (fun v => hit (v=true)) P) + loss := by
  let real (f : Bool → ℝ≥0∞) := uniformMean (fun π : Equiv.Perm A => labelled (fun _ => call π) f P)
  let kept (f : Bool → ℝ≥0∞) := uniformMean (fun H : I → A => guarded H f P (fun _ => none) [])
  let ideal (f : Bool → ℝ≥0∞) := uniformMean (fun H : I → A => labelled (fun j _ _ => H j) f P)
  let yes := fun v : Bool => hit (v=true)
  let no := fun v : Bool => hit (v=false)
  have tot : (fun v => yes v + no v) = fun _ => 1 := by funext v; cases v <;> simp [yes,no,hit]
  have norm : real yes + real no = 1 := by
    unfold real; rw [← mean_add]; simp_rw [← labelled_add,tot,labelled_one]; exact avg_const _
  have sum : kept (fun _ => 1) = kept yes + kept no := by
    unfold kept; rw [← mean_add,← tot]; exact congrArg uniformMean (funext fun H => guarded_add H yes no P _ _)
  have g : kept yes ≤ ideal yes := mean_mono fun H => guard_bound (fun _ => le_rfl) H P _ _ (by simp [coherent])
  have h : kept no ≤ real no := (transcript_coefficient no P).trans_eq (congrArg uniformMean
    (funext fun π => labelled_forget π no P))
  have fin : kept no ≠ ⊤ := (lt_of_le_of_lt (h.trans ((le_add_left le_rfl).trans_eq norm)) one_lt_top).ne
  simp_rw [labelled_forget]
  apply (ENNReal.add_le_add_iff_right fin).mp
  change real yes + kept no ≤ ideal yes + loss + kept no
  calc _ ≤ real yes + real no := add_le_add le_rfl h
       _ = 1 := norm
       _ ≤ kept yes + kept no + loss := coverage.trans_eq (congrArg (·+loss) sum)
       _ ≤ _ := by rw [add_right_comm]; exact add_le_add (add_le_add g le_rfl) le_rfl

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.compare_acceptance
