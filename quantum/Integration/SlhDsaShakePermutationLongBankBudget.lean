import Integration.SlhDsaShakePermutationLongBank
import Integration.SlhDsaShakePermutationItsrBanks

namespace Reduction.ShakePermutation.Long.BankRun
open Quantum Classical MLink OracleSpec OracleComp PQ.Interactive ENNReal SetOracle ItsrLabel
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
attribute [local irreducible] uniformMean
variable {A : Type}

private theorem avg_le {X : Type} [Fintype X] [Nonempty X] (f : X → ℝ≥0∞) (b : ℝ≥0∞)
    (h : ∀ x, f x ≤ b) : uniformMean f ≤ b :=
  (Classic.mean_mono h).trans_eq (Classic.avg_const b)

private theorem update_size {X Y : Type} [Fintype X] [DecidableEq X]
    (D : Database X Y) (x : X) (y : Y) : Database.size (Function.update D x (some y)) ≤ D.size+1 := by
  classical
  change (Finset.univ.filter _).card ≤ (Finset.univ.filter (fun i => (D i).isSome)).card+1
  refine (Finset.card_le_card (t := insert x (Finset.univ.filter fun i => (D i).isSome)) ?_).trans (Finset.card_insert_le ..)
  intro i hi
  by_cases h : i = x
  · simp [h]
  · have v := (Finset.mem_filter.mp hi).2
    rw [Function.update_of_ne h] at v
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,v⟩)

theorem run_le_one (p : OracleComp Spec A) (D : Bank) (W : A → Bank → ℝ≥0∞)
    (one : ∀ a d, W a d ≤ 1) : run W p D ≤ 1 := by
  induction p using OracleComp.inductionOn generalizing D with
  | pure a => exact one a D
  | query_bind i k ih =>
    rcases i with n|x
    · exact avg_le _ _ (fun r => ih r D)
    · change (match D x with | some v => run W (k v) D | none => uniformMean fun v => run W (k v) (Function.update D x (some v))) ≤ 1
      cases e : D x <;> simp only [e]
      · exact avg_le _ _ (fun r => ih r _)
      · exact ih _ D

/-- A classical prephase pays once for each fresh lookup that can spoil its graph. -/
theorem budget (p : OracleComp Spec A) (D : Bank) (Q q : ℕ)
    (count : CountBound (fun i => i.isRight = true) p q) (size : D.size+q ≤ Q)
    (clean : Bank → Prop) [DecidablePred clean] (start : clean D)
    (post : A → Bank → Prop) (history : all p D post) (W : A → Bank → ℝ≥0∞)
    (one : ∀ a d, W a d ≤ 1) (b δ : ℝ≥0∞)
    (leaf : ∀ a d, post a d → clean d → d.size ≤ Q → W a d ≤ b)
    (step : ∀ d : Bank, d.size ≤ Q → clean d → ∀ x, d x = none →
      uniformMean (fun v : Words => Classic.hit (¬clean (Function.update d x (some v)))) ≤ δ) :
    run W p D ≤ b+q*δ := by
  induction p using OracleComp.inductionOn generalizing D q with
  | pure a => exact (leaf a D history start (by omega)).trans (le_self_add ..)
  | query_bind i k ih =>
    rcases i with n|x
    · exact avg_le _ _ (fun r => ih r D q (count r) size start (history r))
    · change (match D x with | some v => run W (k v) D | none => uniformMean fun v => run W (k v) (Function.update D x (some v))) ≤ _
      change (match D x with | some v => all (k v) D post | none => ∀ v, all (k v) (Function.update D x (some v)) post) at history
      obtain ⟨hpos,hcount⟩ := count
      have hq : q-1+1=q := by omega
      cases e : D x with
      | some v =>
        simp only [e] at history ⊢
        exact (ih v D (q-1) (hcount v) (by omega) start history).trans (by gcongr; omega)
      | none =>
        simp only [e] at history ⊢
        let U := fun v : Words => Function.update D x (some v)
        have bound (v : Words) : run W (k v) (U v) ≤ (b+(q-1:ℕ)*δ)+Classic.hit (¬clean (U v)) := by
          by_cases good : clean (U v)
          · simp only [Classic.hit,not_true_eq_false,good,ite_false,add_zero]
            exact ih v (U v) (q-1) (hcount v) (by have sz : Database.size (U v) ≤ D.size+1 := update_size D x v; omega) good (history v)
          · simp only [Classic.hit,good,not_false_eq_true,ite_true]
            exact (run_le_one _ _ _ one).trans (le_add_left le_rfl)
        refine (Classic.mean_mono bound).trans ?_
        rw [Classic.mean_add,Classic.avg_const]
        apply le_trans (add_le_add le_rfl (step D (by omega) start x e))
        apply le_of_eq
        rw [add_assoc,← add_one_mul,← Nat.cast_add_one,hq]
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.budget
