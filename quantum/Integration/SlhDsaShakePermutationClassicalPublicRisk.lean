import Integration.SlhDsaShakePermutationClassicalHistory
import Integration.SlhDsaShakePermutationClassicalCoins
import Integration.SlhDsaShakePermutationClassicalIdeal

namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp MLink SLHDSA PQ.Interactive
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1600000

def publicIdx {S : Sha2Set} {N : ℕ} : (Outer S N).Domain → Bool
  | .inr (.inl _) => true
  | _ => false

def publicBad (S : Sha2Set) (N T : ℕ) {Z : Type} (rates : Row T → Rate) (caps : Row T → Capacity)
    (raw : ShakeApi.RawTable S N) (P : OracleComp (Outer S N) Z) : EdgeTrace Words → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => EdgeTrace Words → ℝ≥0∞) (fun _ _ => 0)
    (fun i _ k t => match i with
      | .inl _ => uniformMean fun r => k r t
      | .inr (.inr x) => k (raw x) t
      | .inr (.inl (d,x)) => if h : old t d x then k h.choose t else
        let j := publicRow T t d x
        let y := join (rates j) (caps j)
        if isolated t x y then k y (edge d x y::t) else 1) P

theorem mean_comm {U V : Type} [Fintype U] [Fintype V] (f : U → V → ℝ≥0∞) :
    uniformMean (fun u => uniformMean (f u)) = uniformMean (fun v => uniformMean (fun u => f u v)) := by
  unfold uniformMean; simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]

theorem mean_mono {U : Type} [Fintype U] {g h : U → ℝ≥0∞} (le : ∀ u, g u ≤ h u) : uniformMean g ≤ uniformMean h :=
  Finset.sum_le_sum fun u _ => mul_le_mul' le_rfl (le u)

theorem mean_add {U : Type} [Fintype U] (g h : U → ℝ≥0∞) :
    uniformMean (fun u => g u + h u) = uniformMean g + uniformMean h := by
  simp only [uniformMean,mul_add,Finset.sum_add_distrib]

theorem mean_hit {U : Type} [Fintype U] [DecidableEq U] (D : Finset U) :
    uniformMean (fun u => hit (u ∈ D)) = (D.card : ℝ≥0∞) / Fintype.card U := by
  unfold uniformMean hit unifW
  simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,
    Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]

def capLoss (Q : ℕ) : ℝ≥0∞ := ((2*Q+2 : ℕ) : ℝ≥0∞) / Fintype.card Capacity

theorem public_risk_aux (S : Sha2Set) (N T : ℕ) {Z : Type} (rates : Row T → Rate)
    (raw : ShakeApi.RawTable S N) (P : OracleComp (Outer S N) Z) (Q q : ℕ)
    (budget : CountBound (fun i => publicIdx (S := S) (N := N) i = true) P q) (QT : Q ≤ T)
    (seen : Finset (Row T)) (b : Bank (Row T) Capacity) (t : EdgeTrace Words)
    (links : ∀ j ∉ seen, b j = none) (good : History T t seen) (size : t.length+q ≤ Q) :
    uniformMean (fun H => publicBad S N T rates (fill b H) raw P t) ≤ q * capLoss Q := by
  induction P using OracleComp.inductionOn generalizing q seen b t with
  | pure => simp [publicBad,uniformMean]
  | query_bind i k ih =>
    rw [countBound_query_bind] at budget
    rcases i with n|⟨d,x⟩|x
    · change uniformMean (fun H => uniformMean (fun r => publicBad S N T rates (fill b H) raw (k r) t)) ≤ _
      rw [mean_comm]
      exact (mean_mono (fun r => ih r q (budget r) seen b t links good size)).trans_eq (avg_const _)
    · have pos := budget.1
      obtain ⟨q,rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt pos)
      have residual (y) := budget.2 y
      simp only [Nat.add_sub_cancel] at residual
      by_cases oldx : old t d x
      · change uniformMean (fun H => if h : old t d x then publicBad _ _ _ _ _ _ (k h.choose) t else _) ≤ _
        simp only [dite_eq_left oldx]
        exact (ih _ q (residual _) seen b t links good (by omega)).trans
          (mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ _)) le_rfl)
      · let j := publicRow T t d x
        have fresh := publicRow_new good (by omega) d x oldx
        rw [unfilled b j (links j fresh) (fun H => publicBad S N T rates H raw ((Outer S N).query (.inr (.inl (d,x))) >>= k) t)]
        let nxt (c : Capacity) := Function.update b j (some c)
        let D := forbidden wordSplit 0 t x
        let y (c : Capacity) := join (rates j) c
        have atj (c : Capacity) (h : Row T → Capacity) : fill (nxt c) h j = c := by simp [fill,nxt]
        have iso (c : Capacity) : isolated t x (y c) ↔ c ∉ D := by simp only [isolated,y,cap_join,D]
        calc
          _ ≤ uniformMean (fun c : Capacity => hit (c ∈ D) + q*capLoss Q) := by
            apply mean_mono
            intro c
            change uniformMean (fun H => if known : old t d x then _ else
              if isolated t x (y (fill (nxt c) H j)) then publicBad S N T rates (fill (nxt c) H) raw
                (k (y (fill (nxt c) H j))) (edge d x (y (fill (nxt c) H j))::t) else 1) ≤ _
            simp only [dite_eq_right oldx,atj,iso]
            by_cases bad : c ∈ D
            · simp [bad,hit,avg_const]
            · simp only [bad,not_false_eq_true,ite_true,hit,ite_false,zero_add]
              apply ih _ q (residual _) (insert j seen) (nxt c) _ _ (history_step good d x _ oldx ((iso c).mpr bad))
              · simp only [List.length_cons]; omega
              · intro u unused
                simp only [Finset.mem_insert,not_or] at unused
                exact (Function.update_of_ne unused.1 _ _).trans (links _ unused.2)
          _ = (D.card : ℝ≥0∞) / Fintype.card Capacity + q*capLoss Q := by rw [mean_add,mean_hit,avg_const]
          _ ≤ capLoss Q + q*capLoss Q := by
            apply add_le_add _ le_rfl
            apply mul_le_mul' _ le_rfl
            exact Nat.cast_le.mpr ((forbidden_card wordSplit 0 t x).trans (by omega))
          _ = _ := by rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm]
    · exact ih _ q (budget _) seen b t links good size

theorem public_risk (S : Sha2Set) (N T : ℕ) {Z : Type} (rates : Row T → Rate)
    (raw : ShakeApi.RawTable S N) (P : OracleComp (Outer S N) Z) (q : ℕ)
    (budget : CountBound (fun i => publicIdx (S := S) (N := N) i = true) P q) (h : q ≤ T) :
    uniformMean (fun H => publicBad S N T rates H raw P []) ≤ q * capLoss q :=
  public_risk_aux S N T rates raw P q q budget h ∅ (fun _ => none) [] (by simp) (emptyHistory T) (by simp)

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.public_risk
