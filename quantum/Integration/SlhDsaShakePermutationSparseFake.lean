import Integration.SlhDsaShakePermutationSparseTrace

/-! Hitting an independently sampled auxiliary target word during a bounded
classical forward-only run, including adaptively selected sponge inputs. -/
namespace Reduction.ShakePermutation.SparsePort.Trace
open Classical Classic OracleComp OracleSpec PQ.Interactive SetOracle ENNReal
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000
variable {J : Type} [Fintype J] [DecidableEq J]

def fake {A : Type} (u : J → A) (w : A) := ∃ j, u j = w

private theorem count_hit {A : Type} [Fintype A] (w : A) :
    Fintype.card {u : J → A // ∃ j, u j = w} * Fintype.card A ≤ Fintype.card J * Fintype.card (J → A) := by
  classical
  rw [← Fintype.card_prod,← Fintype.card_prod]
  let tag (u : {u : J → A // ∃ j, u j = w}) := u.property.choose
  let pack (p : {u : J → A // ∃ j, u j = w} × A) := (tag p.1,Function.update p.1.val (tag p.1) p.2)
  apply Fintype.card_le_of_injective pack
  rintro ⟨u,a⟩ ⟨v,b⟩ he
  have idx := congrArg Prod.fst he
  change tag u = tag v at idx
  have fn := congrArg Prod.snd he
  change Function.update u.val (tag u) a = Function.update v.val (tag v) b at fn
  rw [← idx] at fn
  apply Prod.ext _ (by simpa only [Function.update_self] using congrFun fn (tag u))
  apply Subtype.ext; funext j
  by_cases h : j = tag u
  · subst j
    have hU : u.val (tag u) = w := u.property.choose_spec
    have hV : v.val (tag v) = w := v.property.choose_spec
    exact hU.trans ((congrArg v.val idx).trans hV).symm
  · simpa only [Function.update_of_ne h] using congrFun fn j

def indicator (b : Prop) [Decidable b] : ℝ≥0∞ := if b then 1 else 0

private theorem mass {A : Type} [Fintype A] (P : A → Prop) [DecidablePred P] :
    uniformMean (fun a => indicator (P a)) = (Fintype.card {a // P a} : ℝ≥0∞) / Fintype.card A := by
  simp [uniformMean,indicator,unifW,Fintype.card_subtype,div_eq_mul_inv]

theorem single {A : Type} [Fintype A] [Nonempty A] (w : A) :
    uniformMean (fun u : J → A => indicator (fake u w)) ≤ (Fintype.card J : ℝ≥0∞) / Fintype.card A := by
  classical
  let B := Fintype.card {u : J → A // ∃ j, u j = w}
  let T := Fintype.card (J → A)
  have h : B*Fintype.card A ≤ Fintype.card J*T := count_hit w
  have hm : uniformMean (fun u : J → A => indicator (fake u w)) = (B : ℝ≥0∞)/T := by
    let V := {u : J → A // fake u w}
    have m := mass (fun u : J → A => fake u w)
    simp only [← Nat.card_eq_fintype_card] at m
    simpa only [B,T,← Nat.card_eq_fintype_card,fake] using m
  rw [hm]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast]
  rw [div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := J → A)) (by exact_mod_cast Fintype.card_pos (α := A))]
  exact_mod_cast h

private theorem swap {A B : Type} [Fintype A] [Fintype B] (f : A → B → ℝ≥0∞) :
    uniformMean (fun a => uniformMean (f a)) = uniformMean (fun b => uniformMean (fun a => f a b)) := by
  unfold uniformMean; simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]

private theorem ask {α : Type} (π : Permutation) (x : Words) (k : Words → OracleComp Fwd α)
    (pred : Words → Prop) [DecidablePred pred] :
    eager π (fun b => if b then 1 else 0) (monitor pred (Fwd.query (.inr x) >>= k)) =
      if pred (π x) then 1 else eager π (fun b => if b then 1 else 0) (monitor pred (k (π x))) := by
  change eager π _ (if pred (π x) then pure true else _) = _
  split <;> rfl

theorem fake_risk {α : Type} (π : Permutation) (p : OracleComp Fwd α) (Q : ℕ)
    (count : CountBound (fun i => i.isRight = true) p Q) :
    uniformMean (fun u : J → Words => eager π (fun b => if b then 1 else 0) (monitor (fake u) p)) ≤
      Q * ((Fintype.card J : ℝ≥0∞) / Fintype.card Words) := by
  classical
  let m := (Fintype.card J : ℝ≥0∞) / Fintype.card Words
  induction p using OracleComp.inductionOn generalizing Q with
  | pure => change uniformMean (fun _ : J → Words => 0) ≤ _; simp only [uniformMean,mul_zero,Finset.sum_const_zero,zero_le]
  | query_bind i k ih =>
    rw [countBound_query_bind] at count
    rcases i with n|x
    · change uniformMean (fun u : J → Words => uniformMean (fun r => eager π _ (monitor (fake u) (k r)))) ≤ _
      rw [swap]; exact ShakeXof.mean_le_const (fun r => ih r Q (count r))
    · have pos := count.1
      obtain ⟨q,rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt pos)
      have rest := count.2 (π x)
      simp only [Nat.add_sub_cancel] at rest
      let g (u : J → Words) := eager π (fun b => if b then 1 else 0) (monitor (fake u) (k (π x)))
      have each (u : J → Words) : eager π (fun b => if b then 1 else 0)
          (monitor (fake u) (Fwd.query (.inr x) >>= k)) ≤ g u + indicator (fake u (π x)) := by
        rw [ask]
        by_cases h : fake u (π x)
        · simp [h,indicator]
        · simp [h,indicator,g]
      have bound := Finset.sum_le_sum (s:=Finset.univ) (fun u _ => mul_le_mul' (le_refl (unifW _ u)) (each u))
      simp only [mul_add,Finset.sum_add_distrib] at bound
      rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      exact bound.trans (add_le_add (ih (π x) q rest) (single (J:=J) (π x)))

end
end Reduction.ShakePermutation.SparsePort.Trace
#print axioms Reduction.ShakePermutation.SparsePort.Trace.fake_risk
