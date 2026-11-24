import Integration.SlhDsaShakePermutationClassicalDriver

namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp Classical SLHDSA MLink
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def visible (T : ℕ) (H : Row T → Words) (t : EdgeTrace Words) (d : Bool) (x : Words) :
    Words × EdgeTrace Words :=
  if h : old t d x then (h.choose,t) else
    let y := H (publicRow T t d x)
    (y,edge d x y::t)

/-- Each honest XOF query reads only its padded input's rate row. Its
message, prefixes and inner capacities are absent from the public log. -/
def idealOuter (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words)
    (raw : ShakeApi.RawTable S N) (ev : Z → ℝ≥0∞) (P : OracleComp (Outer S N) Z) :
    EdgeTrace Words → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => EdgeTrace Words → ℝ≥0∞) (fun z _ => ev z)
    (fun i _ k t => match i with
      | .inl _ => uniformMean fun r => k r t
      | .inr (.inl (d,x)) => let z := visible T H t d x; k z.1 z.2
      | .inr (.inr x) => k (raw x) t) P

def rawOf (S : Sha2Set) {N T : ℕ} (cap : Completion.blockCap N ≤ T) (H : Row T → Words) : ShakeApi.RawTable S N :=
  fun x => ShakeXof.head (output_sizes S).2 (Completion.bytes (rateOf (H (.inl (Completion.address cap x)))))

theorem driver_ideal (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T)
    {Z : Type} (H : Row T → Words) (ev : Z → ℝ≥0∞) (P : OracleComp (Outer S N) Z) (t : EdgeTrace Words) :
    labelled (fun j _ _ => H j) ev (driver S N T P t) =
      idealOuter S N T H (rawOf S cap H) ev P t := by
  induction P using OracleComp.inductionOn generalizing t with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩|x
    · change labelled _ _ (_ >>= _) = _
      rw [labelled_bind]
      exact congrArg uniformMean (funext fun r => ih r t)
    · change labelled _ _ (publicStep T t d x >>= _) = _
      rw [labelled_bind,publicStep]
      change _ = idealOuter _ _ _ _ _ _ (k (visible T H t d x).1) (visible T H t d x).2
      unfold visible
      split
      · exact ih _ _
      · rw [labelled_bind]
        exact ih _ _
    · change labelled _ _ (absorb T [] 0 _ >>= _) = _
      rw [labelled_bind]
      change labelled _ _ (absorb T [] (bankState T H []) _) = _
      rw [absorb_ideal,List.nil_append]
      let p := messageBlocks (sp (List.ofFn x.2))
      have len : p.length ≤ T := by
        change (messageBlocks _).length ≤ T; rw [messageBlocks_length]
        apply le_trans _ cap
        simp only [sp,List.length_map,List.length_ofFn,Completion.blockCap]
        exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.le_of_lt_succ x.1.isLt)) _
      have pos : 0 < p.length := by simp [p,messageBlocks_length]
      have e : bankState T H p = H (.inl (Completion.address cap x)) := by
        simp only [bankState,List.isEmpty_iff_length_eq_zero,Nat.ne_of_gt pos,ite_false,rowId,dite_eq_left len]
        rfl
      change labelled _ _ (driver S N T (k (ShakeXof.head (output_sizes S).2 (Completion.bytes (rateOf (bankState T H p))))) t) = _
      rw [e]; exact ih _ t

def banks (T : ℕ) (rates : Fix.Table T) (caps : Fix.Domain T → Capacity) (outside : Port → Words) : Row T → Words :=
  Sum.elim (fun p => join (rates p) (caps p)) outside

def banksEquiv (T : ℕ) : (Fix.Table T × (Fix.Domain T → Capacity) × (Port → Words)) ≃ (Row T → Words) where
  toFun z := banks T z.1 z.2.1 z.2.2
  invFun H := ((fun p => rateOf (H (.inl p))),(fun p => capOf (H (.inl p))),fun x => H (.inr x))
  left_inv z := by rcases z with ⟨r,k,u⟩; simp [banks]
  right_inv H := by funext i; cases i <;> simp [banks]

theorem mean_prod {A B : Type} [Fintype A] [Fintype B] (f : A × B → ℝ≥0∞) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  have inv := @ENNReal.mul_inv (Fintype.card A : ℝ≥0∞) (Fintype.card B : ℝ≥0∞) (by simp) (by simp)
  simp only [uniformMean,Fintype.sum_prod_type,Finset.mul_sum,unifW,Fintype.card_prod,Nat.cast_mul,
    inv,mul_assoc]

private theorem mean_triple {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (e : A × B × C ≃ D) (f : D → ℝ≥0∞) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => uniformMean (fun c => f (e (a,b,c))))) := by
  let g := fun z => f (e z)
  have w : uniformMean f = uniformMean g := (mean_equiv e f).symm
  refine w.trans ((mean_prod g).trans ?_)
  exact congrArg uniformMean (funext fun a => mean_prod (fun z => g (a,z)))

theorem ideal_completion (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T)
    {Z : Type} (ev : Z → ℝ≥0∞) (P : OracleComp (Outer S N) Z) :
    uniformMean (fun H : Row T → Words => labelled (fun j _ _ => H j) ev (driver S N T P [])) =
      uniformMean (fun g : Completion.Private T => uniformMean (fun raw : ShakeApi.RawTable S N =>
        uniformMean (fun k : Fix.Domain T → Capacity => uniformMean (fun u : Port → Words =>
          idealOuter S N T (banks T (Completion.complete S cap g raw) k u) raw ev P [])))) := by
  let test := fun H : Row T → Words => labelled (fun j _ _ => H j) ev (driver S N T P [])
  let score := fun r : Fix.Table T => uniformMean (fun k : Fix.Domain T → Capacity =>
    uniformMean (fun u : Port → Words => test (banks T r k u)))
  refine (mean_triple (banksEquiv T) test).trans ?_
  refine (Completion.uniform_complete S cap (output_sizes S).2 score).trans ?_
  apply congrArg uniformMean; funext g
  apply congrArg uniformMean; funext raw
  apply congrArg uniformMean; funext k
  apply congrArg uniformMean; funext u
  let H := banks T (Completion.complete S cap g raw) k u
  have e : rawOf S cap H = raw := funext fun x => by
    change ShakeXof.head _ (Completion.bytes (rateOf (join _ _))) = _
    rw [rate_join]
    exact Completion.prefix_complete S cap g raw x (output_sizes S).2
  exact (driver_ideal S N T cap H ev P []).trans
    (congrArg (fun f => idealOuter S N T H f ev P []) e)

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.ideal_completion
