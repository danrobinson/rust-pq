import Integration.SlhDsaShakePermutationSparseFailure
import Integration.SlhDsaShakePermutationSparseModel
import Integration.SlhDsaShakeXofTcr

/-! Statistical replacement of a full family of one-block sponge outputs.
The single simulated public port is available coherently in both directions,
and is also the port used by other honest whole-sponge computations. -/
namespace Reduction.ShakePermutation.SparsePort
open Classical SetOracle ENNReal
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {J Y Z : Type} [Fintype J] [DecidableEq J] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [Fintype Z] [DecidableEq Z] [Nonempty Z]

private theorem const_mean {A : Type} [Fintype A] [Nonempty A] (c : ℝ≥0∞) :
    uniformMean (fun _ : A => c) = c := by simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]

private theorem rate {A : Type} [Fintype A] [Nonempty A] (P : A → Prop) [DecidablePred P]
    (n : ℕ) (h : Fintype.card {a // P a} * 2^n ≤ Fintype.card A) :
    uniformMean (fun a => if P a then 1 else 0) ≤ ((2:ℝ≥0∞)^n)⁻¹ := by
  have exact_mass : uniformMean (fun a => if P a then 1 else 0) =
      (Fintype.card {a // P a} : ℝ≥0∞) / (Fintype.card A) := by
    simp [uniformMean,unifW,Fintype.card_subtype,div_eq_mul_inv]
  rw [exact_mass]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
  rw [ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,← one_div,
    ENNReal.toReal_natCast,ENNReal.toReal_natCast,div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := A)) (by positivity),one_mul]
  exact_mod_cast h

variable (e : Words ≃ Y × Z) (a : J ↪ Words) (base : J)

abbrev Parts (J Y Z : Type) := (J → Y) × (J → Z)

def splitWorld : (J → Words) ≃ Parts J Y Z :=
  (Equiv.arrowCongr (Equiv.refl _) e).trans
    (Equiv.arrowProdEquivProdArrow J (fun _ => Y) (fun _ => Z))

private theorem split_mean (V : Parts J Y Z → ℝ≥0∞) :
    uniformMean (fun t : J → Words => V (splitWorld e t)) = uniformMean V := by
  let h := Equiv.sum_comp (splitWorld e (J := J)) (fun w => unifW _ w * V w)
  simpa only [uniformMean,unifW,Fintype.card_congr (splitWorld e (J := J))] using h

private theorem pair_mean (v : Parts J Y Z → ℝ≥0∞) :
    uniformMean v = uniformMean (fun f => uniformMean (fun s => v (f,s))) := by
  simp only [uniformMean,Fintype.sum_prod_type,unifW,Fintype.card_prod,Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    Finset.mul_sum,mul_assoc]

def exactTable (π : Permutation) (j : J) := (e (π (a j))).1

private theorem local_law (π : Permutation) (t : J → Words)
    (ok : Function.Injective (Program.pair a π t)) (sm : small (splitWorld e t).2) :
    let p := (Program.resample a (π,t)).1
    oracle p = simulatedPort e a π (splitWorld e t).2 base (splitWorld e t).1 ∧
      exactTable e a p = (splitWorld e t).1 := by
  have eq : target e (splitWorld e t).2 (splitWorld e t).1 = t :=
    funext fun j => e.symm_apply_apply (t j)
  have inj : Function.Injective (Program.pair a π (target e (splitWorld e t).2 (splitWorld e t).1)) := by rw [eq]; exact ok
  dsimp only
  simp only [Program.resample,dite_eq_left ok]
  constructor
  · funext p
    have match_ := eval_eq e a π _ sm (splitWorld e t).1 base inj p
    simpa only [simulatedPort,eq] using match_.symm
  · funext j
    have h := Program.exchange_hit (⟨_,ok⟩ : (Bool × J) ↪ Words) false j
    exact congrArg (fun x => (e x).1) h

private def warn (p : Prop) [Decidable p] : ℝ≥0∞ := if p then 1 else 0

private theorem fixed (π : Permutation) (jcap : Fintype.card J ≤ 2^768) (zcap : 2^1344 ≤ Fintype.card Z)
    (W : (Port → Words) → (J → Y) → ℝ≥0∞) (bounded : ∀ H f, W H f ≤ 1) :
    uniformMean (fun t : J → Words => let p := (Program.resample a (π,t)).1; W (oracle p) (exactTable e a p)) ≤
      uniformMean (fun f : J → Y => uniformMean (fun s : J → Z => W (simulatedPort e a π s base f) f)) +
      (((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹) := by
  classical
  let W' (w : Parts J Y Z) := W (simulatedPort e a π w.2 base w.1) w.1
  let conflict (t : J → Words) := ¬Function.Injective (Program.pair a π t)
  let crowd (w : Parts J Y Z) := ¬small w.2
  have local_bound (t : J → Words) :
      (let p := (Program.resample a (π,t)).1; W (oracle p) (exactTable e a p)) ≤
        W' (splitWorld e t) + (warn (conflict t) + warn (crowd (splitWorld e t))) := by
    by_cases c : conflict t
    · simp only [warn,ite_eq_left c]
      exact (bounded _ _).trans ((le_self_add.trans le_add_self))
    by_cases b : crowd (splitWorld e t)
    · simp only [warn,ite_eq_left b,ite_eq_right c,zero_add]
      exact (bounded _ _).trans le_add_self
    have ok : Function.Injective (Program.pair a π t) := not_not.mp c
    have sm : small (splitWorld e t).2 := not_not.mp b
    have h := local_law e a base π t ok sm
    simp only [h.1,h.2,W',warn,ite_eq_right b,ite_eq_right c,add_zero,le_refl]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun t _ => mul_le_mul' (le_refl (unifW _ t)) (local_bound t))
  apply h.trans
  simp only [mul_add,Finset.sum_add_distrib]
  change uniformMean (fun t => W' (splitWorld e t)) + (uniformMean (fun t => warn (conflict t)) +
    uniformMean (fun t => warn (crowd (splitWorld e t)))) ≤ _
  rw [split_mean, pair_mean W',split_mean e (fun w => warn (crowd w)),pair_mean (fun w => warn (crowd w))]
  apply add_le_add le_rfl
  apply add_le_add
  · apply rate
    have wordcard : Fintype.card Words = 2^1600 := by
      change Fintype.card (Fin 25 → UInt64) = _
      rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64,← pow_mul]
    have eq : conflict = fun t => ¬Function.Injective (labels (π ∘ a) t) := by
      funext t; unfold conflict
      apply congrArg (fun u : Bool × J → Words => ¬Function.Injective u)
      funext ⟨b,j⟩; cases b <;> rfl
    have hh := fail_nat (π ∘ a) (π.injective.comp a.injective) jcap wordcard
    rw [← eq] at hh
    simpa only [Nat.card_eq_fintype_card] using hh
  · rw [show (fun (_ : J → Y) => uniformMean (fun s : J → Z => warn (crowd (_,s)))) =
      (fun _ => uniformMean (fun s : J → Z => warn (¬small s))) from rfl,const_mean]
    exact rate _ _ (bucket_risk jcap zcap)

private theorem avg_shift {A : Type} [Fintype A] [Nonempty A] (f g : A → ℝ≥0∞) (u : ℝ≥0∞)
    (h : ∀ a, f a ≤ g a + u) : uniformMean f ≤ uniformMean g + u := by
  have le := Finset.sum_le_sum (s := Finset.univ) (fun a _ => mul_le_mul' (le_refl (unifW _ a)) (h a))
  exact le.trans_eq (by simp only [uniformMean,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,sum_unifW,one_mul])

private theorem mean_instance {A : Type} {i j : Fintype A} (f : A → ℝ≥0∞) :
    @uniformMean A i f = @uniformMean A j f := congrArg (fun k => @uniformMean A k f) (Subsingleton.elim i j)

/-- Unrestricted coherent access to the shared forward and inverse permutation
can be replaced by a three-cell public port and an independent table of
formatted-row outputs, with the two explicit statistical penalties. -/
theorem transfer (jcap : Fintype.card J ≤ 2^768) (zcap : 2^1344 ≤ Fintype.card Z)
    (W : (Port → Words) → (J → Y) → ℝ≥0∞) (bounded : ∀ H f, W H f ≤ 1) :
    uniformMean (fun π : Permutation => W (oracle π) (exactTable e a π)) ≤
      uniformMean (fun π : Permutation => uniformMean (fun f : J → Y =>
        uniformMean (fun s : J → Z => W (simulatedPort e a π s base f) f))) +
        (((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹) := by
  let V (π : Permutation) (_ : J → Words) := W (oracle π) (exactTable e a π)
  have h := Program.resample_law a V
  simp only [V,const_mean] at h
  apply h.le.trans
  let score (π : Permutation) := uniformMean (fun t : J → Words => let p := (Program.resample a (π,t)).1; W (oracle p) (exactTable e a p))
  have same : uniformMean (fun π : Permutation => @uniformMean (J → Words) (@Pi.instFintype J (fun _ => Words) (fun x y => Classical.propDecidable (x = y)) _ (fun _ => inferInstance)) (fun t => let p := (Program.resample a (π,t)).1; W (oracle p) (exactTable e a p))) = uniformMean score := congrArg uniformMean (funext (fun (π : Permutation) => mean_instance (fun t : J → Words => let p := (Program.resample a (π,t)).1; W (oracle p) (exactTable e a p))))
  apply same.le.trans
  exact avg_shift (A := Permutation) (fun π => uniformMean (fun t : J → Words => let p := (Program.resample a (π,t)).1; W (oracle p) (exactTable e a p)))
    (fun π => uniformMean (fun f : J → Y => uniformMean (fun s : J → Z => W (simulatedPort e a π s base f) f)))
    _ (fun π => fixed e a base π jcap zcap W bounded)

end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.transfer
