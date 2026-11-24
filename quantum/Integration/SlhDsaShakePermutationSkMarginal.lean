import Integration.SlhDsaShakePermutationSkFormat

namespace Reduction.ShakePermutation.SkFormat
open Classical MLink SLHDSA ENNReal SetOracle
open scoped ENNReal

private theorem key_row {K J B : Type} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype B] [Nonempty B]
    (k : K) (V : (J → B) → ℝ≥0∞) :
    uniformMean (fun W : K × J → B => V (fun j => W (k,j))) = uniformMean V := by
  classical
  let put (w : K × J → B) (g : J → B) (x : K × J) := if x.1 = k then g x.2 else w x
  let get (w : K × J → B) (j : J) := w (k,j)
  have written (w g) : get (put w g) = g := by funext j; simp [get,put]
  have inv : Function.Involutive (fun s : (K × J → B) × (J → B) => (put s.1 s.2,get s.1)) := by
    rintro ⟨w,g⟩
    apply Prod.ext _ (written w g)
    funext x
    rcases x with ⟨i,j⟩
    by_cases e : i=k <;> simp [put,get,e]
  have eq := SetOracle.avg_resample put get inv (fun w => V (get w))
  simpa only [uniformMean,written,← Finset.sum_mul,sum_unifW,one_mul] using eq

private theorem mean_pair {X Y : Type} [Fintype X] [Fintype Y] (v : X × Y → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (fun y => v (x,y))) = uniformMean v := by
  simp only [uniformMean,Fintype.sum_prod_type,unifW,Finset.mul_sum,Fintype.card_prod,Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),mul_assoc]

variable (S : Sha2Set) {J : Type}

def keyedWord (F : J → S.Node) (W : S.Node × J → Suffix S) (k : S.Node) (j : J) : Words :=
  (split S).symm (F j,W (k,j))

@[simp] theorem keyedWord_head (F : J → S.Node) (W : S.Node × J → Suffix S) (k : S.Node) (j : J) :
    ((split S) (keyedWord S F W k j)).1 = F j := by simp [keyedWord]

private theorem assemble {X Y Z K : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    [Fintype X] [Fintype Y] [Fintype Z] [Nonempty Z] (e : X ≃ Y × Z)
    (k : K) (v : (J → Y) → (J → X) → ℝ≥0∞) :
    uniformMean (fun f => uniformMean (fun w : K × J → Z => v f (fun j => e.symm (f j,w (k,j))))) =
      uniformMean (fun t : J → X => v (fun j => (e (t j)).1) t) := by
  classical
  let p := ((Equiv.arrowCongr (Equiv.refl J) e).trans
    (Equiv.arrowProdEquivProdArrow J (fun _ => Y) (fun _ => Z)))
  let test (fg : (J → Y) × (J → Z)) := v fg.1 (fun j => e.symm (fg.1 j,fg.2 j))
  have row (f : J → Y) : uniformMean (fun w : K × J → Z => v f (fun j => e.symm (f j,w (k,j)))) =
      uniformMean (fun g : J → Z => test (f,g)) := key_row k (fun g : J → Z => test (f,g))
  simp only [row]
  rw [mean_pair test]
  have eq := Equiv.sum_comp p.symm (fun t => unifW (J → X) t * v (fun j => (e (t j)).1) t)
  have all (fg) : (fun j => (e (p.symm fg j)).1) = fg.1 := by
    funext j
    change (e (e.symm (fg.1 j,fg.2 j))).1 = _
    rw [Equiv.apply_symm_apply]
  have inv (fg) : p.symm fg = fun j => e.symm (fg.1 j,fg.2 j) := rfl
  simpa only [uniformMean,unifW,Fintype.card_congr p, inv,Equiv.apply_symm_apply,test] using eq

/-- At any fixed secret key, the ideal n-byte PRF and independent suffixes
provide a full uniform permutation-output table. The test may use both
the ideal PRF itself and the assembled words. -/
theorem seed_marginal [Fintype J] [DecidableEq J] (k : S.Node) (v : (J → S.Node) → (J → Words) → ℝ≥0∞) :
    uniformMean (fun F => uniformMean (fun W => v F (keyedWord S F W k))) =
      uniformMean (fun T : J → Words => v (fun j => ((split S) (T j)).1) T) :=
  @assemble J Words S.Node (Suffix S) S.Node _ _ _ _ _ _ _ _ (split S) k v

end Reduction.ShakePermutation.SkFormat
#print axioms Reduction.ShakePermutation.SkFormat.seed_marginal
