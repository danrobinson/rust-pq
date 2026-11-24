import Integration.SlhDsaShakePermutationShear
import Integration.SlhDsaShakePermutationPortMatrix

/-! Programming one h value in the full two-way permutation port. The bound
averaged over a hidden row requires one fixed incoming state for all choices
of that row. Both directions may be queried coherently. -/
namespace Reduction.ShakePermutation.Hidden
open Classical Quantum
set_option maxRecDepth 8192

def addressed (π : Permutation) (ki ko : Mask) (p : Port) : Capacity :=
  if p.1 then capOf p.2 else capOf (mask ko (π (mask ki p.2)))

theorem oracle_agrees (π : Permutation) (ki ko : Mask) (h g : RateMask) (p : Port)
    (agree : h (addressed π ki ko p) = g (addressed π ki ko p)) :
    oracle (salted ki ko h π) p = oracle (salted ki ko g π) p := by
  rcases p with ⟨d,w⟩
  cases d <;> simp only [addressed,Bool.false_eq_true,ite_false,ite_true] at agree <;>
    simp only [oracle_salted,Bool.false_eq_true,ite_false,ite_true,shear,agree]

/-- Amplitudes after the public additive query on a fixed input-address
fiber. Spectator and response amplitudes may be arbitrarily entangled. -/
def after {E : Type} (π : Permutation) (ψ : Port → Words × E → ℂ) (p : Port) (w : Words × E) : ℂ :=
  ψ p (w.1 - oracle π p,w.2)

theorem fibers {E : Type} [Fintype E] (π : Permutation) (ψ : Port → Words × E → ℂ) (p : Port) :
    ∑ w, ‖after π ψ p w‖^2 = ∑ w, ‖ψ p w‖^2 := by
  let e : Equiv.Perm (Words × E) := (Equiv.subRight (oracle π p)).prodCongr (Equiv.refl E)
  exact Equiv.sum_comp e (fun w => ‖ψ p w‖^2)

theorem sq_diff (a b : ℂ) : ‖a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := norm_sub_le a b
  have hh : ‖a-b‖^2 ≤ (‖a‖+‖b‖)^2 := by gcongr
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

/-- Sum of squared errors over all independently chosen hidden locations.
Dividing by the number of capacity values gives the mean one-query loss. -/
theorem all_rows {E : Type} [Fintype E] (π : Permutation) (ki ko : Mask) (h : RateMask)
    (program : Capacity → RateMask) (outside : ∀ c z, z ≠ c → program c z = h z)
    (ψ : Port → Words × E → ℂ) :
    ∑ c, ∑ p, ∑ w, ‖after (salted ki ko (program c) π) ψ p w - after (salted ki ko h π) ψ p w‖^2 ≤
      4 * ∑ p, ∑ w, ‖ψ p w‖^2 := by
  classical
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  rw [Finset.sum_eq_single (addressed π ki ko p)]
  · calc
      _ ≤ ∑ w, 2*(‖after (salted ki ko (program (addressed π ki ko p)) π) ψ p w‖^2 +
          ‖after (salted ki ko h π) ψ p w‖^2) := Finset.sum_le_sum fun w _ => sq_diff _ _
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib,fibers,fibers]; ring
  · intro c _ other
    have eq := oracle_agrees π ki ko (program c) h p (outside c _ (Ne.symm other))
    simp only [after,eq,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
  · simp

end Reduction.ShakePermutation.Hidden
#print axioms Reduction.ShakePermutation.Hidden.all_rows
