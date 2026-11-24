import Integration.SlhDsaShakePermutationPrfTargets
import Integration.SlhDsaShakePermutationSkFormat
import Integration.SlhDsaShakePermutationResample

/-! Distinct simultaneous permutation transpositions at all formatted SK.PRF
inputs. Suffix randomness is independent for each (key, public seed, address);
the target's SHAKE prefix is shared across keys at the same public row. -/
namespace Reduction.ShakePermutation.SkFormat
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Classical MLink SLHDSA ENNReal PrfTargets
variable (S : Sha2Set)

abbrev PublicRow := S.Node × Bytes 32
abbrev Targets := World S.Node (PublicRow S) S.Node (Suffix S)

def target (w : Targets S) (r : SkFormat.Row S) : Words := (split S).symm (val w r)

@[simp] theorem split_target (w : Targets S) (r : SkFormat.Row S) :
    split S (target S w r) = (w.1 r.2,w.2 r) := (split S).apply_symm_apply _

private theorem failure_iff (π : Permutation) (w : Targets S) :
    ¬Function.Injective (Program.pair (input S) π (target S w)) ↔
      Bad (fun r => split S (π (input S r))) w := by
  classical
  constructor
  · intro hn
    by_contra h
    apply hn
    have hi : Function.Injective (val w) := Classical.byContradiction (fun ne => h (Or.inl ne))
    have disj (r t : SkFormat.Row S) : val w r ≠ split S (π (input S t)) := fun eq => h (Or.inr ⟨r,t,eq⟩)
    rintro ⟨d,r⟩ ⟨e,t⟩ eq
    cases d <;> cases e
    · exact Prod.ext rfl ((input S).injective (π.injective eq))
    · exact False.elim (disj t r ((split S).symm_apply_eq.mp eq.symm))
    · exact False.elim (disj r t ((split S).symm_apply_eq.mp eq))
    · exact Prod.ext rfl (hi ((split S).symm.injective eq))
  · rintro (ne|⟨r,t,eq⟩) hi
    · apply ne
      intro r t eq
      exact congrArg Prod.snd (hi (a₁:=(true,r)) (a₂:=(true,t)) (congrArg (split S).symm eq))
    · have he := hi (a₁:=(true,r)) (a₂:=(false,t)) ((split S).symm_apply_eq.mpr eq)
      cases he

/-- Uniform full replacement tables yield pairwise-distinct old and new images
except with probability strictly below 2⁻⁵⁵, for each fixed base permutation. -/
theorem target_failure (π : Permutation) :
    SetOracle.uniformMean (fun w : Targets S =>
      if Function.Injective (Program.pair (input S) π (target S w)) then 0 else 1) <
      ((2:ℝ≥0∞)^55)⁻¹ := by
  have keys : Fintype.card S.Node ≤ 2^256 := by
    change Fintype.card (Bytes _) ≤ _
    rw [card_bytes']; cases S <;> decide +kernel
  have rows : Fintype.card (PublicRow S) ≤ 2^512 := by
    change Fintype.card (S.Node × Bytes 32) ≤ _
    rw [Fintype.card_prod,card_bytes' 32]
    exact (Nat.mul_le_mul_right (256^32) keys).trans (by decide +kernel)
  have words : Fintype.card (S.Node × Suffix S) = 2^1600 := by
    rw [← Fintype.card_congr (split S)]
    change Fintype.card (Fin 25 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  have prob := benchmark_mean (fun r => split S (π (input S r))) keys rows keys words
  convert! prob using 2
  funext w
  by_cases hi : Function.Injective (Program.pair (input S) π (target S w))
  · simp [hi, ← failure_iff]
  · simp [hi, ← failure_iff]

end Reduction.ShakePermutation.SkFormat
#print axioms Reduction.ShakePermutation.SkFormat.target_failure
