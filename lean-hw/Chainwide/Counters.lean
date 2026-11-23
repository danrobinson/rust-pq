import Chainwide.Input
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open ChainWideRust.core.core_arch.x86.avx512f

theorem lane_mask (pred : Fin 16 → Bool) (j : Fin 16) :
    (laneMask pred).bv.getLsbD j.val = pred j := by
  change ((BitVec.ofBoolListLE (List.ofFn pred)).cast (by simp) : BitVec 16).getLsbD j.val = _
  fin_cases j <;> simp [BitVec.getLsbD_cast]

/-- The two packed comparisons used to start and finish individual chains.
The start comparison is unsigned, including counters with their high bit set. -/
theorem start_mask (s e : Reg) :
    _mm512_cmplt_epu32_mask s e ⦃ m => ∀ j : Fin 16, m.bv.getLsbD j.val = decide ((s j).toNat < (e j).toNat) ⦄ := by
  simp only [_mm512_cmplt_epu32_mask,step_simps,lane_mask,implies_true]

theorem end_mask (s e : Reg) :
    _mm512_cmpeq_epi32_mask s e ⦃ m => ∀ j : Fin 16, m.bv.getLsbD j.val = (s j == e j) ⦄ := by
  simp only [_mm512_cmpeq_epi32_mask,step_simps,lane_mask,implies_true]

end slhdsa.X86.Chain
