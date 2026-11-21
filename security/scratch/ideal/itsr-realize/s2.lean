import Ideal.ComposeFinal
open SLHDSA
namespace Ideal.Realize.Itsr

theorem key9_of_type (a : Adrs) (h1 : a.type = 1 ∨ a.type = 4) :
    (SLHDSA.Concrete.sha2AdrsKey a)[9] ≠ 0 := by
  unfold SLHDSA.Concrete.sha2AdrsKey
  split
  · rename_i v hv
    unfold Adrs.compressSha2Checked at hv
    split_ifs at hv
    cases hv
    simp only [Vector.getElem_mk, List.getElem_toArray]
    rcases h1 with h | h <;>
    · simp only [Adrs.compressSha2, h]
      rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
        List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
      simp
      simp [Adrs.toBytesBE, toByte, VCVio.Algorithms.Encoding.natToBytesBE]
  · simp [SLHDSA.Concrete.sha2FallbackKey]
    rcases h1 with h | h <;> simp [h]

end Ideal.Realize.Itsr
