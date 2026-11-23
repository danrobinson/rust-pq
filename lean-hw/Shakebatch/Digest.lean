import Shakebatch.Lanes
import Shakebatch.Read
import Shakebatch.Oneblock
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem read_digest (N : Usize) (s : Matrix machine.width) (bound : N.val ≤ 136) (align : N.val%8=0) :
    shake.batch.read N s ⦃ out => ∀ j < machine.width.val,
      bytes out.val[j]!.val = Spec.Keccak.squeeze (lane s j) 0 N.val ⦄ := by
  apply WP.spec_mono (read_spec N s bound align)
  intro out cells j hj
  rw [Spec.Keccak.squeeze_short _ _ _ (by omega)]
  apply List.ext_getElem
  · simp [bytes]
  · intro b hl hr
    have bn : b < N.val := by simpa [bytes] using hl
    have ks : b/8 < 25 := by omega
    simp only [bytes,List.getElem_map,List.getElem_range,Nat.zero_add]
    rw [← getElem!_pos]
    change (outputByte out j b).bv = _
    rw [cells j hj b bn,stateByte,le_byte _ _ (by omega)]
    simp only [Spec.Keccak.extractByte,lane,Spec.Keccak.ofFnAt _ _ ks,cell]
end slhdsa.ShakeBatch
