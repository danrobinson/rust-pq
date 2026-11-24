import Shakebatch.Seed
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

/-- State words are stored by Keccak coordinate, and then by independent input. -/
def lane (s : Matrix machine.width) (j : Nat) : Spec.Keccak.State :=
  _root_.Array.ofFn fun i : Fin 25 => cell s i.val j

/-- The one hardware-facing contract used by all batched short-input tree hashes. -/
def PermutationCorrect : Prop := ∀ s : Matrix machine.width,
  machine.permute s ⦃ out => ∀ j < machine.width.val, lane out j=Spec.Keccak.permute (lane s j) ⦄

omit machine in
theorem le_byte (w : U64) (b : Nat) (bound : b < 8) :
    (core.num.U64.to_le_bytes w).val[b]!.bv = (w.bv >>> (8*b)).truncate 8 := by
  have conv : (core.num.U64.to_le_bytes w).val = w.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8) := by
    unfold core.num.U64.to_le_bytes
    rw [Array.from_val]
  rw [conv,getElem!_pos _ b (by simp [bound]),List.getElem_map]
  ext k hk
  have bit := BitVec.toLEBytes_getElem_testBit w.bv b k (by simp; omega) ⟨hk,by omega⟩
  simpa only [BitVec.getElem_eq_testBit_toNat,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,
    Nat.testBit_mod_two_pow,decide_true,BitVec.toNat_ofNat,Nat.testBit_shiftRight,hk,Bool.true_and] using bit

end slhdsa.ShakeBatch
