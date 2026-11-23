import Slhdsa.Proofs.Fors
open Nat
namespace slhdsa.ShakeBatch

/-- The global FORS sibling flips the low index bit within its own tree. -/
theorem sibling_eq (tree idx a j : Nat) (less : j < a) :
    ((tree * 2^a + idx) / 2^j) ^^^ 1 = tree*2^(a-j) + ((idx/2^j) ^^^ 1) := by
  have mult : tree*2^a=tree*2^(a-j)*2^j := by rw [Nat.mul_assoc,← pow_add,show a-j+j=a by omega]
  rw [mult,Nat.mul_comm (tree*2^(a-j)) (2^j),Nat.mul_add_div (by positivity : 0 < 2^j)]
  have e : Even (tree*2^(a-j)) := by
    refine ⟨tree*2^(a-j-1),?_⟩
    conv => lhs; rw [show a-j=a-j-1+1 by omega,pow_succ]
    ring
  rcases Nat.even_or_odd (idx/2^j) with he|ho
  · rw [Nat.xor_one_of_even (e.add he),Nat.xor_one_of_even he,Nat.add_assoc]
  · rw [Nat.xor_one_of_odd (e.add_odd ho),Nat.xor_one_of_odd ho]
    have nonzero := ho.pos
    omega
end slhdsa.ShakeBatch
