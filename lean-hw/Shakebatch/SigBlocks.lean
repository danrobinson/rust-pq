import Shakebatch.WriteRows
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

def sigByte (sig : Buffer) (stride n t z b : Nat) : BitVec 8 := sig.val[t*stride+(z*n+b)]!.bv

theorem scattered_block {N : Usize} (rows : Rows N) (first stride z count : Nat) (s out : Buffer)
    (written : Scattered rows first stride (z*N.val) count s out)
    (t h b : Nat) (within : h*N.val+b < stride) (valid : t*stride+(h*N.val+b) < s.length)
    (byte : b < N.val) :
    sigByte out stride N.val t h b =
      if first ≤ t ∧ t < first+count ∧ z=h then rows.val[t-first]!.val[b]!.bv else sigByte s stride N.val t h b := by
  rw [sigByte,written.2 t _ within valid]
  by_cases tree : first ≤ t ∧ t < first+count
  · by_cases level : z=h
    · subst h
      simp [tree.1,tree.2,byte,show z*N.val+b-z*N.val=b by omega]
    · by_cases before : h < z
      · have lim := Nat.mul_le_mul_right N.val (show h+1 ≤ z by omega)
        rw [Nat.add_mul,Nat.one_mul] at lim
        simp [tree.1,tree.2,level,show ¬z*N.val ≤ h*N.val+b by omega,sigByte]
      · have lim := Nat.mul_le_mul_right N.val (show z+1 ≤ h by omega)
        rw [Nat.add_mul,Nat.one_mul] at lim
        simp [tree.1,tree.2,level,show ¬h*N.val+b < z*N.val+N.val by omega,sigByte]
  · by_cases firstOK : first ≤ t
    · simp [firstOK,show ¬t < first+count by omega,sigByte]
    · simp [firstOK,sigByte]

end slhdsa.ShakeBatch
