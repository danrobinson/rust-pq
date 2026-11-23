import Chainwrite.Funs
import Store256.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain

private theorem clear_low_bit (m i j : Nat) (set : m.testBit i = true)
    (low : ∀ k < i, m.testBit k = false) :
    (m &&& (m-1)).testBit j = (m.testBit j && decide (j ≠ i)) := by
  induction j generalizing i m with
  | zero =>
    rw [Nat.testBit_and]
    by_cases eq : i=0
    · subst i
      simp only [Nat.testBit_zero,decide_eq_true_eq] at set
      simp [Nat.testBit_zero,show (m-1)%2 ≠ 1 by omega]
    · have h := low 0 (by omega)
      simp [h]
  | succ j ih =>
    have positive : 0 < m := by by_contra! zero; simp [show m=0 by omega] at set
    cases i with
    | zero =>
      simp only [Nat.testBit_zero,decide_eq_true_eq] at set
      rw [Nat.testBit_and]
      simp [Nat.testBit_succ,show (m-1)/2 = m/2 by omega]
    | succ i =>
      have even := low 0 (by omega)
      simp only [Nat.testBit_zero,decide_eq_false_iff_not] at even
      have eq := ih (m/2) i (by rwa [← Nat.testBit_succ])
        (fun k hk => by rw [← Nat.testBit_succ]; exact low (k+1) (by omega))
      rw [Nat.testBit_and]
      simpa only [Nat.testBit_and,Nat.testBit_succ,show (m-1)/2 = m/2-1 by omega,
        Nat.succ_ne_succ_iff] using eq

theorem pop_bit (m : U16) (nz : m.bv ≠ 0) (j : Nat) :
    (m.bv &&& (m.bv-1)).getLsbD j = (m.bv.getLsbD j && decide (j ≠ m.bv.ctz.toNat)) := by
  have first := BitVec.getLsbD_true_ctz_of_ne_zero nz
  have positive : m.val ≠ 0 := by intro he; apply nz; apply BitVec.eq_of_toNat_eq; exact he
  have sub : (m.bv-1).toNat = m.val-1 := by
    rw [BitVec.toNat_sub_of_le (by change 1 ≤ m.val; omega)]
    rfl
  change (m.bv &&& (m.bv-1)).toNat.testBit j = _
  rw [BitVec.toNat_and,sub]
  change (m.val &&& (m.val-1)).testBit j = (m.val.testBit j && decide (j ≠ m.bv.ctz.toNat))
  exact
    clear_low_bit m.val m.bv.ctz.toNat j first (fun k hk => BitVec.getLsbD_false_of_lt_ctz hk)

end slhdsa.X86.Chain
