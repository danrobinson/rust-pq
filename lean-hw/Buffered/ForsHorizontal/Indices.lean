import Buffered.ForsHorizontal.Program
import Buffered.Transfer
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsHorizontal
open ShakeBatch
open Buffered
set_option maxHeartbeats 850000

theorem init_indices (idx : U32) (z : Usize) (initial : Array U32 16#usize)
    (height : z.val≤14) (room : (idx.val+1)*2^z.val≤1048576) :
    subtree_loop0 ⟨0#usize,z,false⟩ idx z initial ⦃ out => ∀ j≤z.val,
      out.val[j]!.val=idx.val*2^(z.val-j) ⦄ := by
  let progress (it : core.ops.range.RangeInclusive Usize) := if it.exhausted then z.val+1 else it.start.val
  unfold subtree_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.RangeInclusive Usize × Array U32 16#usize => z.val+1-progress q.1)
    (inv := fun q => q.1.«end»=z ∧ q.1.start.val≤z.val ∧ ∀ j<progress q.1, q.2.val[j]!.val=idx.val*2^(z.val-j))
  · rintro ⟨it,current⟩ ⟨last,le,prior⟩
    simp only at last le prior ⊢
    unfold subtree_loop0.body
    step as ⟨opt,next,iteration⟩
    by_cases stopped : it.exhausted=true
    · simp [stopped] at iteration
      simp only [iteration.1,step_simps]
      intro j hj
      exact prior j (by simp [progress,stopped]; omega)
    · have live : it.exhausted=false := by simpa using stopped
      have valid : ¬ (it.«end».val < it.start.val) := by rw [last]; omega
      simp only [live,Bool.false_eq_true,false_or,if_neg valid] at iteration
      have item : opt=some it.start := by split at iteration <;> exact iteration.1
      simp only [item]
      step as ⟨shift,shiftVal⟩
      step as ⟨word,wordVal⟩
      step as ⟨out,store⟩
      have less : idx.val*2^shift.val<U32.size := by
        have pow := Nat.pow_le_pow_right (by decide : 0<2) (show shift.val≤z.val by omega)
        have limit : idx.val * 2^shift.val ≤ 1048576 := ((Nat.mul_le_mul_left idx.val pow).trans (Nat.mul_le_mul_right (2^z.val) (Nat.le_succ idx.val))).trans room
        exact limit.trans_lt (by scalar_tac : 1048576 < U32.size)
      have wordEq : word.val=idx.val*2^(z.val-it.start.val) := by
        rw [wordVal,Nat.shiftLeft_eq,Nat.mod_eq_of_lt less,shiftVal]
      have endEq : it.«end».val=z.val := congrArg UScalar.val last
      have inc : progress next=it.start.val+1 := by
        split at iteration
        · simp [progress,iteration.2.2.2,iteration.2.1]
        · simp [progress,iteration.2.2.2]; omega
      have prev : progress it=it.start.val := by simp [progress,live]
      have last' : next.«end»=z := by split at iteration <;> exact iteration.2.2.1.trans last
      have le' : next.start.val≤z.val := by
        split at iteration
        · rw [iteration.2.1]; omega
        · rw [iteration.2.1]; exact le
      refine ⟨last',le',?_,by rw [inc,prev]; omega⟩
      intro j hj
      rw [store,Array.set_val_eq]
      by_cases same : j=it.start.val
      · subst j; rw [setSame _ _ _ (by simp; omega)]; exact wordEq
      · rw [setOther _ _ _ _ (Ne.symm same)]
        exact prior j (by omega)
  · exact ⟨rfl,by change 0≤z.val; omega,by intro j hj; change j<0 at hj; omega⟩

end slhdsa.ForsHorizontal
