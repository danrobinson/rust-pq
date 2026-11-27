import Parallel.WorkerInterleave

open Aeneas Aeneas.Std Result ParallelWorkerInterleave
namespace ParallelWorkerScalarLow

def sibling (t a j digit : Nat) := t * 2^(a-j) + ((digit / 2^j) ^^^ 1)

/-- The exact checked scalar arithmetic in the worker's authentication loop. -/
def index (digit a t j : U32) : Result U32 := do
  let q ← digit >>> j
  let flip ← lift (q ^^^ 1#u32)
  let shift ← a - j
  let base ← t <<< shift
  base + flip

theorem index_spec (digit a t j : U32) (height : a.val < 32) (below : j.val ≤ a.val)
    (fits : sibling t.val a.val j.val digit.val ≤ U32.max) :
    index digit a t j ⦃ v => v.val = sibling t.val a.val j.val digit.val ⦄ := by
  unfold index
  step as ⟨q, qv, _⟩
  simp only [lift,bind_ok]
  have flip : (q ^^^ 1#u32).val = (digit.val / 2^j.val) ^^^ 1 := by
    simp [UScalar.val_xor,qv,Nat.shiftRight_eq_div_pow]
  step as ⟨shift, sv⟩
  step as ⟨base, bv, _⟩
  have offset : base.val = t.val * 2^(a.val-j.val) := by
    rw [bv, Nat.shiftLeft_eq, sv, Nat.mod_eq_of_lt]
    simp only [sibling,U32.max_eq] at fits
    rw [U32.size_eq]
    omega
  step as ⟨val, eq⟩
  all_goals first | (rw [eq,offset,flip]; rfl) | (rw [offset,flip]; exact fits)

private theorem bind_success {A B : Type} (x : Result A) (f : A → Result B) (y : B)
    (h : (x >>= f) = ok y) : ∃ z, x = ok z ∧ f z = ok y := by
  cases x with
  | ret z => exact ⟨z,rfl,by simpa only [bind_tc_ok] using h⟩
  | div => simp [bind_tc_eq] at h
  | vis eff k =>
    cases eff with
    | fail e =>
      have eq : k = PEmpty.elim := funext (fun v => nomatch v)
      subst k
      change (Result.fail e >>= f) = ok y at h
      simp [bind_tc_eq] at h

theorem intermediate (digit a t j result : U32) (correct : index digit a t j = ok result) :
    ∃ q shift base : U32, digit >>> j = ok q ∧ a-j = ok shift ∧ t <<< shift = ok base ∧
      base + (q ^^^ 1#u32) = ok result := by
  unfold index at correct
  obtain ⟨q,getQ,next⟩ := bind_success _ _ _ correct
  simp only [lift,bind_ok] at next
  obtain ⟨shift,getShift,next⟩ := bind_success _ _ _ next
  obtain ⟨base,getBase,finish⟩ := bind_success _ _ _ next
  exact ⟨q,shift,base,getQ,getShift,getBase,finish⟩

def secretIndex (t a digit : U32) : Result U32 := do
  let base ← t <<< a
  base + digit

theorem secret_index_spec (t a digit : U32) (height : a.val < 32)
    (fits : t.val * 2^a.val + digit.val ≤ U32.max) :
    secretIndex t a digit ⦃ v => v.val = t.val * 2^a.val + digit.val ⦄ := by
  unfold secretIndex
  step as ⟨base,bv,_⟩
  have pos : base.val = t.val * 2^a.val := by
    rw [bv,Nat.shiftLeft_eq,Nat.mod_eq_of_lt]
    rw [U32.max_eq] at fits
    rw [U32.size_eq]
    omega
  step as ⟨idx,iv⟩
  rw [iv,pos]

theorem secret_intermediate (t a digit result : U32) (correct : secretIndex t a digit = ok result) :
    ∃ base : U32, t <<< a = ok base ∧ base+digit = ok result := bind_success _ _ _ correct

end ParallelWorkerScalarLow
