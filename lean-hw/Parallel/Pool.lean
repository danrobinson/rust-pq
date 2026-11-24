import Std

namespace ParallelPool

/-- Model one exclusively owned dispatch. A worker moves from pending to
live after acquiring its publication, and leaves live when it decrements
the completion counter. A live worker may have stopped reading the job
but has not yet announced that it has finished. -/
inductive Run : List Nat → List Nat → Nat → Bool → List Nat → Prop
  | dispatch (n : Nat) : Run (List.range n) [] n false []
  | start {p q live n flag failures i} : Run (p ++ i :: q) live n flag failures →
      Run (p ++ q) (i :: live) n flag failures
  | finish {p q pending n flag failures i} : Run pending (p ++ i :: q) (n+1) flag failures →
      Run pending (p ++ q) n flag failures
  | panic {p q pending n flag failures i} : Run pending (p ++ i :: q) (n+1) flag failures →
      Run pending (p ++ q) n true (i :: failures)

theorem ledger {pending live n flag failures} (run : Run pending live n flag failures) :
    pending.length + live.length = n ∧ (flag = false ↔ failures = []) := by
  induction run with
  | dispatch => simp
  | start _ ih => simp_all [List.length_append]; omega
  | finish _ ih => simp_all [List.length_append]; omega
  | panic _ ih => simp_all [List.length_append]; omega

/-- The caller may clear its borrowed job after acquiring zero. At that
point every worker has finished, including any worker whose closure
unwound. A normally returning dispatch with the failure bit clear certifies
that none of the joined workers panicked. -/
theorem join {pending live flag failures} (run : Run pending live 0 flag failures) :
    pending = [] ∧ live = [] ∧ (flag = false ↔ failures = []) := by
  have h := ledger run
  exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega), h.2⟩

/-- Encoding used by Pool.remaining. The low bit is sticky during dispatch. -/
def encode (n : Nat) (failed : Bool) := 2*n + failed.toNat

theorem packed_join (n : Nat) (failed : Bool) :
    (encode n failed < 2 ↔ n = 0) ∧ (encode 0 failed = 1 ↔ failed = true) ∧
    encode (n+1) failed - 2 = encode n failed ∧
    (encode (n+1) failed < 4 ↔ n = 0) := by
  cases failed <;> simp [encode, Bool.toNat] <;> omega

end ParallelPool
