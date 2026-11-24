import Integration.SlhDsaShakePermutationFixMachine
import Integration.SlhDsaBridgeMsg

namespace Reduction.ShakePermutation.Fix.Machine
open Quantum PQ.Interactive OracleSpec OracleComp Classical
variable {T : ℕ} {X Y U α ι : Type} {sp : OracleSpec ι}
variable [Fintype X] [Fintype Y] [Fintype U] [DecidableEq X] [DecidableEq Y] [DecidableEq U] [AddCommGroup Y]
variable (A : Access X Y) (L : ℕ) (base : X)

@[reducible] def mark {I J : Type} (read : Bool) (classicalCost : ι → Bool) : I ⊕ (J ⊕ ι) → Bool
  | .inl _ => false
  | .inr (.inl _) => read
  | .inr (.inr i) => classicalCost i

@[simp] theorem mark_local {I J : Type} (r : Bool) (c : ι → Bool) (j : I) :
    mark (J := J) r c (.inl j) = false := rfl
@[simp] theorem mark_read {I J : Type} (r : Bool) (c : ι → Bool) (j : J) :
    mark (I := I) r c (.inr (.inl j)) = r := rfl
@[simp] theorem mark_class {I J : Type} (r : Bool) (c : ι → Bool) (i : ι) :
    mark (I := I) (J := J) r c (.inr (.inr i)) = c i := rfl

def allowed {I J : Type} (ok : ι → Prop) : I ⊕ (J ⊕ ι) → Prop
  | .inl _ | .inr (.inl _) => True
  | .inr (.inr i) => ok i

theorem count_mono {κ β : Type} {os : OracleSpec κ} (p : κ → Prop) [DecidablePred p]
    (P : OracleComp os β) {a b : ℕ} (hab : a ≤ b) (h : CountBound p P a) : CountBound p P b := by
  induction P using OracleComp.inductionOn generalizing a b with
  | pure => trivial
  | query_bind t k ih =>
    rw [countBound_query_bind] at h ⊢
    split at h
    · rename_i yes
      rw [ite_eq_left yes]
      exact ⟨by omega,fun r => ih r (by omega) (h.2 r)⟩
    · rename_i no
      rw [ite_eq_right no]
      exact fun r => ih r hab (h r)

omit [AddCommGroup Y] in
private theorem circuit_count {Z : Type} [Fintype Z] [DecidableEq Z]
    (c : Circuit X Y Z) (read : Bool) (cc : ι → Bool) (k : QOC (Register X Y Z) (portSpec + sp) α)
    (q : ℕ) (hk : CountBound (fun i => mark read cc i = true) k q) :
    CountBound (fun i => mark read cc i = true) (c.program k) ((if read then c.cost else 0)+q) := by
  induction c generalizing k q with
  | localOp => rw [Circuit.program,countBound_query_bind]; simpa [Circuit.cost] using hk
  | port => rw [Circuit.program,countBound_query_bind]; cases read <;> simp [Circuit.cost,hk]
  | seq a b ha hb =>
    have h := ha _ _ (hb k q hk)
    cases read <;> simpa [Circuit.program,Circuit.cost,Nat.add_assoc] using h

omit [AddCommGroup Y] in
private theorem circuit_cap {Z : Type} [Fintype Z] [DecidableEq Z]
    (c : Circuit X Y Z) (ok : ι → Prop) (out : α → Prop) (k : QOC (Register X Y Z) (portSpec + sp) α)
    (hk : AllQueries (allowed ok) out k) : AllQueries (allowed ok) out (c.program k) := by
  induction c generalizing k with
  | localOp => exact ⟨trivial,fun _ => hk⟩
  | port => exact ⟨trivial,fun _ => hk⟩
  | seq a b ha hb => exact ha _ (hb k hk)

omit [DecidableEq U] in
/-- Public reads cost at most 8L+4 raw queries each. The same translation
preserves the number of signing requests exactly. -/
theorem raw_count (read : Bool) (cc : ι → Bool) (p : Source U T sp α) (q : ℕ)
    (h : CountBound (fun i => mark read cc i = true) p q) :
    CountBound (fun i => mark read cc i = true) (raw A L base p) ((if read then 8*L+4 else 1)*q) := by
  unfold raw
  let b := if read then 8*L+4 else 1
  have hb : 1 ≤ b := by cases read <;> simp [b]
  have add (n : ℕ) (hn : 0 < n) : b*(n-1)+b = b*n := by
    rw [← Nat.mul_succ]; congr 1; omega
  induction p using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [countBound_query_bind] at h
    rw [simulateQ_bind,simulateQ_spec_query]
    rcases t with j | r | t
    · simp only [rawImpl]
      erw [countBound_query_bind]
      simp only [Bool.false_eq_true,ite_false] at h ⊢
      exact fun i => ih i q (h i)
    · simp only [rawImpl,program_bind,pure_bind]
      cases read with
      | true =>
        simp only [ite_true] at h
        have tail := ih () (q-1) (h.2 ())
        apply count_mono _ _ _ (circuit_count (A.selected L base r.sel r.act) true cc _ _ tail)
        have hCost := A.selected_cost L base r.sel r.act
        have hn := add q h.1
        dsimp [b] at hn ⊢
        omega
      | false =>
        simp only [Bool.false_eq_true,ite_false] at h
        have tail := circuit_count (A.selected L base r.sel r.act) false cc _ _ (ih () q (h ()))
        simpa only [Bool.false_eq_true,ite_false,Nat.zero_add] using tail
    · simp only [rawImpl]
      erw [countBound_query_bind]
      by_cases hcc : cc t = true
      · rw [ite_eq_left hcc] at h ⊢
        have hn := add q h.1
        change 0 < b*q ∧ _
        refine ⟨by omega,fun z => count_mono _ _ ?_ (ih z (q-1) (h.2 z))⟩
        change b*(q-1) ≤ b*q-1
        omega
      · rw [ite_eq_right hcc] at h ⊢
        exact fun z => ih z q (h z)

omit [DecidableEq U] in
theorem raw_cap (ok : ι → Prop) (out : α → Prop) (p : Source U T sp α)
    (h : AllQueries (allowed ok) out p) : AllQueries (allowed ok) out (raw A L base p) := by
  unfold raw
  induction p using OracleComp.inductionOn with
  | pure a => exact h
  | query_bind t k ih =>
    rw [QMsg.allQ_query_bind] at h
    rw [simulateQ_bind,simulateQ_spec_query]
    rcases t with j | r | t
    · exact ⟨trivial,fun i => ih i (h.2 i)⟩
    · simp only [rawImpl,program_bind,pure_bind]
      exact circuit_cap _ _ _ _ (ih () (h.2 ()))
    · exact ⟨h.1,fun z => ih z (h.2 z)⟩

end Reduction.ShakePermutation.Fix.Machine
#print axioms Reduction.ShakePermutation.Fix.Machine.raw_count
#print axioms Reduction.ShakePermutation.Fix.Machine.raw_cap
