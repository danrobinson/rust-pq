import Parallel.Subtree
import Parallel.Signing

namespace ParallelSplitTree
open Spec ParallelSubtree

/-- Bottom-up reduction of consecutive subtrees, with the absolute address
index at each level and ascending in-place writes within a level. -/
def merge (hash : Nat → Nat → Bytes → Bytes → Bytes) (root : Nat) :
    Nat → Nat → (Nat → Bytes) → Bytes
  | _, 0, slots => slots 0
  | sub, levels+1, slots =>
    let count := 2^levels
    let next := reduce count (fun j => hash (sub+1) (root*count+j)) slots
    merge hash root (sub+1) levels next

theorem merge_eq (node : Nat → Nat → Bytes) (hash : Nat → Nat → Bytes → Bytes → Bytes)
    (step : ∀ h i, hash (h+1) i (node h (2*i)) (node h (2*i+1)) = node (h+1) i)
    (root sub levels : Nat) (slots : Nat → Bytes)
    (ready : ∀ j < 2^levels, slots j = node sub (root*2^levels+j)) :
    merge hash root sub levels slots = node (sub+levels) root := by
  induction levels generalizing slots sub with
  | zero => simpa [merge] using ready 0 (by decide)
  | succ n ih =>
    simp only [merge]
    rw [ih]
    · congr 1; omega
    · intro j hj
      have h₁ : 2*j < 2^(n+1) := by rw [Nat.pow_succ]; omega
      have h₂ : 2*j+1 < 2^(n+1) := by omega
      rw [reduce_eq, ite_eq_left hj, ready _ h₁, ready _ h₂, Nat.pow_succ]
      rw [← Nat.mul_assoc, Nat.mul_comm (root * 2^n) 2, ← Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_add]
      exact step sub (root*2^n+j)

theorem xmss (p : Params) (sk pk : Bytes) (a : Adrs) (root sub levels : Nat)
    (slots : Nat → Bytes)
    (ready : ∀ j < 2^levels, slots j = xmssNode p sk (root*2^levels+j) sub pk a) :
    merge (fun h i l r => H p pk {(a.setTypeAndClear TREE) with word2 := h, word3 := i} (l++r))
      root sub levels slots = xmssNode p sk root (sub+levels) pk a :=
  merge_eq (fun h i => xmssNode p sk i h pk a) _ (fun _ _ => rfl) _ _ _ _ ready

theorem fors (p : Params) (sk pk : Bytes) (a : Adrs) (root sub levels : Nat)
    (slots : Nat → Bytes)
    (ready : ∀ j < 2^levels, slots j = forsNode p sk (root*2^levels+j) sub pk a) :
    merge (fun h i l r => H p pk {a with word2 := h, word3 := i} (l++r))
      root sub levels slots = forsNode p sk root (sub+levels) pk a :=
  merge_eq (fun h i => forsNode p sk i h pk a) _ (fun _ _ => rfl) _ _ _ _ ready

/-- The public root for a drained key-generation queue. Ticket completion can
occur in any order. Each published node has the Algorithm 9 subtree contract. -/
theorem keygenRoot (p : Params) (sk pk : Bytes) (a : Adrs) (sub : Nat)
    (valid : sub ≤ p.hp) {k : Nat} {done : List Nat}
    (trace : ParallelSigning.Trace (2^(p.hp-sub)) k [] done)
    (drained : 2^(p.hp-sub) < k) :
    let slots := ParallelSigning.fill (fun i => xmssNode p sk i sub pk a) done
    merge (fun h i l r => H p pk {(a.setTypeAndClear TREE) with word2 := h, word3 := i} (l++r))
      0 sub (p.hp-sub) (fun i => (slots i).getD []) = xmssNode p sk 0 p.hp pk a := by
  dsimp only
  rw [xmss, Nat.add_sub_of_le valid]
  intro j hj
  have mem := ((trace.joined drained).exactly_once.2 j).mpr hj
  simp [ParallelSigning.fill_lookup, mem]

end ParallelSplitTree
