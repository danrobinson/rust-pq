import Spec.SlhDsa
import Mathlib.Data.List.Basic

namespace ParallelSubtree
open Spec

/-- Projection commutes with every iteration of a lane-wise loop. -/
private theorem project {α β ι : Type} (xs : List α) (step : α → ι → β → β)
    (init : ι → β) (i : ι) :
    (xs.foldl (fun st x j => step x j (st j)) init) i =
      xs.foldl (fun st x => step x i st) (init i) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => exact ih _

def leafAddr (a : Adrs) (idx : Nat) (i : Fin 8) : Adrs :=
  { a.setTypeAndClear WOTS_HASH with keypair := 8*idx+i.val }

def endpoints (p : Params) (sk pk : Bytes) (a : Fin 8 → Adrs) (c : Nat) : Fin 8 → Bytes :=
  (List.range 15).foldl (fun st k i => F p pk {a i with word2 := c, word3 := k} (st i))
    (fun i => PRF p pk sk {wotsSkAdrs (a i) with word2 := c})

def leaves (p : Params) (sk pk : Bytes) (a : Fin 8 → Adrs) : Fin 8 → Bytes :=
  let msgs := (List.range (2*p.n+3)).foldl (fun st c i => st i ++ endpoints p sk pk a c i)
    (fun _ => [])
  fun i => T p pk (wotsPkAdrs (a i)) (msgs i)

private theorem appendFold (xs : List Nat) (f : Nat → Bytes) (acc : Bytes) :
    xs.foldl (fun s i => s ++ f i) acc = acc ++ xs.flatMap f := by
  induction xs generalizing acc with
  | nil => simp
  | cons _ _ ih => simp [ih, List.append_assoc]

theorem leaves_eq (p : Params) (sk pk : Bytes) (a : Fin 8 → Adrs)
    (len : p.len = 2*p.n+3) (w : p.w=16) (i : Fin 8) :
    leaves p sk pk a i = wotsPkGen p sk pk (a i) := by
  unfold leaves wotsPkGen
  rw [project (List.range _) (fun c i s => s ++ endpoints p sk pk a c i), appendFold]
  simp only [List.nil_append, len, w]
  congr 1

/-- Model the ascending in-place writes. Reads for parent k still see both original children. -/
def reduce (count : Nat) (hash : Nat → Bytes → Bytes → Bytes) (nodes : Nat → Bytes) :=
  (List.range count).foldl (fun old k j =>
    if j=k then hash k (old (2*k)) (old (2*k+1)) else old j) nodes

theorem reduce_eq (count : Nat) (hash : Nat → Bytes → Bytes → Bytes) (nodes : Nat → Bytes)
    (j : Nat) : reduce count hash nodes j =
      if j<count then hash j (nodes (2*j)) (nodes (2*j+1)) else nodes j := by
  induction count generalizing j with
  | zero => simp [reduce]
  | succ n ih =>
    simp only [reduce,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] at *
    by_cases eq : j=n
    · subst j; simp [ih, show ¬2*n<n by omega, show ¬2*n+1<n by omega]
    · simp only [eq,ite_false,ih, show (j<n+1) ↔ (j<n) by omega]

def parent (p : Params) (pk : Bytes) (addr : Adrs) (idx count height k : Nat) (l r : Bytes) :=
  H p pk {addr.setTypeAndClear TREE with word2 := height, word3 := idx*count+k} (l ++ r)

def subtree8 (p : Params) (sk pk : Bytes) (a : Adrs) (idx : Nat) : Bytes :=
  let base := leaves p sk pk (leafAddr a idx)
  let nodes := fun i => base ⟨i%8, Nat.mod_lt _ (by decide)⟩
  let level := fun n h => reduce n (parent p pk a idx n h)
  level 1 3 (level 2 2 (level 4 1 nodes)) 0

theorem subtree_eq (p : Params) (sk pk : Bytes) (a : Adrs) (idx : Nat)
    (len : p.len = 2*p.n+3) (w : p.w=16) :
    subtree8 p sk pk a idx = xmssNode p sk idx 3 pk a := by
  simp only [subtree8, reduce_eq]
  simp (config := { decide := true }) only [Nat.reduceMul,Nat.reduceAdd,
    Nat.reduceMod,ite_true,leaves_eq _ _ _ _ len w, parent]
  simp only [xmssNode,leafAddr, Nat.mul_one,Nat.add_zero]
  simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]

#print axioms subtree_eq
end ParallelSubtree
