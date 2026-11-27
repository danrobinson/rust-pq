import Spec.SlhDsa
import Shakeopt.ForsTreeTable
namespace Shakeopt.ForsTree
open Spec ParallelKeygen.Tree

/-- The source trace preserves the root index as an affine indeterminate.
    Every intermediate coefficient and constant has the displayed bound. -/
theorem index_fits (root height scale offset : Nat) (cap : (root+1)*2^height < 2^32)
    (hs : scale ≤ 2^height) (ho : offset ≤ 2^height) : scale*root+offset < 2^32 := by
  have bound := Nat.add_le_add (Nat.mul_le_mul_right root hs) ho
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm root] at cap
  exact bound.trans_lt cap

private theorem valid_at (h : Nat) (lo : 3≤h) (hi : h≤14) :
    valid (schedule[h-3]?.getD (.leaf 0 0)) h=true := by
  have all : ∀ t : Fin 12, valid (schedule[t.val]?.getD (.leaf 0 0)) (t.val+3)=true := by decide
  simpa only [Nat.sub_add_cancel lo] using all ⟨h-3,by omega⟩

/-- Evaluate the actual source-selected single and packed parents, and the
    fused leaf result, with arbitrary values satisfying their local API contracts. -/
def root {B : Type} (leaf : Nat → B) (parent : Bool → Nat → Nat → B → B → B) (h i : Nat) : B :=
  eval (fun _ => leaf) parent (schedule[h-3]?.getD (.leaf 0 0)) h i

theorem root_fips (p : Params) (sk pk : Bytes) (a : Adrs)
    (leaf : Nat → Bytes) (parent : Bool → Nat → Nat → Bytes → Bytes → Bytes)
    (leaves : ∀ i, leaf i=F p pk {a with word2:=0,word3:=i} (forsSkGen p sk pk a i))
    (parents : ∀ packed h i l r, parent packed (h+1) i l r=H p pk {a with word2:=h+1,word3:=i} (l++r))
    (h i : Nat) (lo : 3≤h) (hi : h≤14) : root leaf parent h i=forsNode p sk i h pk a := by
  apply eval_valid _ _ (fun z j => forsNode p sk j z pk a)
  · exact fun _ i => leaves i
  · intro b z i; exact parents b z i _ _
  · exact valid_at h lo hi
end Shakeopt.ForsTree
