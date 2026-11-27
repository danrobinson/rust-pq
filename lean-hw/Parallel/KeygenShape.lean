import Spec.SlhDsa
import Mathlib.Tactic.Ring
namespace ParallelKeygen.Tree
/-- Parent flags distinguish packed pair_active from the single thash_pair.
Leaf widths distinguish single-key, two-key, four-key, and eight-key calls. -/
inductive Shape where
  | leaf (lanes : Nat) (keyDelta : Int)
  | branch (packed : Bool) (levelDelta indexDelta : Int) (left right : Shape)
  deriving DecidableEq, Repr

def valid : Shape → Nat → Bool
  | .leaf _ d, 0 => d==0
  | .branch _ h i l r,z+1 => h==0 && i==0 && valid l z && valid r z
  | _,_ => false

def eval {B : Type} (leaf : Nat → Nat → B) (parent : Bool → Nat → Nat → B → B → B) :
    Shape → Nat → Nat → B
  | .leaf k off,_,i => leaf k ((i:Int)+off).toNat
  | .branch b h off l r,z,i => parent b ((z:Int)+h).toNat ((i:Int)+off).toNat
      (eval leaf parent l (z-1) (2*i)) (eval leaf parent r (z-1) (2*i+1))

theorem eval_valid {B} (leaf : Nat → Nat → B) (parent : Bool → Nat → Nat → B → B → B)
    (node : Nat → Nat → B) (leafOk : ∀ k i, leaf k i=node 0 i)
    (pairOk : ∀ b h i, parent b (h+1) i (node h (2*i)) (node h (2*i+1))=node (h+1) i)
    (shape : Shape) (h i : Nat) (good : valid shape h=true) : eval leaf parent shape h i=node h i := by
  induction shape generalizing h i with
  | leaf k off =>
    cases h <;> simp_all [valid,eval]
  | branch b level off l r il ir =>
    cases h with
    | zero => simp [valid] at good
    | succ h =>
      simp only [valid,Bool.and_eq_true,beq_iff_eq] at good
      obtain ⟨⟨⟨rfl,rfl⟩,left⟩,right⟩ := good
      simpa [eval,il _ _ left,ir _ _ right] using pairOk b h i
theorem eval_contract {B} (leaf : Nat → Nat → B) (parent : Bool → Nat → Nat → B → B → B)
    (P : Nat → Nat → B → Prop) (leafOk : ∀ k i, i<512 → P 0 i (leaf k i))
    (pairOk : ∀ b h i l r, (i+1)*2^(h+1)≤512 → P h (2*i) l → P h (2*i+1) r →
      P (h+1) i (parent b (h+1) i l r))
    (shape : Shape) (h i : Nat) (good : valid shape h=true) (room : (i+1)*2^h≤512) :
    P h i (eval leaf parent shape h i) := by
  induction shape generalizing h i with
  | leaf k off =>
    cases h <;> simp_all [valid,eval]
    exact leafOk k i (by omega)
  | branch b level off l r il ir =>
    cases h with
    | zero => simp [valid] at good
    | succ h =>
      simp only [valid,Bool.and_eq_true,beq_iff_eq] at good
      obtain ⟨⟨⟨rfl,rfl⟩,left⟩,right⟩ := good
      simp only [eval,Int.add_zero,Int.toNat_natCast,Nat.add_sub_cancel]
      apply pairOk _ _ _ _ _ room
      · apply il _ _ left
        have eq : (2*i+2)*2^h=(i+1)*2^(h+1) := by ring
        exact (Nat.mul_le_mul_right _ (by omega : 2*i+1≤2*i+2)).trans (eq.symm ▸ room)
      · apply ir _ _ right
        have eq : (2*i+1+1)*2^h=(i+1)*2^(h+1) := by ring
        rwa [eq]

end ParallelKeygen.Tree
