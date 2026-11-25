import Shakebatch.WidthEightForsValues
namespace slhdsa.WidthEight.Fors
open Aeneas Aeneas.Std Result ShakeBatch NativeVerify Spec
open Shakeopt Shakeopt.ForsPlan ParallelKeygen.Tree

/-- Each physical node retains its actual N-byte result. This also makes the
packed and single-parent kernels usable without decoding arbitrary lists. -/
def subtree {B : Type} (leaf : Nat → B) (parent : Bool → Nat → Nat → B → B → B) (h i : Nat) : B :=
  let first := fun k => parent true 1 k (leaf (2*k)) (leaf (2*k+1))
  match h with
  | 0 => leaf i
  | 1 => first i
  | 2 => parent true 2 i (first (2*i)) (first (2*i+1))
  | z+3 => ForsTree.root leaf parent (z+3) i

private theorem eval_map {B} (f : B → Bytes) (leaf : Nat → B) (parent : Bool → Nat → Nat → B → B → B)
    (lv : Nat → Bytes) (pv : ForsWideSignature.Parent) (hl : ∀ i, f (leaf i)=lv i)
    (hp : ∀ b h i l r, f (parent b h i l r)=pv b h i (f l) (f r)) (s : Shape) (h i : Nat) :
    f (eval (fun _ => leaf) parent s h i) = eval (fun _ => lv) pv s h i := by
  induction s generalizing h i with
  | leaf => apply hl
  | branch b z off l r il ir => simp only [eval,hp,il,ir]

private theorem subtree_map {B} (f : B → Bytes) (leaf : Nat → B) (parent : Bool → Nat → Nat → B → B → B)
    (lv : Nat → Bytes) (pv : ForsWideSignature.Parent) (hl : ∀ i, f (leaf i)=lv i)
    (hp : ∀ b h i l r, f (parent b h i l r)=pv b h i (f l) (f r)) (h i : Nat) :
    f (subtree leaf parent h i) = ForsWideSignature.subtree lv pv h i := by
  match h with
  | 0 | 1 | 2 => simp only [subtree,ForsWideSignature.subtree,hp,hl]
  | h+3 => exact eval_map f leaf parent lv pv hl hp _ _ _

variable [machine : Machine]
def signature (perm : Active machine) {N : Usize} (p : params.Params) (md : Slice U8) (sk seed : Array U8 N)
    (a : address.Adrs) : Bytes :=
  let pick := fun j => (Spec.base2b (bytes md.val) p.a.val p.k.val)[j]!
  (canonical (Shake.params p) false).flatMap fun (op,x) => bytes (match op with
    | .secret => secret perm sk seed a (x.eval pick)
    | .node h => subtree (leaf perm sk seed a) (parent perm seed a) h (x.eval pick)).val

theorem signature_eq (perm : Active machine) (correct : ActiveCorrect machine perm) (pos : 0<machine.width.val)
    {N : Usize} (p : params.Params) (hp : PN p N) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    signature perm p md sk seed a=Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a) := by
  rw [←ForsWideSignature.signature_eq (Shake.params p) _ _ _ _ (by exact hp.valid.a_le)]
  unfold signature ForsWideSignature.signature ForsWideSignature.execute
  apply List.flatMap_congr
  rintro ⟨op,x⟩ _
  cases op with
  | secret => exact secret_fips perm correct pos p hp sk seed a _
  | node h =>
    apply subtree_map (fun row : Array U8 N => bytes row.val) _ _ _ _
    · intro i
      exact leaf_fips perm correct pos p hp sk seed a domain i
    · intro b z i l r
      exact parent_fips perm correct pos p hp seed a b z i l r

end slhdsa.WidthEight.Fors
