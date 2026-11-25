import Parallel.KeygenShapeTable
import Parallel.KeygenHost
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost
open ParallelKeygen.Tree
noncomputable section

/-- The lane identifier is the scalar, two-key, four-key or eight-key leaf
entry in shake/batch.rs. The packed flag selects pair_active or thash_pair. -/
class TreeOps where
  wide : Bool
  leaf {N : Usize} (lanes : Nat) (sk seed : Array U8 N) (a : address.Adrs) (key : U32) : Result (Array U8 N)
  pair {N : Usize} (packed : Bool) (seed : Array U8 N) (a : address.Adrs) (l r : Array U8 N) : Result (Array U8 N)

def shape (wide : Bool) (z : Nat) := (schedule wide)[z-1]?.getD (.leaf 1 0)

theorem table_valid (wide : Bool) (h : Nat) (lo : 1≤h) (hi : h≤9) : valid (shape wide h) h=true := by
  cases wide <;> interval_cases h <;> decide

def treePair [ops : TreeOps] {N : Usize} (seed : Array U8 N) (a : address.Adrs) (b : Bool) (z i : Nat)
    (left right : Result (Array U8 N)) : Result (Array U8 N) := do
  let l ← left
  let r ← right
  let atype ← address.Adrs.with_type a address.TREE
  let ah ← address.Adrs.with_word2 atype (word z)
  let parent ← address.Adrs.with_word3 ah (word i)
  ops.pair b seed parent l r

def tree [ops : TreeOps] {N : Usize} (sk seed : Array U8 N) (i z : U32) (a : address.Adrs) :=
  eval (fun k j => ops.leaf k sk seed a (word j)) (treePair seed a) (shape ops.wide z.val) z.val i.val

structure TreeOpsCorrect (ops : TreeOps) (p : params.Params) (N : Usize) : Prop where
  leaf : ∀ k (sk seed : Array U8 N) (a : address.Adrs) (i : U32),
    ops.leaf k sk seed a i ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p) (bytes sk.val)
      i.val 0 (bytes seed.val) (adrsS a) ⦄
  pair : ∀ b (seed : Array U8 N) (a : address.Adrs) (l r : Array U8 N),
    ops.pair b seed a l r ⦃ out => bytes out.val=Spec.H (Shake.params p) (bytes seed.val) (adrsS a)
      (bytes l.val ++ bytes r.val) ⦄

theorem tree_spec [ops : TreeOps] {N : Usize} (p : params.Params) (correct : TreeOpsCorrect ops p N)
    (sk seed : Array U8 N) (i z : U32) (a : address.Adrs) (lo : 1≤z.val) (hi : z.val≤9)
    (room : (i.val+1)*2^z.val≤512) :
    tree sk seed i z a ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p)
      (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄ := by
  let P (h idx : Nat) (x : Result (Array U8 N)) := x ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p)
    (bytes sk.val) idx h (bytes seed.val) (adrsS a) ⦄
  apply eval_contract _ _ P _ _ _ _ _ (table_valid _ _ lo hi) room
  · intro k idx bound
    have wd : (word idx).val=idx := by change (BitVec.ofNat 32 idx).toNat=idx; simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : idx<2^32)]
    simpa only [P,wd] using correct.leaf k sk seed a (word idx)
  · intro b h idx l r fits lh rh
    have idxBound := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (h+1))).trans fits
    have hz : h+1<2^32 := by
      have cap := (Nat.le_mul_of_pos_left (2^(h+1)) (Nat.succ_pos idx)).trans fits
      have := Nat.lt_two_pow_self (n:=h+1)
      omega
    have wordOk (v : Nat) (bound : v<2^32) : (word v).val=v := by change (BitVec.ofNat 32 v).toNat=v; simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
    unfold P at lh rh ⊢
    unfold treePair
    obtain ⟨l',runL,postL⟩ := spec_imp_exists lh
    obtain ⟨r',runR,postR⟩ := spec_imp_exists rh
    simp only [runL,runR,bind_ok,address.Adrs.with_type,address.Adrs.with_word2,address.Adrs.with_word3]
    apply WP.spec_mono (correct.pair b seed _ l' r')
    intro v got
    simp only [got,postL,postR,Spec.xmssNode,adrsS,Spec.Adrs.setTypeAndClear,wordOk _ hz,
      wordOk idx (by omega),Spec.TREE,address.TREE]
    rfl
end
end slhdsa.ParallelKeygenHost
