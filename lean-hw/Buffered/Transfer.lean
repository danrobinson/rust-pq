import Buffered.Grid
import Buffered.Store
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered
open ShakeBatch

def xmss {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (h i : Nat) :=
  Spec.xmssNode (Shake.params p) (bytes sk.val) i h (bytes seed.val) (adrsS a)

theorem hashed_node {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a tree : address.Adrs)
    {root z c} {buf : Buffer N} {len cur} (old : Grid (xmss p sk seed a) root z c buf len cur)
    (h j : Nat) (live : h<z) (enough : 2*j+1<waiting c h) (domain : adrsS tree=(adrsS a).setTypeAndClear Spec.TREE) :
    Spec.H (Shake.params p) (bytes seed.val) {adrsS tree with word2:=h+1,word3:=nextBase root z c (h+1)+j}
      (cellBytes buf h (2*j) ++ cellBytes buf h (2*j+1)) =
    xmss p sk seed a (h+1) (nextBase root z c (h+1)+j) := by
  rw [old.cell h (by omega) (2*j) (by omega),old.cell h (by omega) (2*j+1) enough,domain]
  simp only [xmss,Spec.xmssNode]
  have e : rowBase root z c h + 2*j = 2*(nextBase root z c (h+1)+j) := by
    simp [rowBase,nextBase,level_step root z h live]
    omega
  rw [e,show rowBase root z c h+(2*j+1)=2*(nextBase root z c (h+1)+j)+1 by omega]

theorem set_value {α : Type} [Inhabited α] {n : Usize} (old : Array α n) (k : Usize) (v : α) (j : Nat)
    (fits : k.val<n.val) : (old.set k v).val[j]! = if j=k.val then v else old.val[j]! := by
  rw [Array.set_val_eq]
  by_cases same : j=k.val
  · subst j;rw [if_pos rfl,setSame _ _ _ (by simpa using fits)]
  · rw [if_neg same,setOther _ _ _ _ (Ne.symm same)]

theorem stored_bytes {N depth : Usize} {buf out : Array (Row16 N) depth} {h pos n : Nat} {rows : Rows8 N}
    (store : Stored buf out h pos n rows) (node : Nat → Spec.Bytes)
    (refine : ∀ k<n, bytes rows.val[k]!.val=node k) (k j : Nat) :
    cellBytes out k j = if k=h ∧ pos≤j ∧ j<pos+n then node (j-pos) else cellBytes buf k j := by
  unfold cellBytes;rw [store k j];split_ifs with hit
  · exact refine _ (by omega)
  · rfl
end slhdsa.Buffered
