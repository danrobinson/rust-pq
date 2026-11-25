import Buffered.Leaves
import Fused.AuthSuffix
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
set_option maxHeartbeats 2000000
set_option linter.concreteInstances false
variable [kernel : Kernel]
local instance smallMachine : Machine := machine kernel

private def Gathered {N : Usize} (idx : U32) (tree : address.Adrs) (leaves : Array (Array U8 N) 4#usize)
    (count : Nat) (addresses : Array address.Adrs 8#usize) (ls rs : Rows8 N) : Prop :=
  ∀ j<count, adrsS addresses.val[j]! = {adrsS tree with word2:=1,word3:=2*idx.val+j} ∧
    ls.val[j]! = leaves.val[2*j]! ∧ rs.val[j]! = leaves.val[2*j+1]!

private theorem gather {N : Usize} (idx : U32) (tree : address.Adrs) (leaves : Array (Array U8 N) 4#usize)
    (addresses : Array address.Adrs 8#usize) (ls rs : Rows8 N) (bound : idx.val<128) :
    subtree_loop0 ⟨0#usize,2#usize⟩ idx tree leaves addresses ls rs ⦃ a l r => Gathered idx tree leaves 2 a l r ⦄ := by
  unfold subtree_loop0
  apply loop.spec_decr_nat (measure := fun s : core.ops.range.Range Usize × Array address.Adrs 8#usize × Rows8 N × Rows8 N => 2-s.1.start.val)
    (inv := fun s => s.1.«end»=2#usize ∧ s.1.start.val≤2 ∧ Gathered idx tree leaves s.1.start.val s.2.1 s.2.2.1 s.2.2.2)
  · rintro ⟨it,addresses,ls,rs⟩ ⟨last,le,prior⟩
    simp only at last le prior ⊢
    unfold subtree_loop0.body
    by_cases more : it.start.val<2
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [last]; exact more) as ⟨_,next,tag,inc,stop⟩
      simp only [tag,lift,bind_ok]
      have cast : (UScalar.cast .U32 it.start).val=it.start.val := by scalar_tac
      step as ⟨a,level⟩
      step as ⟨base,baseVal⟩
      step as ⟨i,idxVal⟩
      step as ⟨parent,addr⟩
      step as ⟨addresses',storeA⟩
      step as ⟨li,liVal⟩
      step as ⟨l,loadL⟩
      step as ⟨ls',storeL⟩
      step as ⟨ri,riVal⟩
      step as ⟨r,loadR⟩
      step as ⟨rs',storeR⟩
      refine ⟨stop.trans last,by omega,?_,by omega⟩
      intro j hj
      rw [storeA,storeL,storeR,Array.set_val_eq,Array.set_val_eq,Array.set_val_eq]
      by_cases same : j=it.start.val
      · subst j
        rw [setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega)]
        rw [addr,level,loadL,loadR,←getElem!_pos,←getElem!_pos]
        simp [adrsS,idxVal,cast,baseVal,liVal,riVal,Nat.mul_comm]
      · rw [setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same)]
        exact prior j (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last]; exact Nat.le_of_not_gt more) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      simpa [step_simps,show it.start.val=2 by omega] using prior
  · exact ⟨rfl,by change 0≤2; decide,by intro j inside; exact False.elim (Nat.not_lt_zero j inside)⟩

theorem height_one {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (idx : U32) (a : address.Adrs) (small : SmallLeaves p sk seed a) (room : idx.val<256) :
    subtree sk seed idx 1#u32 a ⦃ out => bytes out.val =
      Spec.xmssNode (Shake.params p) (bytes sk.val) idx.val 1 (bytes seed.val) (adrsS a) ⦄ := by
  unfold subtree
  simp only [bind_ok,show (8#usize != 8#usize)=false from rfl,Bool.false_eq_true,ite_false]
  step as ⟨tree,treeSpec,treeEq⟩
  simp [lift,bind_ok,massert]
  step as ⟨first,firstEq⟩
  step with small 2#usize (Or.inl rfl) first (by change first.val+2≤512; omega) as ⟨leaves,values⟩
  step as ⟨adr,level⟩
  step as ⟨parent,index⟩
  step as ⟨l,loadL⟩
  step as ⟨r,loadR⟩
  step with Shake.pair_spec seed parent l r as ⟨out,hash⟩
  rw [loadL,loadR,←getElem!_pos,←getElem!_pos] at hash
  have left := values 0 (by decide)
  have right := values 1 (by decide)
  simp only [firstEq,Nat.add_zero,Nat.mul_comm idx.val 2] at left right
  apply Fused.parentValue p hp sk seed a (adrsS parent) _ _ _ idx.val 0
  · rw [index,level,treeEq]; simp only [adrsS,address.TREE,Spec.TREE,Spec.Adrs.setTypeAndClear]; rfl
  · exact left
  · exact right
  · simpa only [List.append_assoc] using hash

theorem height_two {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (idx : U32) (a : address.Adrs) (small : SmallLeaves p sk seed a) (room : idx.val<128)
    (active : ActiveCorrect (machine kernel) kernel.active) :
    subtree sk seed idx 2#u32 a ⦃ out => bytes out.val =
      Spec.xmssNode (Shake.params p) (bytes sk.val) idx.val 2 (bytes seed.val) (adrsS a) ⦄ := by
  unfold subtree
  simp only [bind_ok,show (8#usize != 8#usize)=false from rfl,Bool.false_eq_true,ite_false]
  step as ⟨tree,treeSpec,treeEq⟩
  simp [lift,bind_ok,massert,show (2#u32)≠1#u32 by decide]
  step as ⟨first,firstEq⟩
  step with small 4#usize (Or.inr rfl) first (by change first.val+4≤512; omega) as ⟨leaves,values⟩
  step with gather idx tree leaves _ _ _ room as ⟨addresses,ls,rs,g⟩
  step with @ActiveHash.pair_fips (machine kernel) kernel.active N seed addresses ls rs 2#usize
    (by change 2≤8; decide) active hp.le32 (aligned_hash hp) as ⟨parents,hashed⟩
  have firstRow (j : Nat) (hj : j<2) : bytes parents.val[j]!.val =
      Spec.xmssNode (Shake.params p) (bytes sk.val) (2*idx.val+j) 1 (bytes seed.val) (adrsS a) := by
    obtain ⟨addr,l,r⟩ := g j hj
    apply Fused.parentValue p hp sk seed a (adrsS addresses.val[j]!) (bytes ls.val[j]!.val) (bytes rs.val[j]!.val) _ (2*idx.val+j) 0
    · rw [addr,treeSpec]; simp only [address.TREE,Spec.TREE]; rfl
    · rw [l,values _ (by change 2*j<4; omega),show first.val+2*j=2*(2*idx.val+j) by omega]
    · rw [r,values _ (by change 2*j+1<4; omega),show first.val+(2*j+1)=2*(2*idx.val+j)+1 by omega]
    · exact hashed j hj
  have plen : parents.length=8 := Array.length_eq parents
  step as ⟨adr,level⟩
  step as ⟨parent,index⟩
  step as ⟨l,loadL⟩
  all_goals try (rw [plen];decide)
  step as ⟨r,loadR⟩
  all_goals try (rw [plen];decide)
  step with Shake.pair_spec seed parent l r as ⟨out,hash⟩
  rw [loadL,loadR,←getElem!_pos,←getElem!_pos] at hash
  apply Fused.parentValue p hp sk seed a (adrsS parent) _ _ _ idx.val 1
  · rw [index,level,treeEq]; simp only [adrsS,address.TREE,Spec.TREE,Spec.Adrs.setTypeAndClear]; rfl
  · simpa only [Nat.add_zero] using firstRow 0 (by decide)
  · exact firstRow 1 (by decide)
  · simpa only [List.append_assoc] using hash

end slhdsa.Buffered
