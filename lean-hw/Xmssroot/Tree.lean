import Xmssroot.Level
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssRoot

def levelSpec {N} (p : params.Params) (seed : XmssRootRust.hash.Seed N) (sk : Array U8 N)
    (a : XmssRootRust.address.Adrs) (idx height k : Nat) (roots : Nodes N) :=
  ∀ j<2^(height-k), bytes roots.val[j]!.val = Spec.xmssNode (paramsS p) (bytes sk.val)
    (idx*2^(height-k)+j) k (bytes seed.pk_seed.val) (addressOf a)

theorem nextLevel {N} (p : params.Params) (hp : PN p N) (seed : XmssRootRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (XmssRootRust.parentSeed seed))) (sk : Array U8 N)
    (a : XmssRootRust.address.Adrs) (idx h k : Nat) (first level : U32) (n : Usize) (roots : Nodes N)
    (height : h≤4) (active : k<h) (base : first.val=idx*2^h) (lev : level.val=k+1)
    (size : n.val=2^(h-(k+1))) (prior : levelSpec p seed sk a idx h k roots)
    (limit : (idx+1)*2^h≤2^32) :
    XmssRootRust.xmss.wide.batch_root_loop0_loop0 ⟨0#usize,n⟩ seed first roots level
      {a with typ:=XmssRootRust.address.TREE,keypair:=0#u32,word2:=level,word3:=0#u32} ⦃ out =>
      levelSpec p seed sk a idx h (k+1) out ⦄ := by
  have small : n.val≤8 := by rw [size]; interval_cases h <;> interval_cases k <;> decide
  have spread : 2^(h-k)=2*2^(h-(k+1)) := by
    rw [show h-k=(h-(k+1))+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have off : first.val >>> level.val = idx*2^(h-(k+1)) := by
    rw [base,lev,Nat.shiftRight_eq_div_pow,show h=(h-(k+1))+(k+1) by omega,Nat.pow_add,← Nat.mul_assoc]
    simp
  have room : (first.val >>> level.val)+n.val≤2^32 := by
    rw [off,size,← Nat.add_one_mul]
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))) limit
  apply WP.spec_mono (reduceLevel p hp seed hs _ first level roots n small (by omega) room)
  intro out done j hj
  rw [done j (by omega)]
  obtain ⟨hl,hr⟩ : 2*j<2^(h-k) ∧ 2*j+1<2^(h-k) := by omega
  simp only [parent,prior _ hl,prior _ hr,Spec.xmssNode,off,lev]
  have leftEq : idx*2^(h-k)+2*j=2*(idx*2^(h-(k+1))+j) := by rw [spread]; ring
  have rightEq : idx*2^(h-k)+(2*j+1)=2*(idx*2^(h-(k+1))+j)+1 := by omega
  rw [leftEq,rightEq]
  simp only [addressOf,TreeHash.addr,XmssRootRust.parentAddr,adrsS,Spec.Adrs.setTypeAndClear,Spec.TREE,XmssRootRust.address.TREE,← lev,off]
  rfl
end slhdsa.X86.XmssRoot
