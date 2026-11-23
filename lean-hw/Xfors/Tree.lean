import Xfors.Batch
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Fors

def levelSpec {N} (p : params.Params) (seed : XForsRust.hash.Seed N) (sk : Array U8 N)
    (a : XForsRust.address.Adrs) (idx height k : Nat) (roots : Nodes N) :=
  ∀ j<2^(height-k), bytes roots.val[j]!.val = Spec.forsNode (paramsS p) (bytes sk.val)
    (idx*2^(height-k)+j) k (bytes seed.pk_seed.val) (addressOf a)

theorem nextLevel {N} (p : params.Params) (hp : PN p N) (seed : XForsRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (XForsRust.scalarSeed seed))) (sk : Array U8 N)
    (a : XForsRust.address.Adrs) (idx h k : Nat) (first level : U32) (n start : Usize) (roots arr : Nodes N)
    (height : h≤7) (active : k<h) (base : first.val=idx*2^(h-(k+1))) (lev : level.val=k+1)
    (size : n.val=2^(h-(k+1))) (prior : levelSpec p seed sk a idx h k roots)
    (limit : (idx+1)*2^h≤2^32) (bound : start.val≤n.val)
    (written : ∀ j<start.val, bytes arr.val[j]!.val=parent p seed {a with word2:=level} first roots j)
    (intact : ∀ j, start.val≤j → j<128 → arr.val[j]! = roots.val[j]!) :
    XForsRust.fors.wide.subtree_loop0_loop0 ⟨start,n⟩ seed.pk_seed seed.state seed.state512 arr first {a with word2:=level} ⦃ out =>
      levelSpec p seed sk a idx h (k+1) out ⦄ := by
  have small : n.val≤64 := by rw [size]; apply Nat.pow_le_pow_right (by decide : 0<2) (show h-(k+1)≤6 by omega)
  have spread : 2^(h-k)=2*2^(h-(k+1)) := by
    rw [show h-k=(h-(k+1))+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have room : first.val+n.val≤2^32 := by
    rw [base,size,← Nat.add_one_mul]
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))) limit
  apply WP.spec_mono (reduceLevel p hp seed hs _ first roots arr start n small room bound written intact)
  intro out reduced j hj
  rw [reduced j (by omega)]
  obtain ⟨hl,hr⟩ : 2*j<2^(h-k) ∧ 2*j+1<2^(h-k) := by omega
  simp only [parent,prior _ hl,prior _ hr,Spec.forsNode,base,lev]
  have leftEq : idx*2^(h-k)+2*j=2*(idx*2^(h-(k+1))+j) := by rw [spread]; ring
  have rightEq : idx*2^(h-k)+(2*j+1)=2*(idx*2^(h-(k+1))+j)+1 := by omega
  rw [leftEq,rightEq]
  simp [addressOf,TreeHash.addr,XForsRust.scalarAddr,adrsS,lev]

end slhdsa.X86.Fors
