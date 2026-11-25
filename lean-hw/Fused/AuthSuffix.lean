import Fused.AuthPairs
import Fused.AuthTail
import Shakebatch.Sibling
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
set_option maxHeartbeats 2000000
variable [kernel : Kernel]
local instance authSuffixMachine : Machine := machine kernel

/-- The suffix of the extracted wide XMSS signer, beginning at the first
authentication-block byte offset. -/
def auth_suffix {N : Usize} (p : params.Params) (sk : Array U8 N) (idx : U32) (seed : Array U8 N)
    (addr : address.Adrs) (len sig_lane : Usize) (base_leaf : U32) (sig1 : alloc.vec.Vec U8)
    (nodes : Array (Array U8 N) 8#usize) : Result (alloc.vec.Vec U8) := do
    let out_pos ← len * N
    let i6 ← out_pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig1 { start := out_pos, «end» := i6 }
    let i7 ← lift (sig_lane ^^^ 1#usize)
    let a5 ← Array.index_usize nodes i7
    let s1 ← lift (Array.to_slice a5)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let tree_adrs ← address.Adrs.with_type addr address.TREE
    let i8 ← sig_lane >>> 1#i32
    let p1 ← lift (i8 ^^^ 1#usize)
    let i9 ← sig_lane >>> 2#i32
    let h2 ← lift (i9 ^^^ 1#usize)
    let i10 ← 2#usize * h2
    let i11 ← i10 + 1#usize
    let addrs := Array.repeat 8#usize tree_adrs
    let a6 := Array.repeat N 0#u8
    let left := Array.repeat 8#usize a6
    let a7 := Array.repeat N 0#u8
    let right := Array.repeat 8#usize a7
    let s3 ← lift (Array.to_slice (Array.make 3#usize [ p1, i10, i11 ]))
    let i12 ← core.slice.Slice.iter s3
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.Usize) i12
    let sig2 := index_mut_back s2
    let (addrs1, left1, right1) ←
      xmss_sign_batch_loop4 iter base_leaf nodes tree_adrs addrs
        left right
    let lvl1 ← (NativeVerify.ActiveHash.pair_active kernel.active) seed addrs1 left1 right1 3#usize
    let i13 ← i6 + N
    let (s4, index_mut_back1) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig2 { start := i6, «end» := i13 }
    let a8 ← Array.index_usize lvl1 0#usize
    let s5 ← lift (Array.to_slice a8)
    let s6 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s4 s5
    let a9 ← address.Adrs.with_word2 tree_adrs 2#u32
    let i14 ← base_leaf >>> 2#i32
    let i15 ← lift (UScalar.cast .U32 h2)
    let i16 ← i14 + i15
    let a21 ← address.Adrs.with_word3 a9 i16
    let a10 ← Array.index_usize lvl1 1#usize
    let a11 ← Array.index_usize lvl1 2#usize
    let auth2 ← shake.hash.thash_pair seed a21 a10 a11
    let sig3 := index_mut_back1 s6
    let i17 ← i13 + N
    let (s7, index_mut_back2) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig3 { start := i13, «end» := i17 }
    let s8 ← lift (Array.to_slice auth2)
    let s9 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s7 s8
    let sig4 := index_mut_back2 s9
    xmss_sign_batch_loop5 { start := 3#u32, «end» := p.hp } sk
      idx seed addr sig4 i17

private theorem parentValue {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (parent : Spec.Adrs) (left right value : Spec.Bytes) (i z : Nat)
    (aspec : parent = {(adrsS a).setTypeAndClear Spec.TREE with word2:=z+1,word3:=i})
    (l : left = Spec.xmssNode (Shake.params p) (bytes sk.val) (2*i) z (bytes seed.val) (adrsS a))
    (r : right = Spec.xmssNode (Shake.params p) (bytes sk.val) (2*i+1) z (bytes seed.val) (adrsS a))
    (hash : value=Spec.shake256 (bytes seed.val ++ (parent.bytes ++ (left ++ right))) N.val) :
    value = Spec.xmssNode (Shake.params p) (bytes sk.val) i (z+1) (bytes seed.val) (adrsS a) := by
  rw [hash,aspec,l,r,Spec.xmssNode]
  simp [Spec.H,Shake.params,paramsS_n,hp.n_eq,List.append_assoc]

private theorem laneSibling (idx lane base z : Nat) (h : z<3) (b : base=8*(idx/8)) (l : lane=idx%8) :
    ((idx / 2^z) ^^^ 1) = idx/8 * 2^(3-z) + ((lane/2^z) ^^^ 1) := by
  have eq : (idx/8)*2^3+lane=idx := by omega
  simpa only [eq] using ShakeBatch.sibling_eq (idx/8) lane 3 z h

theorem suffix_correct {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N) (idx : U32)
    (seed : Array U8 N) (a : address.Adrs) (len lane : Usize) (base : U32)
    (sig : alloc.vec.Vec U8) (rows : Array (Array U8 N) 8#usize) (front : Spec.Bytes)
    (subtree : SubtreeAt p sk seed a) (perms : ActiveCorrect (machine kernel) kernel.active)
    (height : 3≤p.hp.val) (bound : idx.val<2^p.hp.val) (baseAligned : base.val=8*(idx.val/8))
    (laneOk : lane.val=idx.val%8) (length : sig.length=len.val*N.val+p.hp.val*N.val)
    (written : bytes (sig.val.take (len.val*N.val))=front)
    (leaves : ∀ j < 8, bytes rows.val[j]!.val = Spec.xmssNode (Shake.params p) (bytes sk.val)
      (base.val+j) 0 (bytes seed.val) (adrsS a)) :
    auth_suffix p sk idx seed a len lane base sig rows ⦃ out =>
      bytes out.val=front ++ authPrefix (SiblingAt p sk seed a idx.val) p.hp.val ⦄ := by
  let node := fun i z => Spec.xmssNode (Shake.params p) (bytes sk.val) i z (bytes seed.val) (adrsS a)
  let outBase := len.val*N.val
  have room3 := Nat.mul_le_mul_right N.val height
  have max : sig.length≤Usize.max := by simp
  have laneb : lane.val<8 := laneOk ▸ Nat.mod_lt _ (by decide)
  have small : idx.val<512 := bound.trans_le (Nat.pow_le_pow_right (by decide) hp.valid.hp_le)
  have siblings := laneSibling idx.val lane.val base.val
  unfold auth_suffix
  step as ⟨lo,loEq⟩
  step as ⟨hi1,h1⟩
  step as ⟨dst1,back1,_,ld1,wr1⟩
  have sib0 : (lane ^^^ 1#usize).val=lane.val ^^^ 1 := by simp [UScalar.val_xor]
  have sib0lt : (lane ^^^ 1#usize).val<8 := sib0 ▸ Nat.xor_lt_two_pow (n:=3) laneb (by decide)
  try simp only [lift,bind_ok]
  step as ⟨row0,read0⟩
  try simp only [lift,bind_ok]
  step as ⟨w0,cpy0⟩
  all_goals try scalar_tac
  have save0 : (back1 w0).val=sig.val.setSlice! lo.val row0.val := by
    rw [wr1,cpy0];simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,Array.val_to_slice]
  obtain ⟨size0,head0⟩ := copy_prefix sig _ row0 _ (by omega) save0
  have node0 : bytes row0.val=SiblingAt p sk seed a idx.val 0 := by
    rw [read0,←getElem!_pos,leaves _ sib0lt,sib0]
    unfold SiblingAt
    rw [siblings 0 (by decide) baseAligned laneOk]
    congr 3 <;> omega
  step as ⟨atree,tree,_⟩
  step as ⟨x1,x1v,_⟩
  all_goals try (rcases System.Platform.numBits_eq with bits|bits <;> rw [bits] <;> decide)
  try simp only [lift,bind_ok]
  step as ⟨x2,x2v,_⟩
  all_goals try (rcases System.Platform.numBits_eq with bits|bits <;> rw [bits] <;> decide)
  try simp only [lift,bind_ok]
  let i1 := x1 ^^^ 1#usize
  let i2 := x2 ^^^ 1#usize
  have p1 : i1.val=(lane.val/2)^^^1 := by simp [i1,UScalar.val_xor,x1v,Nat.shiftRight_eq_div_pow]
  have p2 : i2.val=(lane.val/4)^^^1 := by simp [i2,UScalar.val_xor,x2v,Nat.shiftRight_eq_div_pow]
  have lt1 : i1.val<4 := p1 ▸ Nat.xor_lt_two_pow (n:=2) (by omega) (by decide)
  have lt2 : i2.val<2 := p2 ▸ Nat.xor_lt_two_pow (n:=1) (by omega) (by decide)
  step as ⟨c0,c0v⟩
  step as ⟨c1,c1v⟩
  change c0.val=2*i2.val at c0v
  change c1.val=c0.val+1 at c1v
  let prs : Slice Usize := (Array.make 3#usize [i1,c0,c1]).to_slice
  have prsVal : prs.val=[i1,c0,c1] := rfl
  have three : prs.length=3 := rfl
  have bounds (j : Nat) (live : j<prs.length) : prs.val[j]!.val<4 := by
    rw [three] at live
    have lc0 : c0.val<4 := by change c0.val=2*i2.val at c0v;omega
    have lc1 : c1.val<4 := by change c0.val=2*i2.val at c0v;omega
    interval_cases j <;> first | exact lt1 | exact lc0 | exact lc1
  simp only [core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,core.iter.traits.iterator.Iterator.enumerate.default,lift,bind_ok]
  step with prepare_pairs prs base rows atree _ _ _ (by omega) bounds as ⟨addresses,left,right,prepared⟩
  step with @ActiveHash.pair_fips (machine kernel) kernel.active N seed addresses left right 3#usize (by change 3≤8; decide) perms hp.le32 (aligned_hash hp) as ⟨lv1,values⟩
  have lvLen : lv1.length=8 := Array.length_eq lv1
  have parent (j : Nat) (jl : j<3) : bytes lv1.val[j]!.val = node (base.val/2+prs.val[j]!.val) 1 := by
    obtain ⟨addr,leftRow,rightRow⟩ := prepared j jl
    have prb := bounds j jl
    have lhs := leaves (2*prs.val[j]!.val) (by omega)
    have rhs := leaves (2*prs.val[j]!.val+1) (by omega)
    apply parentValue p hp sk seed a (adrsS addresses.val[j]!) (bytes left.val[j]!.val) (bytes right.val[j]!.val) _ (base.val/2+prs.val[j]!.val) 0
    · rw [addr,tree];simp only [address.TREE,Spec.TREE] <;> rfl
    · rw [leftRow,lhs];congr 1 <;> omega
    · rw [rightRow,rhs];congr 1 <;> omega
    · exact values j jl
  step as ⟨hi2,h2⟩
  step as ⟨dst2,back2,_,ld2,wr2⟩
  step as ⟨row1,read1⟩
  all_goals try (rw [lvLen];decide)
  try simp only [lift,bind_ok]
  step as ⟨w1,cpy1⟩
  all_goals try scalar_tac
  have save1 : (back2 w1).val=(back1 w0).val.setSlice! hi1.val row1.val := by
    rw [wr2,cpy1];simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,Array.val_to_slice]
  obtain ⟨size1,head1⟩ := copy_prefix _ _ row1 _ (by omega) save1
  have node1 : bytes row1.val=SiblingAt p sk seed a idx.val 1 := by
    rw [read1,←getElem!_pos,parent 0 (by decide),prsVal]
    unfold SiblingAt node
    rw [siblings 1 (by decide) baseAligned laneOk]
    change node (base.val/2+i1.val) 1 = node (idx.val/8*4 + ((lane.val/2) ^^^ 1)) 1
    rw [←p1]
    congr 1 <;> omega
  step as ⟨at2,at2v⟩
  step as ⟨b2,b2v,_⟩
  try simp only [lift,bind_ok]
  have cast : (UScalar.cast .U32 i2).val=i2.val := by scalar_tac
  have bp : b2.val=base.val/4 := by simp [b2v,Nat.shiftRight_eq_div_pow]
  step as ⟨word,wv⟩
  step as ⟨addr2,word3⟩
  step as ⟨l2,lget⟩
  all_goals try (rw [lvLen];decide)
  step as ⟨r2,rget⟩
  all_goals try (rw [lvLen];decide)
  step with Shake.pair_spec seed addr2 l2 r2 as ⟨row2,hash2⟩
  have node2 : bytes row2.val=SiblingAt p sk seed a idx.val 2 := by
    unfold SiblingAt
    rw [siblings 2 (by decide) baseAligned laneOk]
    have same : idx.val/8*2^(3-2)+(lane.val/2^2 ^^^ 1) = base.val/4+i2.val := by
      change idx.val/8*2 + ((lane.val/4) ^^^ 1) = base.val/4+i2.val
      rw [←p2];omega
    rw [same]
    apply parentValue p hp sk seed a (adrsS addr2) (bytes l2.val) (bytes r2.val) _ (base.val/4+i2.val) 1
    · rw [word3,at2v]
      change {adrsS atree with word2:=2,word3:=word.val} = _
      rw [tree,wv,cast,bp];simp only [address.TREE,Spec.TREE] <;> rfl
    · rw [lget,←getElem!_pos,parent 1 (by decide)]
      change node (base.val/2+c0.val) 1=_
      rw [c0v]
      unfold node
      congr 1 <;> omega
    · rw [rget,←getElem!_pos,parent 2 (by decide)]
      change node (base.val/2+c1.val) 1=_
      rw [c1v,c0v]
      unfold node
      congr 1 <;> omega
    · simpa only [List.append_assoc] using hash2
  step as ⟨hi3,h3⟩
  step as ⟨dst3,back3,_,ld3,wr3⟩
  try simp only [lift,bind_ok]
  step as ⟨w2,cpy2⟩
  all_goals try scalar_tac
  have save2 : (back3 w2).val=(back2 w1).val.setSlice! hi2.val row2.val := by
    rw [wr3,cpy2];simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,Array.val_to_slice]
  obtain ⟨size2,head2⟩ := copy_prefix _ _ row2 _ (by omega) save2
  apply auth_tail p hp sk seed idx a _ hi3 outBase 3#u32 front subtree bound height (by decide)
    (size2.trans (size1.trans (size0.trans length))) (by change hi3.val=outBase+3*N.val;dsimp [outBase];omega)
  rw [h3,head2,h2,head1,h1,head0,loEq,written,node0,node1,node2]
  simp [authPrefix,show List.range 3=[0,1,2] by decide,List.append_assoc]
end slhdsa.Fused
