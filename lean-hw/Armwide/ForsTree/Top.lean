import Armwide.ForsTree.Levels

open Aeneas Aeneas.Std Result
namespace slhdsa.ArmForsTree
open ArmXmss
set_option maxRecDepth 8192

private theorem fill_spec {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (sk : Array U8 N) (a : address.Adrs) (tree : (adrsS a).typ=Spec.FORS_TREE)
    (first : U32) (s : Slice (Array U8 N)) :
    fillLeaves seed.state sk a first s ⦃ out => out.length=s.length ∧ ∀ i<s.length,
      bytes out.val[i]!.val=Spec.forsNode (paramsS p) (bytes sk.val) (first.val+i) 0 (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  have width : (paramsS p).n=N.val := congrArg UScalar.val hp.n_eq
  have seeded : wv seed.state.val=seedState N.val (bytes seed.pk_seed.val) := hs.1
  simp only [fillLeaves,WP.spec_ok,Slice.from_val,Slice.length,List.length_ofFn,true_and]
  intro i hi
  rw [getElem!_pos _ i (by simpa using hi),List.getElem_ofFn]
  have value := fused_leaf_fips (paramsS p) hp.valid (bytes seed.pk_seed.val) (bytes sk.val)
    (by rw [width];simp) (by rw [width];simp) (adrsS a) tree (first.val+i)
  rw [width,← seeded] at value
  exact (row_eq _ _ (by rw [value,Spec.forsNode_length _ hp.valid,width])).trans value

private theorem restored {N} (p : params.Params) (sk : Array U8 N) (seed : hash.Seed N) (a : address.Adrs)
    (idx h : Nat) (first : U32) (base : first.val=idx*2^h)
    (input : Nodes N 128#usize) (back : Slice (Array U8 N) → Nodes N 128#usize)
    (restore : ∀ s', (back s').val=input.val.setSlice! 0 s'.val)
    (out : Slice (Array U8 N)) (len : out.length=2^h)
    (values : ∀ i<2^h, bytes out.val[i]!.val=Spec.forsNode (paramsS p) (bytes sk.val)
      (first.val+i) 0 (bytes seed.pk_seed.val) (adrsS a)) (cap : 2^h≤128) :
    level p seed sk a idx h 0 (back out) := by
  intro j hj
  simp only [Nat.sub_zero] at hj ⊢
  rw [restore,List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega,by change j-0<out.length;omega,by simp;omega⟩]
  simpa only [Nat.sub_zero,base] using values j hj

private theorem finalNode {N} (p : params.Params) (sk : Array U8 N) (seed : hash.Seed N) (a : address.Adrs)
    (idx h : Nat) (roots : Nodes N 128#usize) (values : level p seed sk a idx h h roots) :
    bytes roots.val[0]!.val=Spec.forsNode (paramsS p) (bytes sk.val) idx h (bytes seed.pk_seed.val) (adrsS a) := by
  simpa using values 0 (by simp)

/-- Native Arm FORS subtree, through the extracted slice writes and root read,
with dynamic SHA-512 dispatch and every accepted native subtree height. -/
theorem subtree_fips {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N)
    (hs : SeedOk seed) (enabled : Bool) (sk : Array U8 N) (idx height : U32) (a : address.Adrs)
    (tree : (adrsS a).typ=Spec.FORS_TREE) (small : height.val≤7) (limit : (idx.val+1)*2^height.val≤2^32) :
    fors.arm.subtree enabled sk idx height seed a ⦃ out => bytes out.val=
      Spec.forsNode (paramsS p) (bytes sk.val) idx.val height.val (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  have cap : 2^height.val≤128 := Nat.pow_le_pow_right (by decide) small
  unfold fors.arm.subtree
  step as ⟨n,nEq⟩
  · rcases System.Platform.numBits_eq with b|b <;> rw [b] <;> omega
  have size : n.val=2^height.val := by
    rw [nEq,Nat.shiftLeft_eq,Nat.one_mul,Usize.size_scalarTac_eq.2,Nat.mod_eq_of_lt]
    rcases System.Platform.numBits_eq with b|b <;> rw [b] <;> omega
  have base (first : U32) (eqn : first.val=(idx.val <<< height.val)%U32.size) :
      first.val=idx.val*2^height.val := by
    rw [eqn,Nat.shiftLeft_eq,U32.size_eq,Nat.mod_eq_of_lt]
    rw [Nat.add_one_mul] at limit; have := Nat.two_pow_pos height.val;omega
  have fits : n≤128#usize := by change n.val≤128;omega
  split
  · rename_i width; subst N
    simp [lift,Array.to_slice_mut,Array.to_slice,Array.from_slice,core.slice.Slice.copy_from_slice,
      Slice.len,Array.length_eq,bind_ok]
    step as ⟨first,firstEq⟩
    step with Array.index_mut_SliceIndexRangeToUsizeSlice _ ⟨n⟩ fits as ⟨s,back,_,slen,write⟩
    step with fill_spec p hp seed hs sk a tree first s as ⟨out,len,vals⟩
    simp only [core.ops.range.RangeInclusive.new,bind_ok]
    have leaves := restored p sk seed a idx.val height.val first (base _ firstEq) _ back write out
      (len.trans (slen.trans size)) (by simpa only [slen,size] using vals) cap
    step with reduceSmall p hp seed hs sk a idx height n _ small size leaves limit as ⟨roots,done⟩
    step as ⟨v,read⟩
    simpa [read,getElem!_pos] using finalNode p sk seed a idx.val height.val roots done
  · rename_i notSmall
    have wide : N.val=24 ∨ N.val=32 := by rcases hp.nok with h|h|h <;> scalar_tac
    step as ⟨first,firstEq⟩
    step with Array.index_mut_SliceIndexRangeToUsizeSlice _ ⟨n⟩ fits as ⟨s,back,_,slen,write⟩
    step with fill_spec p hp seed hs sk a tree first s as ⟨out,len,vals⟩
    simp only [core.ops.range.RangeInclusive.new,bind_ok]
    have leaves := restored p sk seed a idx.val height.val first (base _ firstEq) _ back write out
      (len.trans (slen.trans size)) (by simpa only [slen,size] using vals) cap
    step with reduceWide p hp seed hs wide enabled sk a idx height n _ small size leaves limit as ⟨roots,done⟩
    step as ⟨v,read⟩
    simpa [read,getElem!_pos] using finalNode p sk seed a idx.val height.val roots done

end slhdsa.ArmForsTree
