import Cachepath.BuilderShakeSteps
open Aeneas Aeneas.Std Result
open slhdsa.cache.endtoend
namespace slhdsa.cache.builder.nativeShake
set_option linter.concreteInstances false

private def RowPrefix {N : Usize} (f : Nat → Spec.Bytes) (size k : Nat) (s : Rows N) :=
  s.length = size ∧ ∀ j < k, bytes s.val[j]!.val = f j

private theorem one_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk pk : Array U8 N)
    (a : address.Adrs) (z : U32) (pos : 0 < z.val) (hz : z.val ≤ p.hp.val)
    (children parents : Rows N) (hc : Row children (2*width p.hp.val z.val) (Value p sk pk a (z.val-1)))
    (i : Usize) (hi : i.val < width p.hp.val z.val)
    (init : RowPrefix (Value p sk pk a z.val) (width p.hp.val z.val) i.val parents) :
    one pk a z children i parents ⦃ out =>
      RowPrefix (Value p sk pk a z.val) (width p.hp.val z.val) (i.val+1) out ⦄ := by
  have widthBound := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show p.hp.val-z.val ≤ 9 by have h := valid_hp_le p hp.valid; omega)
  have cast : (UScalar.cast .U32 i).val = i.val := UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by
    unfold width at hi; change i.val < 2^32; omega)
  obtain ⟨len,correct⟩ := hc
  obtain ⟨plen,prev⟩ := init
  have room := children.property
  change children.length ≤ Usize.max at room
  unfold one
  step with with_type_spec as ⟨a1,_,ha1⟩
  step with with_word2_spec as ⟨a2,ha2⟩
  simp only [lift,bind_ok]
  step with with_word3_spec as ⟨a3,ha3⟩
  step as ⟨il,hil⟩
  step as ⟨l,hl⟩
  step as ⟨ir,hir⟩
  step as ⟨r,hr⟩
  have pair := Shake.hash2_spec p hp pk a3 l r
  unfold shake.xmss.hash2 at pair
  step with pair as ⟨out,hout⟩
  step as ⟨s,hs⟩
  subst s
  refine ⟨by simp [plen],?_⟩
  intro j hj
  rw [Slice.set_val_eq,getElem!_pos _ _ (by simp; change j < parents.length; omega),List.getElem_set]
  split
  · rename_i eq; subst j
    have left := correct il.val (by omega)
    have right := correct ir.val (by omega)
    rw [getElem!_pos children.val il.val (by change il.val < children.length; omega),← hl,hil] at left
    rw [getElem!_pos children.val ir.val (by change ir.val < children.length; omega),← hr,hir,hil] at right
    have pred : z.val-1+1=z.val := by omega
    rw [hout,left,right]
    unfold Value
    conv_rhs => rw [← pred,Spec.xmssNode]
    simp [pred,ha3,ha2,ha1,adrsS,Spec.Adrs.setTypeAndClear,address.TREE,Spec.TREE,cast]
  · have hj' : j < parents.val.length := by change j < parents.length; omega
    simpa only [getElem!_pos parents.val j hj'] using prev j (by omega)

private theorem scalar_pairs {N : Usize} (p : params.Params) (hp : PN p N) (sk pk : Array U8 N)
    (a : address.Adrs) (z : U32) (pos : 0 < z.val) (hz : z.val ≤ p.hp.val)
    (count : Usize) (hc : count.val = width p.hp.val z.val)
    (children parents : Rows N) (childrenOk : Row children (2*width p.hp.val z.val) (Value p sk pk a (z.val-1)))
    (plen : parents.length = width p.hp.val z.val) :
    build_xmss_tree_loop0_loop0 ⟨0#usize,count⟩ pk a z children parents ⦃ out =>
      Row out parents.length (Value p sk pk a z.val) ⦄ := by
  unfold build_xmss_tree_loop0_loop0
  rw [show (fun (it,v) => build_xmss_tree_loop0_loop0.body pk a z children it v) =
    rangeBody (one pk a z children) from one_body ..]
  apply WP.spec_mono (row _ (RowPrefix (Value p sk pk a z.val) (width p.hp.val z.val)) count
    (fun i x hi h => one_spec p hp sk pk a z pos hz children x childrenOk i (hc ▸ hi) h)
    parents ⟨plen,by intro j hj; omega⟩)
  intro out h
  simpa only [RowPrefix,Row,hc,plen] using h

private noncomputable abbrev want {N : Usize} (p : params.Params) (sk pk : Array U8 N) (a : address.Adrs) :=
  expected p.hp.val (Value p sk pk a)

private theorem stage_spec {N : Usize} [b : Backend] (backend : Correct b N) (p : params.Params)
    (hp : PN p N) (sk pk : Array U8 N) (a : address.Adrs) (height z : U32)
    (heightEq : height.val = p.hp.val) (leaves : Usize) (leavesEq : leaves.val = 2^p.hp.val)
    (v : Nodes N) (pos : 0 < z.val) (hz : z.val ≤ p.hp.val)
    (init : Ready p.hp.val (want p sk pk a) (levelOff p.hp.val z.val) v) :
    stage height pk a leaves z v ⦃ v' =>
      Ready p.hp.val (want p sk pk a) (levelOff p.hp.val (z.val+1)) v' ⦄ := by
  have small := valid_hp_le p hp.valid
  have bits := System.Platform.numBits_eq
  unfold stage
  step as ⟨pred,hpred⟩
  step with offset height pred (by omega) (by omega) as ⟨prev,old⟩
  step with offset height z (by omega) (by omega) as ⟨cur,atRow⟩
  step with Usize.ShiftRight_spec leaves z (by scalar_tac) as ⟨count,hcount,_⟩
  rw [leavesEq,leafCount hz] at hcount
  rw [heightEq,hpred] at old
  rw [heightEq] at atRow
  change prev.val = levelOff p.hp.val (z.val-1) at old
  change cur.val = levelOff p.hp.val z.val at atRow
  have predEq : z.val-1+1=z.val := by omega
  have prevWidth : width p.hp.val (z.val-1) = 2*width p.hp.val z.val := by
    unfold width
    rw [show p.hp.val - (z.val-1) = (p.hp.val-z.val)+1 by omega,pow_succ,Nat.mul_comm]
  have cut := next (show z.val-1 ≤ p.hp.val by omega)
  rw [predEq,← atRow,← old,prevWidth] at cut
  have after : cur.val + count.val ≤ v.length := by
    have positive : 0 < width p.hp.val z.val := Nat.two_pow_pos _
    have := row_bound hz (show width p.hp.val z.val - 1 < width p.hp.val z.val by omega)
    rw [← atRow,← init.1] at this
    omega
  have vroom := v.property
  change v.length ≤ Usize.max at vroom
  simp only [lift,bind_ok,alloc.vec.Vec.deref_mut]
  step with core.slice.Slice.split_at_mut.spec v.slice cur (by change cur.val ≤ v.length; omega) as
    ⟨left,right,splitBack,clen,rlen,front,tail,restore⟩
  change right.length = v.length-cur.val at rlen
  step as ⟨twice,ht⟩
  step as ⟨stop,hstop⟩
  step as ⟨children,hchildren,childSize⟩
  step with core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec ⟨count⟩ right (by change count.val ≤ right.length; omega) as ⟨parents,parentBack,hparents,parentSize,replace⟩
  have childrenOk : Row children (2*width p.hp.val z.val) (Value p sk pk a (z.val-1)) := by
    refine ⟨by omega,?_⟩
    intro j hj
    rw [hchildren,List.getElem!_slice _ _ j left.val (by change _ ≤ left.length ∧ _; omega),front]
    have atFront : prev.val+j < cur.val := by omega
    have inVec : prev.val+j < v.val.length := by change prev.val+j < v.length; omega
    rw [getElem!_pos _ _ (by simpa [alloc.vec.Vec.val] using And.intro atFront inVec),List.getElem_take]
    change bytes v.val[prev.val+j].val = _
    have h := init.2 (prev.val+j) (by simpa [atRow] using atFront)
    rw [getElem!_pos v.val _ inVec] at h
    rw [h,old]
    exact expected_at _ (by omega) (by omega)
  obtain ⟨enabled,he⟩ := backend.detector
  rw [he,bind_ok]
  have finalize (new : Rows N) (rowOk : Row new parents.length (Value p sk pk a z.val)) :
      Ready p.hp.val (want p sk pk a) (levelOff p.hp.val (z.val+1))
        ⟨splitBack (left,parentBack new)⟩ := by
    have back := replace new
    have restoreLen : (parentBack new).length = v.slice.length-cur.val := by
      change ((parentBack new).val).length = _
      rw [back,List.length_setSlice!]
      exact rlen
    have ⟨buf,sz⟩ := restore left (parentBack new) clen restoreLen
    refine ⟨sz.trans init.1,?_⟩
    intro j hj
    change bytes (splitBack (left,parentBack new)).val[j]!.val = _
    rw [buf]
    by_cases first : j < cur.val
    · have hjl : j < left.val.length := by change j < left.length; omega
      have vj : j < v.slice.val.length := by change j < v.length; omega
      rw [List.getElem!_append_left _ _ _ hjl,front,getElem!_pos _ _ (by simpa using And.intro first vj),List.getElem_take]
      have before := init.2 j (atRow ▸ first)
      rw [getElem!_pos v.val j (by change j < v.length; omega)] at before
      simpa only [alloc.vec.Vec.val] using before
    · rw [next hz,← atRow,← hcount] at hj
      have inside : j-cur.val < new.length := by have := rowOk.1; omega
      have eq : j = cur.val + (j-cur.val) := by omega
      rw [List.getElem!_append_right _ _ _ (by change left.length ≤ j; omega),show left.val.length = cur.val from clen,
        back,slhdsa.setSlice0_getElem! _ _ _ inside (by change new.length ≤ right.length; have := rowOk.1; change right.length = v.length-cur.val at rlen; omega)]
      rw [rowOk.2 _ (by have := rowOk.1; omega)]
      have good := expected_at (Value p sk pk a) hz (show j-cur.val < width p.hp.val z.val by omega)
      rw [show levelOff p.hp.val z.val + (j-cur.val) = j by omega] at good
      exact good.symm
  cases enabled
  · simp only [Bool.false_eq_true,↓reduceIte]
    step with scalar_pairs p hp sk pk a z pos hz count hcount children parents childrenOk
      (parentSize.trans hcount) as ⟨new,okRow⟩
    exact finalize new okRow
  · simp only [↓reduceIte]
    step with backend.parents he p hp sk pk a z children parents pos hz childrenOk (parentSize.trans hcount)
      as ⟨new,okRow⟩
    exact finalize new okRow


/-- The extracted SHAKE builder establishes the cache invariant, with contracts only
on the two batched operations when the backend selects them. -/
theorem kernel {N : Usize} [b : Backend] (backend : Correct b N) (p : params.Params) (hp : PN p N) :
    CacheopsRust.cache.constructor.TreeKernel (@build_xmss_tree b N) (Shake.params p) := by
  intro height layer idx sk pk heightEq
  change height.val = p.hp.val at heightEq
  have small := valid_hp_le p hp.valid
  have bits := System.Platform.numBits_eq
  have cap : 2^height.val < Usize.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show height.val ≤ 9 by omega)
    scalar_tac
  unfold build_xmss_tree
  simp only [address.Adrs.new,address.Adrs.with_layer,address.Adrs.with_tree,bind_ok]
  let a : address.Adrs := ⟨layer,idx,0#u32,0#u32,0#u32,0#u32⟩
  step with Usize.ShiftLeft_spec 1#usize height (by scalar_tac) as ⟨leaves,hl,_⟩
  have leafEq : leaves.val = 2^p.hp.val := by rw [hl,Nat.one_shiftLeft,Nat.mod_eq_of_lt cap,heightEq]
  step with count_spec height (by omega) as ⟨count,hcount⟩
  rw [heightEq] at hcount
  have clone : (core.clone.CloneArray N core.clone.CloneU8).clone (Array.repeat N 0#u8) =
      ok (Array.repeat N 0#u8) := by
    obtain ⟨_,he,rfl⟩ := spec_imp_exists (core.array.CloneArray.clone_spec core.clone.CloneU8
      (Array.repeat N 0#u8) (by intros; rfl))
    exact he
  step with alloc.vec.from_elem_spec _ _ count clone as ⟨v,_,hv⟩
  have leafBound : leaves.val ≤ v.length := by
    rw [hv,hcount,leafEq,treeSize,pow_succ]
    have := Nat.two_pow_pos p.hp.val
    omega
  step with alloc.vec.Vec.index_mut_RangeTo_spec v ⟨leaves⟩ leafBound as ⟨slots,back,_,len,rewriteBack⟩
  step with fill_spec backend p hp sk pk a slots (len.trans leafEq) as ⟨filled,hf⟩
  step as ⟨it,start,stop,fresh⟩
  have h1 : levelOff p.hp.val 1 = 2^p.hp.val := by
    rw [show 1=0+1 by rfl,next (by omega : 0 ≤ p.hp.val)]
    simp [levelOff,width]
  have init : Ready p.hp.val (want p sk pk a) (levelOff p.hp.val 1) (back filled) := by
    constructor
    · change (back filled).val.length = _
      rw [rewriteBack,List.length_setSlice!]
      exact hv.trans hcount
    · intro j hj
      rw [h1] at hj
      have hfill : j < filled.val.length := by change j < filled.length; have := hf.1; omega
      rw [rewriteBack,slhdsa.setSlice0_getElem! _ _ _ hfill (by change filled.length ≤ v.length; have := hf.1; omega),
        hf.2 j (by omega)]
      have eq := expected_at (Value p sk pk a) (by omega : 0 ≤ p.hp.val)
        (show j < width p.hp.val 0 by simpa [width] using hj)
      simpa only [levelOff,Nat.sub_zero,Nat.sub_self,Nat.zero_add] using eq.symm
  unfold build_xmss_tree_loop0
  rw [show (fun (it1,v') => build_xmss_tree_loop0.body height pk a leaves it1 v') =
    inclusiveBody (stage height pk a leaves) from stage_body ..]
  have nz := hp.valid.hp_pos
  change 1 ≤ p.hp.val at nz
  step with levels _ (fun z => Ready p.hp.val (want p sk pk a) (levelOff p.hp.val z)) height
    (by omega) (fun z x pos bound => stage_spec backend p hp sk pk a height z heightEq leaves leafEq
      x pos (by omega)) it start stop fresh (back filled) init as ⟨v2,hv2⟩
  have bound : levelOff p.hp.val (height.val+1) = treeSize p.hp.val := by simp [heightEq,levelOff,treeSize]
  obtain ⟨len,hx⟩ := hv2
  rw [bound] at hx
  have hb := contents (v:=v2) (Shake.params p) (bytes sk.val) (bytes pk.val) (adrsS a) hx
  exact ⟨len,by simpa [a,adrsS,layerAdrs,Spec.Adrs.zero] using hb⟩

end slhdsa.cache.builder.nativeShake
