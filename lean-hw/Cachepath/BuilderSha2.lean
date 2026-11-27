import Cachepath.BuilderSteps

open Aeneas Aeneas.Std Result
open slhdsa.cache.endtoend
namespace slhdsa.cache.builder
open sha2_ops

noncomputable abbrev target {N : Usize} (p : params.Params) (sk : Array U8 N) (seed : hash.Seed N)
    (a : address.Adrs) := expected p.hp.val (fun z i =>
      Spec.xmssNode (paramsS p) (bytes sk.val) i z (bytes seed.pk_seed.val) (adrsS a))

def Ready {N : Usize} (H : Nat) (f : Nat → Spec.Bytes) (k : Nat) (v : Nodes N) :=
  v.length = treeSize H ∧ Prefix v f k

private theorem nativeCast (i : Usize) {H z} (small : H ≤ 9) (hi : i.val < width H z) :
    (UScalar.cast .U32 i).val = i.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  have := Nat.pow_le_pow_right (by decide : 0 < 2) (show H-z ≤ 9 by omega)
  unfold width at hi
  change i.val < 2^32
  omega

theorem leaf_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed)
    (a : address.Adrs) (i : Usize) (v : Nodes N) (hi : i.val < width p.hp.val 0)
    (init : Ready p.hp.val (target p sk seed a) i.val v) :
    leaf sk seed a i v ⦃ v' => Ready p.hp.val (target p sk seed a) (i.val+1) v' ⦄ := by
  have bound := row_bound (by omega : 0 ≤ p.hp.val) hi
  simp only [levelOff,Nat.sub_zero,Nat.sub_self,Nat.zero_add] at bound
  have cast := nativeCast i (valid_hp_le p hp.valid) hi
  unfold leaf
  step with with_type_spec as ⟨a1,_,ha1⟩
  simp only [lift,bind_ok]
  step with with_keypair_spec as ⟨a2,ha2⟩
  step with wots_pk_gen_spec p hp sk seed hs a2 as ⟨out,hout⟩
  step with alloc.vec.Vec.index_mut_usize_spec v i (init.1 ▸ bound) as ⟨_,back,_,hback⟩
  rw [hback]
  refine ⟨(alloc.vec.Vec.set_length ..).trans init.1, set_prefix (init.1 ▸ bound) init.2 ?_⟩
  have eq := expected_at (fun z j => Spec.xmssNode (paramsS p) (bytes sk.val) j z
    (bytes seed.pk_seed.val) (adrsS a)) (by omega : 0 ≤ p.hp.val) hi
  simp only [levelOff,Nat.sub_zero,Nat.sub_self,Nat.zero_add] at eq
  unfold target
  rw [hout,eq]
  simp [Spec.xmssNode,ha2,ha1,Spec.Adrs.setTypeAndClear,adrsS,address.WOTS_HASH,Spec.WOTS_HASH,cast]

private theorem parent_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (z : U32) (prev cur i : Usize)
    (v : Nodes N) (pos : 0 < z.val) (hz : z.val ≤ p.hp.val) (hi : i.val < width p.hp.val z.val)
    (old : prev.val = levelOff p.hp.val (z.val-1)) (atRow : cur.val = levelOff p.hp.val z.val)
    (init : Ready p.hp.val (target p sk seed a) (cur.val+i.val) v) :
    parent seed a z prev cur i v ⦃ v' => Ready p.hp.val (target p sk seed a) (cur.val+(i.val+1)) v' ⦄ := by
  have hz' : z.val - 1 + 1 = z.val := by omega
  have prevWidth : width p.hp.val (z.val-1) = width p.hp.val z.val * 2 := by
    simp only [width]
    rw [show p.hp.val - (z.val-1) = (p.hp.val-z.val)+1 by omega, pow_succ]
  have boundary := next (show z.val-1 ≤ p.hp.val by omega)
  rw [hz',← atRow,← old,prevWidth] at boundary
  have bound := row_bound hz hi
  rw [← atRow,← init.1] at bound
  have room := v.property
  change v.length ≤ Usize.max at room
  have cast := nativeCast i (valid_hp_le p hp.valid) hi
  unfold parent
  step with with_type_spec as ⟨a1,_,ha1⟩
  step with with_word2_spec as ⟨a2,ha2⟩
  simp only [lift,bind_ok]
  step with with_word3_spec as ⟨a3,ha3⟩
  step as ⟨two,h2⟩
  step as ⟨il,hil⟩
  step with alloc.vec.Vec.index_usize_spec v il (by omega) as ⟨l,hl⟩
  step as ⟨il',hil'⟩
  step as ⟨ir,hir⟩
  step with alloc.vec.Vec.index_usize_spec v ir (by omega) as ⟨r,hr⟩
  step with hash2_spec p hp seed hs a3 l r as ⟨out,hout⟩
  step as ⟨dst,hdst⟩
  step with alloc.vec.Vec.index_mut_usize_spec v dst (by omega) as ⟨_,back,_,hback⟩
  rw [hback]
  have right : ir.val = prev.val + (2*i.val+1) := by omega
  have left : il.val = prev.val + 2*i.val := by omega
  have children (j : Usize) (index : Nat) (ix : j.val = prev.val+index)
      (size : index < width p.hp.val (z.val-1)) :
      bytes v.val[j.val]!.val = Spec.xmssNode (paramsS p) (bytes sk.val) index
        (z.val-1) (bytes seed.pk_seed.val) (adrsS a) := by
    have h := init.2 j.val (by omega)
    rw [h,ix,old]
    exact expected_at _ (by omega) size
  have lvalue := children il (2*i.val) left (by omega)
  have rvalue := children ir (2*i.val+1) right (by omega)
  rw [getElem!_pos v.val il.val (by change il.val < v.length; omega),← hl] at lvalue
  rw [getElem!_pos v.val ir.val (by change ir.val < v.length; omega),← hr] at rvalue
  refine ⟨(alloc.vec.Vec.set_length ..).trans init.1, ?_⟩
  have eq : cur.val+(i.val+1) = dst.val+1 := by omega
  rw [eq]
  apply set_prefix (by omega) (hdst ▸ init.2)
  unfold target
  rw [hdst,atRow,expected_at _ hz hi,hout,lvalue,rvalue]
  conv_rhs => rw [← hz',Spec.xmssNode]
  simp [hz',ha3,ha2,ha1,adrsS,Spec.Adrs.setTypeAndClear,address.TREE,Spec.TREE,cast]


theorem leafCount {H z : Nat} (hz : z ≤ H) : 2^H >>> z = width H z := by
  rw [Nat.shiftRight_eq_div_pow,← Nat.sub_add_cancel hz, Nat.pow_add, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  simp [width]

theorem level_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (height z : U32)
    (heightEq : height.val = p.hp.val) (leaves : Usize) (leavesEq : leaves.val = 2^p.hp.val)
    (v : Nodes N) (pos : 0 < z.val) (hz : z.val ≤ p.hp.val)
    (init : Ready p.hp.val (target p sk seed a) (levelOff p.hp.val z.val) v) :
    level height seed a leaves z v ⦃ v' =>
      Ready p.hp.val (target p sk seed a) (levelOff p.hp.val (z.val+1)) v' ⦄ := by
  have small := valid_hp_le p hp.valid
  unfold level
  step as ⟨pred,hpred⟩
  step with offset height pred (by omega) (by omega) as ⟨prev,old⟩
  step with offset height z (by omega) (by omega) as ⟨cur,atRow⟩
  have bits := System.Platform.numBits_eq
  step with Usize.ShiftRight_spec leaves z (by scalar_tac) as ⟨count,hcount,_⟩
  rw [leavesEq,leafCount hz] at hcount
  rw [heightEq,hpred] at old
  rw [heightEq] at atRow
  change prev.val = levelOff p.hp.val (z.val-1) at old
  change cur.val = levelOff p.hp.val z.val at atRow
  unfold build_xmss_tree_loop1_loop0
  rw [show (fun (iter1,nodes1) => build_xmss_tree_loop1_loop0.body seed a z prev cur iter1 nodes1) =
    rangeBody (parent seed a z prev cur) from parent_body ..]
  step with row _ (fun i => Ready p.hp.val (target p sk seed a) (cur.val+i)) count
    (fun i x hi => parent_spec p hp sk seed hs a z prev cur i x pos hz (hcount ▸ hi) old atRow)
    v (by simpa [atRow] using init) as ⟨v',hv'⟩
  simpa only [next hz,atRow,hcount] using hv'

theorem count_spec (hp : U32) (h : hp.val ≤ 9) :
    tree_node_count hp ⦃ n => n.val = treeSize hp.val ⦄ := by
  have small : 2^(hp.val+1) < Usize.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show hp.val+1 ≤ 10 by omega)
    scalar_tac
  unfold tree_node_count
  step as ⟨z,hz⟩
  have bits := System.Platform.numBits_eq
  step with Usize.ShiftLeft_spec 1#usize z (by scalar_tac) as ⟨n,hn,_⟩
  have hn' : n.val = 2^(hp.val+1) := by rw [hn,hz,Nat.one_shiftLeft,Nat.mod_eq_of_lt small]
  have pos := Nat.two_pow_pos (hp.val+1)
  step as ⟨total,ht⟩
  exact ht.trans (by rw [hn']; rfl)

/-- The extracted serial SHA-2 tree builder uses the verified WOTS, hash2 and seed
bodies on every node. This discharges its tree-kernel contract at every layer and index. -/
theorem sha2_kernel {N : Usize} (p : params.Params) (hp : PN p N) :
    CacheopsRust.cache.constructor.TreeKernel (@build_xmss_tree N) (paramsS p) := by
  intro height layer idx sk pk heightEq
  change height.val = p.hp.val at heightEq
  have small := valid_hp_le p hp.valid
  have cap : 2^height.val < Usize.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show height.val ≤ 9 by omega)
    scalar_tac
  unfold build_xmss_tree
  step with seed_ctx_spec hp.nok pk as ⟨seed,hpk,hs⟩
  simp only [address.Adrs.new,address.Adrs.with_layer,address.Adrs.with_tree,bind_ok]
  let a : address.Adrs := ⟨layer,idx,0#u32,0#u32,0#u32,0#u32⟩
  have bits := System.Platform.numBits_eq
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
  unfold build_xmss_tree_loop0
  rw [show (fun (it,v') => build_xmss_tree_loop0.body sk seed a it v') =
    rangeBody (leaf sk seed a) from leaf_body ..]
  step with row _ (Ready p.hp.val (target p sk seed a)) leaves
    (fun i x hi => leaf_spec p hp sk seed hs a i x (by simpa [width,leafEq] using hi))
    v ⟨hv.trans hcount,by intro j hj; omega⟩ as ⟨v1,hv1⟩
  step as ⟨it,start,stop,fresh⟩
  have h1 : levelOff p.hp.val 1 = 2^p.hp.val := by
    rw [show 1=0+1 by rfl,next (by omega : 0 ≤ p.hp.val)]
    simp [levelOff,width]
  unfold build_xmss_tree_loop1
  rw [show (fun (it1,v') => build_xmss_tree_loop1.body height seed a leaves it1 v') =
    inclusiveBody (level height seed a leaves) from level_body ..]
  have nz := hp.valid.hp_pos
  change 1 ≤ p.hp.val at nz
  step with levels _ (fun z => Ready p.hp.val (target p sk seed a) (levelOff p.hp.val z))
    height (by omega) (fun z x pos bound => level_spec p hp sk seed hs a height z heightEq
      leaves leafEq x pos (by omega)) it start stop fresh v1 (by rw [h1,← leafEq]; exact hv1)
    as ⟨v2,hv2⟩
  have bound : levelOff p.hp.val (height.val+1) = treeSize p.hp.val := by simp [heightEq,levelOff,treeSize]
  obtain ⟨len,hx⟩ := hv2
  rw [bound] at hx
  have hb := contents (v:=v2) (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) hx
  exact ⟨len,by simpa [hpk,a,adrsS,layerAdrs,Spec.Adrs.zero] using hb⟩

end slhdsa.cache.builder
