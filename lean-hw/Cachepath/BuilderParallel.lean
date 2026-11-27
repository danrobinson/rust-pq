import Cachepath.BuilderParallelProgram
import Cachepath.BuiltSession
open Aeneas Aeneas.Std Result
open slhdsa.cache.endtoend
namespace slhdsa.cache.builder.workers
set_option linter.concreteInstances false

/-- A caller may fall back even if its parallel attempt touched the destination:
only its extent must survive a declined fill. Successful fills owe each WOTS leaf. -/
structure Correct (pool : Pool) (N : Usize) : Prop where
  sha2 : ∀ (p : params.Params) (_ : PN p N) (sk : Array U8 N) (seed : hash.Seed N) (_ : SeedOk seed)
    (a : address.Adrs) (leaves : Usize) (out : nativeShake.Rows N), leaves.val = 2^p.hp.val →
    out.length = leaves.val → @Pool.sha2 pool N leaves sk seed a out ⦃ result =>
      result.2.length = out.length ∧ (result.1 = true → ∀ i < out.length,
      bytes result.2.val[i]!.val = Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val)
        {(adrsS a).setTypeAndClear Spec.WOTS_HASH with keypair := i}) ⦄
  shake : ∀ (p : params.Params) (_ : PN p N) (sk pk : Array U8 N)
    (a : address.Adrs) (leaves : Usize) (out : nativeShake.Rows N), leaves.val = 2^p.hp.val →
    out.length = leaves.val → @Pool.shake pool N leaves sk pk a out ⦃ result =>
      result.2.length = out.length ∧ (result.1 = true → ∀ i < out.length,
      bytes result.2.val[i]!.val = nativeShake.Value p sk pk a 0 i) ⦄

private theorem install {N : Usize} {H : Nat} (v : Nodes N) (written : nativeShake.Rows N)
    (result : Nodes N) (node : Nat → Nat → Spec.Bytes)
    (vlen : v.length = treeSize H) (wsize : written.length = 2^H)
    (copy : result.val = v.val.setSlice! 0 written.val)
    (correct : ∀ i < written.length, bytes written.val[i]!.val = node 0 i) :
    Ready H (expected H node) (2^H) result := by
  have room : written.length ≤ v.length := by
    rw [vlen,wsize,treeSize,pow_succ]; have := Nat.two_pow_pos H; omega
  refine ⟨by change result.val.length = _; rw [copy,List.length_setSlice!]; exact vlen,?_⟩
  intro i hi
  have h := correct i (by omega)
  rw [copy,slhdsa.setSlice0_getElem! _ _ _ (by change i < written.length; omega) room,h]
  have eq := expected_at node (by omega : 0 ≤ H) (show i < width H 0 by simpa [width] using hi)
  simpa only [levelOff,Nat.sub_zero,Nat.sub_self,Nat.zero_add] using eq.symm

private theorem sha2Levels {N : Usize} (p : params.Params) (hp : PN p N) (height : U32) (h : height.val=p.hp.val)
    (sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (leaves : Usize)
    (hl : leaves.val=2^p.hp.val) (v : Nodes N) (init : Ready p.hp.val (target p sk seed a) (2^p.hp.val) v) :
    (do let it ← core.ops.range.RangeInclusive.new 1#u32 height
        sha2_ops.build_xmss_tree_loop1 it height seed a leaves v) ⦃ out =>
      out.length = treeSize p.hp.val ∧ Built out.deref (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  step as ⟨it,start,stop,fresh⟩
  unfold sha2_ops.build_xmss_tree_loop1
  rw [show (fun (it1,v') => sha2_ops.build_xmss_tree_loop1.body height seed a leaves it1 v') =
    inclusiveBody (level height seed a leaves) from level_body ..]
  have h1 : levelOff p.hp.val 1 = 2^p.hp.val := by
    rw [show 1=0+1 by rfl,next (by omega : 0 ≤ p.hp.val)]
    simp [levelOff,width]
  have nz := hp.valid.hp_pos
  change 1 ≤ p.hp.val at nz
  step with levels _ (fun z => Ready p.hp.val (target p sk seed a) (levelOff p.hp.val z)) height
    (by omega) (fun z x pos bound => level_spec p hp sk seed hs a height z h leaves hl x pos (by omega))
    it start stop fresh v (h1 ▸ init) as ⟨out,ready⟩
  obtain ⟨len,ok⟩ := ready
  rw [show levelOff p.hp.val (height.val+1) = treeSize p.hp.val by simp [h,levelOff,treeSize]] at ok
  exact ⟨len,contents _ _ _ _ ok⟩

private theorem shakeLevels {N : Usize} [b : nativeShake.Backend] (kernels : nativeShake.Correct b N)
    (p : params.Params) (hp : PN p N) (height : U32) (h : height.val=p.hp.val)
    (sk pk : Array U8 N) (a : address.Adrs) (leaves : Usize) (hl : leaves.val=2^p.hp.val)
    (v : Nodes N) (init : Ready p.hp.val (nativeShake.want p sk pk a) (2^p.hp.val) v) :
    (do let it ← core.ops.range.RangeInclusive.new 1#u32 height
        nativeShake.build_xmss_tree_loop0 it height pk a leaves v) ⦃ out =>
      out.length = treeSize p.hp.val ∧ Built out.deref (Shake.params p) (bytes sk.val) (bytes pk.val) (adrsS a) ⦄ := by
  step as ⟨it,start,stop,fresh⟩
  unfold nativeShake.build_xmss_tree_loop0
  rw [show (fun (it1,v') => nativeShake.build_xmss_tree_loop0.body height pk a leaves it1 v') =
    inclusiveBody (nativeShake.stage height pk a leaves) from nativeShake.stage_body ..]
  have h1 : levelOff p.hp.val 1 = 2^p.hp.val := by
    rw [show 1=0+1 by rfl,next (by omega : 0 ≤ p.hp.val)]
    simp [levelOff,width]
  have nz := hp.valid.hp_pos
  change 1 ≤ p.hp.val at nz
  step with levels _ (fun z => Ready p.hp.val (nativeShake.want p sk pk a) (levelOff p.hp.val z)) height
    (by omega) (fun z x pos bound => nativeShake.stage_spec kernels p hp sk pk a height z h leaves hl x pos (by omega))
    it start stop fresh v (h1 ▸ init) as ⟨out,ready⟩
  obtain ⟨len,ok⟩ := ready
  rw [show levelOff p.hp.val (height.val+1) = treeSize p.hp.val by simp [h,levelOff,treeSize]] at ok
  exact ⟨len,contents _ _ _ _ ok⟩


theorem sha2_kernel {N : Usize} [pool : Pool] (workers : Correct pool N) (p : params.Params) (hp : PN p N) :
    CacheopsRust.cache.constructor.TreeKernel (@sha2Tree pool N) (paramsS p) := by
  intro height layer idx sk pk heightEq
  change height.val = p.hp.val at heightEq
  have small := valid_hp_le p hp.valid
  have cap : 2^height.val < Usize.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show height.val ≤ 9 by omega)
    scalar_tac
  unfold sha2Tree
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

  have total := hv.trans hcount
  have leafBound : leaves.val ≤ v.length := by
    rw [total,leafEq,treeSize,pow_succ]; have := Nat.two_pow_pos p.hp.val; omega
  step with alloc.vec.Vec.index_mut_RangeTo_spec v ⟨leaves⟩ leafBound as ⟨slots,back,_,len,copy⟩
  step with workers.sha2 p hp sk seed hs a leaves slots leafEq len as ⟨built,filled,flen,correct⟩
  have written : filled.length = 2^p.hp.val := flen.trans (len.trans leafEq)
  have finish (x : Nodes N) (ready : Ready p.hp.val (target p sk seed a) (2^p.hp.val) x) :=
    sha2Levels p hp height heightEq sk seed hs a leaves leafEq x ready
  cases built with
  | true =>
    simp only [↓reduceIte]
    have rowOk := install v filled (back filled) (fun z j => Spec.xmssNode (paramsS p) (bytes sk.val) j z (bytes seed.pk_seed.val) (adrsS a)) total written (copy filled)
      (fun i hi => by simpa [Spec.xmssNode] using correct rfl i (flen ▸ hi))
    simpa [hpk,a,adrsS,layerAdrs,Spec.Adrs.zero,show (paramsS p).hp = p.hp.val from rfl] using finish (back filled) rowOk
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    unfold sha2_ops.build_xmss_tree_loop0
    rw [show (fun (it,v') => sha2_ops.build_xmss_tree_loop0.body sk seed a it v') =
      rangeBody (leaf sk seed a) from leaf_body ..]
    have size : (back filled).length = treeSize p.hp.val := by
      change (back filled).val.length = _
      rw [copy,List.length_setSlice!]; exact total
    step with row _ (Ready p.hp.val (target p sk seed a)) leaves
      (fun i x hi => leaf_spec p hp sk seed hs a i x (by simpa [width,leafEq] using hi)) (back filled)
      ⟨size,by intro j hj; omega⟩ as ⟨v1,ok⟩
    simpa [hpk,a,adrsS,layerAdrs,Spec.Adrs.zero,show (paramsS p).hp = p.hp.val from rfl] using finish v1 (leafEq ▸ ok)

theorem shake_kernel {N : Usize} [pool : Pool] [backend : nativeShake.Backend] (workers : Correct pool N) (kernels : nativeShake.Correct backend N) (p : params.Params) (hp : PN p N) :
    CacheopsRust.cache.constructor.TreeKernel (@shakeTree pool backend N) (Shake.params p) := by
  intro height layer idx sk pk heightEq
  change height.val = p.hp.val at heightEq
  have small := valid_hp_le p hp.valid
  have cap : 2^height.val < Usize.size := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show height.val ≤ 9 by omega)
    scalar_tac
  unfold shakeTree
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

  have total := hv.trans hcount
  have leafBound : leaves.val ≤ v.length := by
    rw [total,leafEq,treeSize,pow_succ]; have := Nat.two_pow_pos p.hp.val; omega
  step with alloc.vec.Vec.index_mut_RangeTo_spec v ⟨leaves⟩ leafBound as ⟨slots,back,_,len,copy⟩
  step with workers.shake p hp sk pk a leaves slots leafEq len as ⟨built,filled,flen,correct⟩
  have written : filled.length = 2^p.hp.val := flen.trans (len.trans leafEq)
  have sourceLen : (back filled).length = treeSize p.hp.val := by
    change (back filled).val.length = _
    rw [copy,List.length_setSlice!]; exact total
  have choose :
      (if built then ok (back filled) else do
        let (s,write) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))
          (back filled) ⟨leaves⟩
        let fresh ← nativeShake.fill_leaves_chunk sk pk a 0#usize s
        ok (write fresh)) ⦃ x => Ready p.hp.val (nativeShake.want p sk pk a) (2^p.hp.val) x ⦄ := by
    cases built with
    | true =>
      simp only [↓reduceIte,WP.spec_ok]
      exact install v filled _ _ total written (copy filled) (fun i hi => correct rfl i (flen ▸ hi))
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte]
      step with alloc.vec.Vec.index_mut_RangeTo_spec (back filled) ⟨leaves⟩ (by change leaves.val ≤ _; omega)
        as ⟨s,write,_,sz,copy'⟩
      step with nativeShake.fill_spec kernels p hp sk pk a s (sz.trans leafEq) as ⟨fresh,rowOk⟩
      exact install _ fresh _ _ sourceLen (rowOk.1.trans (sz.trans leafEq)) (copy' fresh)
        (fun i hi => rowOk.2 i (rowOk.1 ▸ hi))
  step with choose as ⟨out,ready⟩
  simpa [a,adrsS,layerAdrs,Spec.Adrs.zero,show (Shake.params p).hp = p.hp.val from rfl] using
    shakeLevels kernels p hp height heightEq sk pk a leaves leafEq out ready

end slhdsa.cache.builder.workers

open slhdsa
namespace CacheopsRust.Public
variable [backend : Closed.Backend] [pool : slhdsa.cache.builder.workers.Pool]
  [trees : slhdsa.cache.builder.nativeShake.Backend]
local instance (N : Usize) : Builders N :=
  ⟨slhdsa.cache.builder.workers.sha2Tree, slhdsa.cache.builder.workers.shakeTree⟩

/-- Repeated public cached calls in a parallel-feature build, conditional on
the worker leaf fill and any selected SHAKE accelerator operations. -/
theorem parallel_build_and_sign_many {N : Usize} [Closed.DispatchCorrect backend N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) (family : CacheopsRust.cache.HashFamily)
    (workers : slhdsa.cache.builder.workers.Correct pool N)
    (shakeKernels : family = .Shake → slhdsa.cache.builder.nativeShake.Correct trees N)
    (capacity : Usize) (sk : Slice U8) (hs : sk.length = 4*N.val)
    (key : Spec.KeyOk (familyParams p family) (bytes sk.val)) (qs : List (Request N))
    (room : ∀ q ∈ qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) :
    (do let c ← CacheopsRust.cache.constructor.newCache N slhdsa.cache.builder.workers.sha2Tree
          slhdsa.cache.builder.workers.shakeTree family p sk
        let c' ← CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity c capacity
        runRequests p sk c' qs) ⦃ out =>
      out.1.map (fun v => v.map fun sig => bytes sig.val) = qs.map (requestSpec (familyParams p family) sk) ∧
      out.2.family = family ∧ out.2.layer_d2_capacity = capacity ∧
      slhdsa.cache.endtoend.CacheValid out.2 (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
        (Spec.block (familyParams p family) (bytes sk.val) 2) ⦄ := by
  apply new_then_sign_many p hp family _ _ capacity sk hs key qs room
  · rintro rfl; exact slhdsa.cache.builder.workers.sha2_kernel workers _ hp
  · rintro rfl; exact slhdsa.cache.builder.workers.shake_kernel workers (shakeKernels rfl) _ hp

end CacheopsRust.Public
