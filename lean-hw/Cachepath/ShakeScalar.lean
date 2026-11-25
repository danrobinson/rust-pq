import Cachepath.ShakeScalarProgram
import Cachepath.ShakeXmss
import Slhdsa.Proofs.ShakeFors

open Aeneas Aeneas.Std Result slhdsa
namespace slhdsa.CacheScalar

private theorem bind_same {α β : Type} (m : Result α) (f g : α → Result β)
    (h : ∀ x, f x = g x) : Std.bind m f = Std.bind m g := congrArg (Std.bind m) (funext h)

private abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32)

private def cursor (v : alloc.vec.Vec U32) (i : Usize) : Iter :=
  ⟨⟨alloc.vec.Vec.deref v, i.val⟩, i⟩

private theorem next_some (v : alloc.vec.Vec U32) (i : Usize) (h : i.val < v.length) :
    ∃ j : Usize, i + 1#usize = ok j ∧ j.val = i.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next (core.iter.traits.iterator.IteratorSliceIter U32)
          (cursor v i) = ok (some (i,v.val[i.val]), cursor v j) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) v i = ok v.val[i.val] := by
  obtain ⟨j,add,hj⟩ := spec_imp_exists (Usize.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
  have bound : i.val < (alloc.vec.Vec.deref v).len := by simpa [Slice.length, alloc.vec.Vec.length, vec_deref_val] using h
  refine ⟨j,add,hj,?_,?_⟩
  · simp only [cursor,core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next,bound,
      ↓reduceDIte, bind_ok, uncurry, add,hj]
    simp
    exact getElem_congr_coll (i := i.val) (w := by simpa [vec_deref_val] using h) (vec_deref_val v)
  · rw [alloc.vec.Vec.index_slice_index]
    obtain ⟨x,hx,rfl⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec v i h)
    exact hx

private theorem next_none (v : alloc.vec.Vec U32) (i : Usize) (h : ¬i.val < v.length) :
    core.iter.adapters.enumerate.IteratorEnumerate.next (core.iter.traits.iterator.IteratorSliceIter U32)
      (cursor v i) = ok (none, cursor v i) := by
  have stop : ¬i.val < (alloc.vec.Vec.deref v).len := by simpa [Slice.length, alloc.vec.Vec.length, vec_deref_val] using h
  simp only [cursor,core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorSliceIter.next,stop,
    ↓reduceDIte, bind_ok, uncurry]

private theorem wots_sign_loop {N : Usize} (sk seed : Array U8 N) (a : address.Adrs)
    (digits : alloc.vec.Vec U32) (sig : alloc.vec.Vec U8) (i : Usize) :
    cache.shake_ops.wots_sign_loop (cursor digits i) sk seed a sig =
      shake.wots.wots_sign_loop sk seed a digits sig i := by
  unfold cache.shake_ops.wots_sign_loop shake.wots.wots_sign_loop
  conv_lhs => rw [loop.eq_def]
  conv_rhs => rw [loop.eq_def]
  simp only [cache.shake_ops.wots_sign_loop.body, shake.wots.wots_sign_loop.body]
  by_cases h : i.val < digits.length
  · obtain ⟨j,add,hj,step,index⟩ := next_some digits i h
    have lt : i < alloc.vec.Vec.len digits := h
    simp only [step, index, add, lt, ↓reduceIte, uncurry, bind_ok, Std.bind_assoc]
    iterate 6 (apply bind_same; intro x)
    exact wots_sign_loop sk seed a digits _ j
  · have stop : ¬i < alloc.vec.Vec.len digits := h
    simp only [next_none digits i h, stop, ↓reduceIte, uncurry, bind_ok]
termination_by digits.length - i.val
decreasing_by omega

private theorem wots_pk_from_sig_loop {N : Usize} (sig : Slice U8) (seed : Array U8 N)
    (a : address.Adrs) (digits : alloc.vec.Vec U32) (pk : shake256.Sponge) (i : Usize) :
    cache.shake_ops.wots_pk_from_sig_loop (cursor digits i) sig seed a.layer a.tree a.typ a.keypair a.word2 a.word3 pk =
      shake.wots.wots_pk_from_sig_loop sig seed a.layer a.tree a.typ a.keypair a.word2 a.word3 digits pk i := by
  unfold cache.shake_ops.wots_pk_from_sig_loop shake.wots.wots_pk_from_sig_loop
  conv_lhs => rw [loop.eq_def]
  conv_rhs => rw [loop.eq_def]
  simp only [cache.shake_ops.wots_pk_from_sig_loop.body, shake.wots.wots_pk_from_sig_loop.body]
  by_cases h : i.val < digits.length
  · obtain ⟨j,add,hj,step,index⟩ := next_some digits i h
    have lt : i < alloc.vec.Vec.len digits := h
    simp only [step, index, add, lt, ↓reduceIte, uncurry, bind_ok, Std.bind_assoc]
    repeat' (apply bind_same; intro x)
    exact wots_pk_from_sig_loop sig seed a digits _ j
  · have stop : ¬i < alloc.vec.Vec.len digits := h
    simp only [next_none digits i h, stop, ↓reduceIte, uncurry, bind_ok]
termination_by digits.length - i.val
decreasing_by omega

private theorem fors_pk_from_sig_loop {N : Usize} (height : U32) (sig : Slice U8) (seed : Array U8 N)
    (a : address.Adrs) (digits : alloc.vec.Vec U32) (pk : shake256.Sponge) (i : Usize) :
    cache.shake_ops.fors_pk_from_sig_loop (cursor digits i) height sig seed a.layer a.tree a.typ a.keypair a.word2 a.word3 pk =
      shake.fors.fors_pk_from_sig_loop height sig seed a.layer a.tree a.typ a.keypair a.word2 a.word3 digits pk i := by
  unfold cache.shake_ops.fors_pk_from_sig_loop shake.fors.fors_pk_from_sig_loop
  conv_lhs => rw [loop.eq_def]
  conv_rhs => rw [loop.eq_def]
  simp only [cache.shake_ops.fors_pk_from_sig_loop.body, shake.fors.fors_pk_from_sig_loop.body]
  by_cases h : i.val < digits.length
  · obtain ⟨j,add,hj,step,index⟩ := next_some digits i h
    have lt : i < alloc.vec.Vec.len digits := h
    simp only [step, index, add, lt, ↓reduceIte, uncurry, bind_ok, Std.bind_assoc]
    repeat' (apply bind_same; intro x)
    exact fors_pk_from_sig_loop height sig seed a digits _ j
  · have stop : ¬i < alloc.vec.Vec.len digits := h
    simp only [next_none digits i h, stop, ↓reduceIte, uncurry, bind_ok]
termination_by digits.length - i.val
decreasing_by omega

private theorem fors_path {N : Usize} (sk seed : Array U8 N) (a : address.Adrs)
    (it : core.ops.range.Range U32) (height : U32) (stop : it.end = height)
    (sig : alloc.vec.Vec U8) (idx tree : U32) :
    cache.shake_ops.fors_sign_loop0_loop0 it height sk seed a sig idx tree =
      shake.fors.fors_sign_loop0_loop0 sk seed a height sig tree idx it.start := by
  unfold cache.shake_ops.fors_sign_loop0_loop0 shake.fors.fors_sign_loop0_loop0
  conv_lhs => rw [loop.eq_def]
  conv_rhs => rw [loop.eq_def]
  simp only [cache.shake_ops.fors_sign_loop0_loop0.body,shake.fors.fors_sign_loop0_loop0.body]
  by_cases more : it.start.val < it.end.val
  · obtain ⟨⟨o,nxt⟩,step,ho,hn,hen⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec it more)
    have lt : it.start < height := by subst height; exact more
    have room : it.start.val + 1 ≤ U32.max := by scalar_tac
    obtain ⟨j,add,hj⟩ := spec_imp_exists (U32.add_spec (x:=it.start) (y:=1#u32) room)
    have jn : j = nxt.start := by scalar_tac
    subst o
    simp only [step, uncurry, bind_ok, lt, ↓reduceIte, Std.bind_assoc, add,jn]
    repeat' (apply bind_same; intro x)
    exact fors_path sk seed a nxt height (hen.trans stop) _ idx tree
  · obtain ⟨⟨o,nxt⟩,step,ho,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by omega))
    have no : ¬it.start < height := by subst height; exact more
    subst o
    simp only [step,uncurry,bind_ok,no,↓reduceIte]
termination_by it.end.val-it.start.val
decreasing_by rw [hen,hn]; omega

private theorem fors_outer {N : Usize} (k height : U32) (sk seed : Array U8 N)
    (a : address.Adrs) (indices : alloc.vec.Vec U32) (len : indices.length = k.val)
    (sig : alloc.vec.Vec U8) (i : U32) (u : Usize) (count : u.val = i.val) :
    cache.shake_ops.fors_sign_loop0 (cursor indices u) height sk seed a sig =
      shake.fors.fors_sign_loop0 k sk seed a height indices sig i := by
  unfold cache.shake_ops.fors_sign_loop0 shake.fors.fors_sign_loop0
  conv_lhs => rw [loop.eq_def]
  conv_rhs => rw [loop.eq_def]
  simp only [cache.shake_ops.fors_sign_loop0.body,shake.fors.fors_sign_loop0.body]
  by_cases h : u.val < indices.length
  · obtain ⟨un,addU,hu,step,index⟩ := next_some indices u h
    have lt : i < k := by change i.val < k.val; omega
    obtain ⟨j,addJ,hj⟩ := spec_imp_exists (U32.add_spec (x:=i) (y:=1#u32) (by scalar_tac))
    have castI : UScalar.cast .U32 u = i := by apply UScalar.eq_of_val_eq; simp; scalar_tac
    have castU : UScalar.cast .Usize i = u := by apply UScalar.eq_of_val_eq; simp; scalar_tac
    simp only [step,uncurry,bind_ok,lt,↓reduceIte,Std.bind_assoc,castI,castU,lift,index,addJ]
    simp only [fors_path sk seed a ⟨0#u32,height⟩ height rfl]
    repeat' (apply bind_same; intro x)
    simpa only [cache.shake_ops.fors_sign_loop0, shake.fors.fors_sign_loop0,
      cache.shake_ops.fors_sign_loop0.body, shake.fors.fors_sign_loop0.body, uncurry,lift,bind_ok,
      Std.bind_assoc, fors_path sk seed a ⟨0#u32,height⟩ height rfl] using
      fors_outer k height sk seed a indices len x j un (by scalar_tac)
  · have stop : ¬i < k := by change ¬i.val < k.val; omega
    simp only [next_none indices u h,stop,↓reduceIte,uncurry,bind_ok]
termination_by indices.length - u.val
decreasing_by omega

-- A detector outcome stays a hypothesis so both hardware choices remain available.
set_option linter.concreteInstances false
variable [Acceleration]

/-- Cached scalar WOTS signing returns exactly the portable signature bytes. -/
theorem wots_sign_eq {N : Usize} (p : params.Params) (hp : PN p N)
    (scalar : Acceleration.available N = ok false) (m sk seed : Array U8 N) (a : address.Adrs) :
    cache.shake_ops.wots_sign m sk seed a = shake.wots.wots_sign m sk seed a := by
  unfold cache.shake_ops.wots_sign shake.wots.wots_sign
  obtain ⟨digits,ds,_,len,_⟩ := spec_imp_exists (wots_digits_spec p hp m)
  have bound : (alloc.vec.Vec.len digits).val * N.val ≤ Usize.max := by
    change digits.length * N.val ≤ Usize.max
    have hN := hp.le32
    have hd : digits.length ≤ 67 := by omega
    have := Nat.mul_le_mul hd hN
    scalar_tac
  obtain ⟨cap,hm,_⟩ := spec_imp_exists (Usize.mul_spec (x:=alloc.vec.Vec.len digits) (y:=N) bound)
  simp only [ds, cache.shake_ops.simd.available, scalar, bind_ok, Bool.false_eq_true, ↓reduceIte, hm,
    core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  exact wots_sign_loop sk seed a digits (alloc.vec.Vec.new U8) 0#usize

/-- Scalar WOTS recovery returns the portable root on every candidate signature. -/
theorem wots_recover_eq {N : Usize} (scalar : Acceleration.available N = ok false)
    (sig : Slice U8) (m seed : Array U8 N) (a : address.Adrs) :
    cache.shake_ops.wots_pk_from_sig sig m seed a = shake.wots.wots_pk_from_sig sig m seed a := by
  unfold cache.shake_ops.wots_pk_from_sig shake.wots.wots_pk_from_sig
  apply bind_same; intro digits
  simp only [cache.shake_ops.simd.available, scalar, bind_ok, Bool.false_eq_true, ↓reduceIte,
    core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  iterate 3 (apply bind_same; intro x)
  rw [← wots_pk_from_sig_loop sig seed a digits _ 0#usize]
  rfl

/-- Scalar FORS recovery returns the portable root on every candidate signature. -/
theorem fors_recover_eq {N : Usize} (scalar : Acceleration.available N = ok false)
    (p : params.Params) (sig md : Slice U8) (seed : Array U8 N) (a : address.Adrs) :
    cache.shake_ops.fors_pk_from_sig p sig md seed a = shake.fors.fors_pk_from_sig p sig md seed a := by
  unfold cache.shake_ops.fors_pk_from_sig shake.fors.fors_pk_from_sig
  apply bind_same; intro size
  apply bind_same; intro indices
  simp only [cache.shake_ops.simd.available, scalar, bind_ok, Bool.false_eq_true, ↓reduceIte,
    core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  iterate 3 (apply bind_same; intro x)
  rw [← fors_pk_from_sig_loop p.a sig seed a indices _ 0#usize]
  rfl

/-- Cached scalar FORS signing returns exactly the portable signature bytes. -/
theorem fors_sign_eq {N : Usize} (p : params.Params) (hp : PN p N)
    (scalar : Acceleration.available N = ok false) (md : Slice U8)
    (hmd : md.length = (p.k.val * p.a.val + 7) / 8) (sk seed : Array U8 N) (a : address.Adrs) :
    cache.shake_ops.fors_sign p md sk seed a = shake.fors.fors_sign p md sk seed a := by
  unfold cache.shake_ops.fors_sign shake.fors.fors_sign
  let k := UScalar.cast .Usize p.k
  have hk : k.val = p.k.val := by simp [k]
  have ha : 1 ≤ p.a.val := hp.valid.a_pos
  have ha' : p.a.val ≤ 14 := hp.valid.a_le
  obtain ⟨indices,bd,_,len,_⟩ := spec_imp_exists (base_2b_spec md p.a k (by omega) (by rw [hk,hmd]; omega))
  obtain ⟨cap,capEq,_⟩ := spec_imp_exists (fors_sig_bytes_spec p hp.valid)
  simp only [lift,bind_ok, ← show k = UScalar.cast .Usize p.k from rfl, bd,
    cache.shake_ops.simd.available, scalar, Bool.false_eq_true, ↓reduceIte,capEq,
    core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  exact fors_outer p.k p.a sk seed a indices (by simpa [hk] using len) (alloc.vec.Vec.new U8) 0#u32 0#usize rfl

/-- All four scalar outcomes discharge the corresponding primitive models in serial cache assembly. -/
theorem assembly_contracts {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (CacheopsRust.toSlhParams p) N) (scalar : Acceleration.available N = ok false)
    (msg sk seed : Array U8 N) (a : CacheopsRust.address.Adrs) (md sig : Slice U8)
    (hmd : md.length = (p.k.val * p.a.val + 7) / 8) :
    let adrs := CacheopsRust.toSlhAdrs a
    let params := CacheopsRust.toSlhParams p
    cache.shake_ops.wots_sign msg sk seed adrs = CacheopsRust.cache.shake_ops.wots_sign msg sk seed a ∧
    cache.shake_ops.wots_pk_from_sig sig msg seed adrs =
      CacheopsRust.cache.shake_ops.wots_pk_from_sig sig msg seed a ∧
    cache.shake_ops.fors_sign params md sk seed adrs = CacheopsRust.cache.shake_ops.fors_sign p md sk seed a ∧
    cache.shake_ops.fors_pk_from_sig params sig md seed adrs =
      CacheopsRust.cache.shake_ops.fors_pk_from_sig p sig md seed a :=
  ⟨wots_sign_eq _ hp scalar _ _ _ _, wots_recover_eq scalar _ _ _ _,
    fors_sign_eq _ hp scalar _ hmd _ _ _, fors_recover_eq scalar _ _ _ _ _⟩

end slhdsa.CacheScalar
