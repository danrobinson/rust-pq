import Cachepath.SubtreeProgram
open Aeneas Aeneas.Std Result ControlFlow

namespace slhdsa.cache.builder.nativeShake.Subtree

private def stage {N : Usize} [Backend] (i z : U32) (seed : Array U8 N) (addr : address.Adrs)
    (leaves : Usize) (h : U32) (cur : Nodes N) : Result (Nodes N) := do
  let count ← leaves >>> h
  let delta ← z - h
  let base ← (UScalar.cast .Usize i) <<< delta
  let next ← alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) (Array.repeat N 0#u8) count
  let (out,restore) ← lift (alloc.vec.Vec.deref_mut next)
  let out' ← Backend.pairs seed addr h base cur.deref out
  ok (restore out')

private theorem body {N : Usize} [Backend] (i z : U32) (seed : Array U8 N) (addr : address.Adrs)
    (leaves : Usize) :
    (fun (q : Inclusive × Nodes N) => node_loop.body i z seed addr leaves q.1 q.2) =
      inclusiveBody (stage i z seed addr leaves) := by
  funext q
  unfold node_loop.body inclusiveBody
  congr 1
  funext pair
  rcases pair with ⟨o,it⟩
  cases o <;> simp [stage,Std.bind_assoc,bind_tc_eq,lift,alloc.vec.Vec.deref_mut]

/-- A batch fills a contiguous range beginning at its actual (possibly nonzero)
tree index. Parents consume precisely the pair of children at the preceding height. -/
structure Ops (b : Backend) (s : Single) {N : Usize} (p : params.Params) : Prop where
  leaf : ∀ (sk seed : Array U8 N) (a : address.Adrs), s.leaf sk seed a = shake.wots.wots_pk_gen sk seed a
  leaves : ∀ (sk pk : Array U8 N) (a : address.Adrs) (base : Usize) (out : Rows N),
    base.val + out.length ≤ 512 →
    b.fill sk pk a base out ⦃ r => Row r out.length (fun j => Value p sk pk a 0 (base.val+j)) ⦄
  parents : ∀ (sk pk : Array U8 N) (a : address.Adrs) (h : U32) (base : Usize)
    (children out : Rows N), 0 < h.val → h.val ≤ 9 → (base.val+out.length)*2^h.val ≤ 512 →
    Row children (2*out.length) (fun j => Value p sk pk a (h.val-1) (2*base.val+j)) →
    b.pairs pk a h base children out ⦃ r => Row r out.length (fun j => Value p sk pk a h.val (base.val+j)) ⦄

private theorem zero_clone (N : Usize) :
    (core.clone.CloneArray N core.clone.CloneU8).clone (Array.repeat N 0#u8) =
      ok (Array.repeat N 0#u8) := by
  obtain ⟨_,he,rfl⟩ := spec_imp_exists (core.array.CloneArray.clone_spec core.clone.CloneU8
      (Array.repeat N 0#u8) (by intros; rfl))
  exact he

private def levelRow {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (i z h : Nat) (v : Nodes N) :=
  Row v.deref (width z h) (fun j => Value p sk seed a h (i*width z h+j))

private theorem stage_spec {N : Usize} [b : Backend] [s : Single] (p : params.Params)
    (ops : Ops b s (N:=N) p) (i z : U32) (sk seed : Array U8 N) (a : address.Adrs)
    (leaves : Usize) (size : leaves.val = 2^z.val) (small : z.val ≤ 9)
    (fits : (i.val+1)*2^z.val ≤ 512) (h : U32) (pos : 0 < h.val) (le : h.val ≤ z.val)
    (cur : Nodes N) (prev : levelRow p sk seed a i.val z.val (h.val-1) cur) :
    stage i z seed a leaves h cur ⦃ next => levelRow p sk seed a i.val z.val h.val next ⦄ := by
  have bits := System.Platform.numBits_eq
  have factor : width z.val h.val * 2^h.val = 2^z.val := by
    rw [width,← Nat.pow_add,Nat.sub_add_cancel le]
  have before : width z.val (h.val-1) = 2 * width z.val h.val := by
    have sub : z.val-(h.val-1) = z.val-h.val+1 := by omega
    simp only [width,sub,pow_succ,Nat.mul_comm]
  have bound : (i.val*width z.val h.val+width z.val h.val)*2^h.val ≤ 512 := by
    simpa only [Nat.add_mul,Nat.mul_assoc,factor,Nat.one_mul] using fits
  have cap : i.val * width z.val h.val < Usize.size := by
    have := Nat.le_mul_of_pos_right (i.val*width z.val h.val+width z.val h.val) (Nat.two_pow_pos h.val)
    scalar_tac
  have cast : (UScalar.cast .Usize i).val = i.val := by
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    have := Nat.le_mul_of_pos_right (i.val+1) (Nat.two_pow_pos z.val)
    scalar_tac
  unfold stage
  step with Usize.ShiftRight_spec leaves h (by scalar_tac) as ⟨count,hcount,_⟩
  have countEq : count.val = width z.val h.val := by rw [hcount,size,leafCount le]
  step as ⟨delta,hd⟩
  step with Usize.ShiftLeft_spec (UScalar.cast .Usize i) delta (by scalar_tac) as ⟨base,hbase,_⟩
  have baseEq : base.val = i.val*width z.val h.val := by
    rw [hbase,Nat.shiftLeft_eq,cast,hd]; exact Nat.mod_eq_of_lt cap
  step with alloc.vec.from_elem_spec _ _ count (zero_clone N) as ⟨v,_,hv⟩
  simp only [alloc.vec.Vec.deref_mut,lift,bind_ok]
  have ch : Row cur.deref (2*v.deref.length) (fun j => Value p sk seed a (h.val-1) (2*base.val+j)) := by
    rw [cache.endtoend.vec_deref_len,hv,countEq,baseEq]
    simpa only [levelRow,before,Nat.mul_left_comm] using prev
  have sliceLen : v.slice.length = count.val := hv
  step with ops.parents sk seed a h base cur.deref v.slice pos (by omega)
    (by rw [sliceLen,countEq,baseEq]; exact bound) (by rw [sliceLen]; rwa [cache.endtoend.vec_deref_len,hv] at ch) as ⟨new,ok⟩
  change Row _ (width z.val h.val) _
  rw [sliceLen,countEq,baseEq] at ok
  have restore : alloc.vec.Vec.deref (⟨new⟩ : Nodes N) = new := by
    apply Slice.ext; rw [vec_deref_val]; rfl
  simpa only [restore] using ok

/-- All FIPS cache authentication nodes lie within a tree of at most 512 leaves.
The extracted loop checks the width, offset and returned root at each level. -/
theorem node_eq_scalar {N : Usize} [b : Backend] [s : Single] (p : params.Params) (hp : PN p N)
    (ops : Ops b s (N:=N) p) (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs)
    (small : z.val ≤ 9) (fits : (i.val+1)*2^z.val ≤ 512) :
    node sk i z seed a = shake.xmss.xmss_node sk i z seed a := by
  conv_lhs => rw [node.eq_def]
  by_cases zero : z = 0#u32
  · conv_rhs => rw [shake.xmss.xmss_node.eq_def]
    simp only [zero,ite_true,bind_ok,ops.leaf]
  · simp only [zero,ite_false]
    have bound : 2^z.val ≤ 512 := Nat.pow_le_pow_right (by decide : 0 < 2) small
    have bits := System.Platform.numBits_eq
    have lim : 2^z.val < Usize.size := by scalar_tac
    have cast : (UScalar.cast .Usize i).val = i.val := by
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      have := Nat.le_mul_of_pos_right (i.val+1) (Nat.two_pow_pos z.val)
      scalar_tac
    have bc : i.val*2^z.val < Usize.size := by
      have h : i.val*2^z.val ≤ 512 := by
        rw [Nat.add_mul,Nat.one_mul] at fits
        exact (Nat.le_add_right _ _).trans fits
      have u := cache.endtoend.usize_max_ge; scalar_tac
    have proof : (do
        let count ← 1#usize <<< z
        if count <= 512#usize then
          let base ← (UScalar.cast .Usize i) <<< z
          let v ← alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) (Array.repeat N 0#u8) count
          let (rows,back) ← lift (alloc.vec.Vec.deref_mut v)
          let filled ← Backend.fill sk seed a base rows
          let it ← core.ops.range.RangeInclusive.new 1#u32 z
          let last ← node_loop it i z seed a count (back filled)
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array U8 N)) last 0#usize
        else fail .panic) ⦃ out => bytes out.val = Value p sk seed a z.val i.val ⦄ := by
      step with Usize.ShiftLeft_spec 1#usize z (by scalar_tac) as ⟨count,hl,_⟩
      have size : count.val = 2^z.val := by rw [hl,Nat.one_shiftLeft,Nat.mod_eq_of_lt lim]
      simp only [show count ≤ 512#usize by scalar_tac, ite_true]
      step with Usize.ShiftLeft_spec (UScalar.cast .Usize i) z (by scalar_tac) as ⟨base,baseVal,_⟩
      have hbase : base.val = i.val*2^z.val := by rw [baseVal,Nat.shiftLeft_eq,cast,Nat.mod_eq_of_lt bc]
      step with alloc.vec.from_elem_spec _ _ count (zero_clone N) as ⟨v,_,hv⟩
      simp only [alloc.vec.Vec.deref_mut,lift,bind_ok]
      have vs : v.slice.length = count.val := hv
      step with ops.leaves sk seed a base v.slice
        (by rw [vs,size,hbase]; simpa [Nat.add_mul] using fits) as ⟨filled,vals⟩
      step as ⟨it,first,last,fresh⟩
      have init : levelRow p sk seed a i.val z.val (1-1) (⟨filled⟩ : Nodes N) := by
        have restore : alloc.vec.Vec.deref (⟨filled⟩ : Nodes N) = filled := by
          apply Slice.ext; rw [vec_deref_val]; rfl
        simpa only [levelRow,restore,vs,size,hbase,width,Nat.sub_self,Nat.sub_zero] using vals
      have loopOk := levels (stage i z seed a count)
        (fun k => levelRow p sk seed a i.val z.val (k-1)) z (by scalar_tac)
        (fun h v pos le prev => by simpa using stage_spec p ops i z sk seed a count size small fits h pos le v prev)
        it first last fresh _ init
      have run : node_loop it i z seed a count ⟨filled⟩ ⦃ v => levelRow p sk seed a i.val z.val z.val v ⦄ := by
        simpa only [node_loop,body,Nat.add_sub_cancel] using loopOk
      step with run as ⟨v',row⟩
      obtain ⟨len,atIdx⟩ := row
      have n : v'.length = 1 := by simpa only [cache.endtoend.vec_deref_len,width,Nat.sub_self,pow_zero] using len
      step with alloc.vec.Vec.index_usize_spec v' 0#usize (by scalar_tac) as ⟨out,read⟩
      have good := atIdx 0 (by simp [width])
      rw [vec_deref_val,getElem!_pos v'.val 0 (by change 0 < v'.length; omega)] at good
      simpa [width,read] using good
    obtain ⟨count,shift,hv,_⟩ := spec_imp_exists (Usize.ShiftLeft_spec 1#usize z (by scalar_tac))
    have size : count.val = 2^z.val := by change count.val = 2^z.val; rw [hv]; change (1 <<< z.val) % Usize.size = _; rw [Nat.one_shiftLeft,Nat.mod_eq_of_lt lim]
    obtain ⟨x,run,post⟩ := spec_imp_exists proof
    obtain ⟨y,ref,post'⟩ := spec_imp_exists (Shake.xmss_node_spec p hp sk i z seed a (by omega))
    simp only [shift,bind_ok,show count ≤ 512#usize by scalar_tac,ite_true,lift] at run ⊢
    rw [run,ref]
    exact congrArg Result.ok (Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (post.trans post'.symm)))

end slhdsa.cache.builder.nativeShake.Subtree
