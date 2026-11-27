import Cachepath.WotsShortBlocks
import Cachepath.WotsScatter
import Shakebatch.WotsRecover

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.WotsCallbacks
open slhdsa.ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 1300000
variable [machine : Machine]

private theorem chunk_reject {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (seed : Array U8 N) (a : slhdsa.address.Adrs) (digits : Slice U32)
    (valid : ∀ j < digits.length, digits.val[j]!.val < 16) (count : digits.length ≤ 67)
    (positive : 0 < machine.width.val) (permutes : PermutationCorrect) (rest : Slice Usize)
    (fits : ∀ id ∈ rest.val, id.val < digits.length)
    (missing : ∃ id ∈ rest.val, sig.length < (id.val+1)*N.val)
    (table : Array (Array U8 N) 67#usize) :
    ShakeBatch.shake.batch.recover_loop0 ⟨rest,machine.width⟩ sig seed a digits table = fail .panic := by
  have live : 0<rest.length := by
    obtain ⟨id,mem,_⟩ := missing
    exact List.length_pos_of_mem mem
  let slice := Slice.from (rest.val.take machine.width.val) (by have := rest.property; simp)
  let tail := Slice.from (rest.val.drop machine.width.val) (by have := rest.property; simp; omega)
  let nxt : ChunkIter := ⟨tail,machine.width⟩
  have split : slice.val ++ tail.val = rest.val := by simp [slice,tail,Slice.from_val]
  have len : slice.length = min machine.width.val rest.length := by simp [slice,Slice.length,Slice.from_val]
  have nonempty : 0 < slice.length := by omega
  have width : slice.length ≤ machine.width.val := by omega
  have small (id) (h : id ∈ slice.val) := fits id (split ▸ List.mem_append_left _ h)
  have input : nextChunk ⟨rest,machine.width⟩ = ok (some slice,nxt) := by
    have notempty : rest.val.isEmpty=false := by simpa using (List.ne_nil_of_length_pos live)
    simp only [nextChunk,core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,notempty,
      Bool.false_eq_true,ite_false,show machine.width.val≠0 by omega]
    rfl
  have idsProof : core.array.from_fn machine.width (ShakeBatch.shake.batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N)
      slice ⦃ out => ∀ j < machine.width.val, out.val[j]! = slice.val[min j (slice.length-1)]! ⦄ := batch_ids (N:=N) slice nonempty
  obtain ⟨ids,gen,indices⟩ := spec_imp_exists idsProof
  have laneMem j (hj : j < machine.width.val) : ids.val[j]! ∈ slice.val := by
    rw [indices j hj,getElem!_pos _ _ (by change min j (slice.length-1) < slice.length;omega)]
    exact List.getElem_mem _
  have inRange j (hj : j < machine.width.val) := small _ (laneMem j hj)
  have smallId j (hj : j < machine.width.val) : ids.val[j]!.val < 2^32 := by have := inRange j hj;omega
  have room j (hj : j < machine.width.val) : (ids.val[j]!.val+1)*N.val ≤ Usize.max := by
    have := inRange j hj
    exact le_trans (Nat.mul_le_mul (show ids.val[j]!.val+1 ≤ 67 by omega) hp.le32) (by scalar_tac)
  unfold nextChunk at input
  by_cases accessible : ∀ id ∈ slice.val, (id.val+1)*N.val ≤ sig.length
  · have body : ShakeBatch.shake.batch.recover_loop0.body sig seed a digits ⟨rest,machine.width⟩ table
        ⦃ out => ∃ table', out=.cont (nxt,table') ⦄ := by
      unfold ShakeBatch.shake.batch.recover_loop0.body
      simp only [input,bind_ok,uncurry]
      rw [gen,bind_ok]
      step with recover_blocks (N:=N) sig ids (fun j hj => accessible _ (laneMem j hj)) as ⟨vs,blocks⟩
      have limits : core.array.Array.map (ShakeBatch.shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) ids digits
          ⦃ out => ∀ j < machine.width.val, out.val[j]! = digits.val[ids.val[j]!.val]! ⦄ := limit_digits (N:=N) digits ids inRange
      step with limits as ⟨starts,lower⟩
      simp only [W_eq]
      step as ⟨last,hlast⟩
      have finish (j : Nat) (hj : j<machine.width.val) :
          (Array.repeat machine.width last).val[j]!.val = 15 := by simpa [hj] using hlast
      step with wots_chains p hp seed a ids vs starts (Array.repeat machine.width last) smallId
        (fun j hj => by rw [lower j hj,finish j hj]; have := valid _ (inRange j hj); omega) permutes as ⟨rows,_⟩
      have store := WotsScatter.key_spec slice rows table width (by
        intro i hi
        apply lt_of_lt_of_le _ count
        apply small
        rw [getElem!_pos slice.val i hi]
        exact List.getElem_mem _)
      obtain ⟨out,e,_⟩ := spec_imp_exists store
      have same (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Usize)) (t : Array (Array U8 N) 67#usize) :
          ShakeBatch.shake.batch.recover_loop0_loop0.body rows iter t = cell_key_loop.body rows iter t := by
        unfold ShakeBatch.shake.batch.recover_loop0_loop0.body cell_key_loop.body
        apply congrArg (fun k => Std.bind _ k)
        funext q
        rcases q with ⟨_ | ⟨lane,id⟩,next⟩ <;> rfl
      have scatter : ShakeBatch.shake.batch.recover_loop0_loop0 ⟨⟨slice,0⟩,0#usize⟩ table rows = ok out := by
        simpa only [cell_key,core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,
          core.iter.traits.iterator.Iterator.enumerate.default,bind_ok,cell_key_loop,
          ShakeBatch.shake.batch.recover_loop0_loop0,same] using e
      simp only [core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,
        core.iter.traits.iterator.Iterator.enumerate.default,bind_ok,scatter,WP.spec_ok]
      exact ⟨out,rfl⟩
    obtain ⟨_,ran,t,rfl⟩ := spec_imp_exists body
    have missTail : ∃ id ∈ tail.val, sig.length < (id.val+1)*N.val := by
      obtain ⟨id,h,bad⟩ := missing
      rw [← split,List.mem_append] at h
      exact ⟨id,h.resolve_left (fun h => Nat.not_lt_of_ge (accessible _ h) bad),bad⟩
    unfold ShakeBatch.shake.batch.recover_loop0
    conv_lhs => rw [loop.eq_def]
    simp only [ran,bind_ok]
    exact chunk_reject p hp sig seed a digits valid count positive permutes tail
      (fun id h => fits id (split ▸ List.mem_append_right _ h)) missTail t
  · push Not at accessible
    obtain ⟨id,h,bad⟩ := accessible
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp h
    change j < slice.length at hj
    have badlane : ∃ j < machine.width.val, sig.length < (ids.val[j]!.val+1)*N.val := by
      refine ⟨j,by omega,?_⟩
      rwa [indices j (by omega),Nat.min_eq_left (by omega),getElem!_pos slice.val j hj,eq]
    have badmap := map_blocks_panic sig ids room badlane
    unfold ShakeBatch.shake.batch.recover_loop0
    conv_lhs => rw [loop.eq_def]
    simp only [ShakeBatch.shake.batch.recover_loop0.body,input,bind_ok,uncurry]
    rw [gen,bind_ok,badmap,bind_fail,bind_fail]
termination_by rest.length
decreasing_by
  simp only [Slice.length,Slice.from_val,List.length_drop]
  change rest.length-machine.width.val < rest.length
  omega

/-- The first out-of-bounds block in the sorted SIMD schedule produces the Rust panic.
Completed batches use the actual packed chains and may contain repeated padding lanes. -/
theorem packed_reject [stream : Stream] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (seed : Array U8 N) (a : slhdsa.address.Adrs) (digits : Slice U32)
    (count : digits.length ≤ 67) (valid : ∀ j < digits.length, digits.val[j]!.val < 16)
    (positive : 0 < machine.width.val) (permutes : PermutationCorrect) (short : sig.length < digits.length*N.val) :
    ShakeBatch.shake.batch.recover sig seed a digits = fail .panic := by
  obtain ⟨order,sorted,packed⟩ := spec_imp_exists (ShakeBatch.WotsOrder.order_spec digits count valid)
  have crop : core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice Usize))
      order { «end» := digits.len } ⦃ s => s.val = order.val.slice 0 digits.length ∧ s.length=digits.length ⦄ := by
    step*
  obtain ⟨s,sel,view,len⟩ := spec_imp_exists crop
  have correct := sorted_slice digits count order packed s view len
  have fit (id) (h : id ∈ s.val) : id.val < digits.length := by
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp h
    have inside := (correct j hj).1
    rwa [getElem!_pos s.val j hj,eq] at inside
  have nonzero : 0 < digits.length := by
    by_contra! h
    rw [show digits.length=0 by omega,Nat.zero_mul] at short
    omega
  let last := digits.length-1
  have hi : last < digits.length := by change digits.length-1 < digits.length; omega
  let idx := ShakeBatch.WotsOrder.rank digits.val last
  have ir : idx < digits.length := ShakeBatch.WotsOrder.rank_lt _ last hi
  have row : s.val[idx]!.val = last := by
    rw [view,slice0_getElem! _ _ _ ir (by simpa using count)]
    exact packed last hi
  have miss : ∃ id ∈ s.val, sig.length < (id.val+1)*N.val := by
    refine ⟨s.val[idx]!,?_,?_⟩
    · rw [getElem!_pos s.val idx (by change idx<s.length;omega)]
      exact List.getElem_mem _
    · rwa [row,show last+1=digits.length by change digits.length-1+1=digits.length;omega]
  unfold ShakeBatch.shake.batch.recover
  simp only [sorted,sel,bind_ok,ShakeBatch.core.slice.Slice.chunks,show machine.width.val≠0 by omega,ite_false,
    chunk_reject p hp sig seed a digits valid count positive permutes s fit miss,bind_fail]

end CacheopsRust.WotsCallbacks
