import Cachepath.WotsScatterProgram
import Slhdsa.Proofs.Encoding

open Aeneas Aeneas.Std Result
namespace CacheopsRust.WotsScatter

private abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Usize)

/-- Contents after committing the first k SIMD results to their original chain positions. -/
def writes {α} (orig : α) (put : α → Nat → α) : Nat → α
  | 0 => orig
  | k+1 => put (writes orig put k) k

theorem key_spec {N W : Usize} (batch : Slice Usize) (values : Array (Array U8 N) W)
    (table : Array (Array U8 N) 67#usize) (count : batch.length ≤ W.val)
    (bound : ∀ i < batch.length, batch.val[i]!.val < 67) :
    cell_key batch values table ⦃ t => t.val = writes table.val
      (fun data i => data.set batch.val[i]!.val values.val[i]!) batch.length ⦄ := by
  unfold cell_key cell_key_loop
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,bind_ok]
  apply loop.spec_decr_nat
    (measure := fun q : Iter × Array (Array U8 N) 67#usize => batch.length-q.1.iter.i)
    (inv := fun q => q.1.iter.slice = batch ∧ q.1.iter.i ≤ batch.length ∧ q.1.count.val = q.1.iter.i ∧
      q.2.val = writes table.val (fun data i => data.set batch.val[i]!.val values.val[i]!) q.1.iter.i)
  · rintro ⟨⟨⟨ds,i⟩,cnt⟩,t⟩ ⟨rfl,le,idx,prev⟩
    simp only at le idx prev bound count
    unfold cell_key_loop.body core.iter.adapters.enumerate.IteratorEnumerate.next
      core.iter.traits.iterator.IteratorSliceIter core.slice.iter.IteratorSliceIter.next
    by_cases live : i < ds.length
    · have hl : i < ds.len.val := by simpa using live
      have room : cnt.val+1 ≤ Usize.max := by scalar_tac
      simp only [dite_eq_left hl,bind_ok]
      step as ⟨next,hnext⟩
      have he : ds[i] = ds.val[i]! := by rw [getElem!_pos ds.val i live]; rfl
      have hid : ds[i].val < 67 := by rw [he]; exact bound i live
      step as ⟨v,hv⟩
      step as ⟨t',ht⟩
      refine ⟨by omega,by omega,?_,by omega⟩
      rw [ht,Array.set_val_eq,prev,hv,writes,getElem!_pos values.val i (by simpa using show i<W.val by omega)]
      simp only [he,idx]
    · have hl : ¬i < ds.len.val := by simpa using live
      simp only [dite_eq_right hl,bind_ok,step_simps]
      exact (show i = ds.length by omega) ▸ prev
  · exact ⟨rfl,Nat.zero_le _,rfl,rfl⟩

theorem sig_spec {N W : Usize} (batch : Slice Usize) (values : Array (Array U8 N) W)
    (sig : alloc.vec.Vec U8) (count : batch.length ≤ W.val)
    (room : ∀ i < batch.length, batch.val[i]!.val < Usize.max ∧ (batch.val[i]!.val+1)*N.val ≤ sig.length) :
    cell_sig batch values sig ⦃ t => t.val = writes sig.val
      (fun data i => data.setSlice! (batch.val[i]!.val * N.val) values.val[i]!.val) batch.length ⦄ := by
  unfold cell_sig cell_sig_loop
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,bind_ok]
  apply loop.spec_decr_nat
    (measure := fun q : Iter × alloc.vec.Vec U8 => batch.length-q.1.iter.i)
    (inv := fun q => q.1.iter.slice = batch ∧ q.1.iter.i ≤ batch.length ∧ q.1.count.val = q.1.iter.i ∧
      q.2.length = sig.length ∧
      q.2.val = writes sig.val (fun data i => data.setSlice! (batch.val[i]!.val*N.val) values.val[i]!.val) q.1.iter.i)
  · rintro ⟨⟨⟨ds,i⟩,cnt⟩,t⟩ ⟨rfl,le,idx,tlen,prev⟩
    simp only at le idx tlen prev room count
    unfold cell_sig_loop.body core.iter.adapters.enumerate.IteratorEnumerate.next
      core.iter.traits.iterator.IteratorSliceIter core.slice.iter.IteratorSliceIter.next
    by_cases live : i < ds.length
    · have hl : i < ds.len.val := by simpa using live
      have hcnt : cnt.val+1 ≤ Usize.max := by scalar_tac
      simp only [dite_eq_left hl,bind_ok]
      step as ⟨next,hnext⟩
      obtain ⟨ha,hb⟩ := room i live
      have he : ds[i] = ds.val[i]! := by rw [getElem!_pos ds.val i live]; rfl
      have a : ds[i].val < Usize.max := by rw [he]; exact ha
      have b : (ds[i].val+1)*N.val ≤ t.length := by rw [he,tlen]; exact hb
      have lim := t.property
      have lo : ds[i].val*N.val ≤ (ds[i].val+1)*N.val := by rw [Nat.add_mul]; omega
      step as ⟨start,hstart⟩
      step as ⟨j,hj⟩
      step as ⟨stop,hstop⟩
      step as ⟨seg,back,hseg,hlen,hback⟩
      step as ⟨v,hv⟩
      simp only [lift,bind_ok]
      have size : seg.length = N.val := by simp only [hj,Nat.add_mul,Nat.one_mul] at hstop; omega
      step as ⟨seg',hcopy⟩
      refine ⟨by omega,by omega,?_,?_,by omega⟩
      · rw [hback]; simpa only [alloc.vec.Vec.length,alloc.vec.Vec.val,alloc.vec.Vec.setSlice!,Slice.setSlice!_val,List.length_setSlice!] using tlen
      · rw [hback]; simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val]
        change t.val.setSlice! start.val seg'.val = _
        rw [prev,hstart,writes,hcopy,hv,
          getElem!_pos values.val i (by simpa using show i<W.val by omega)]
        simp only [he,idx,Array.val_to_slice,alloc.vec.Vec.val]
    · have hl : ¬i < ds.len.val := by simpa using live
      simp only [dite_eq_right hl,bind_ok,step_simps]
      exact (show i = ds.length by omega) ▸ prev
  · exact ⟨rfl,Nat.zero_le _,rfl,rfl,rfl⟩

private def packed {N : Usize} (rows : List (Array U8 N)) := rows.flatMap (·.val)

private theorem packed_length {N : Usize} (rows : List (Array U8 N)) :
    (packed rows).length = rows.length*N.val := by
  induction rows with
  | nil => simp [packed]
  | cons x xs ih => simpa [packed,Nat.add_mul,Nat.add_comm] using congrArg (N.val+·) ih

private theorem packed_set {N : Usize} (rows : List (Array U8 N)) (id : Nat) (v : Array U8 N)
    (bound : id < rows.length) :
    (packed rows).setSlice! (id*N.val) v.val = packed (rows.set id v) := by
  have split := List.set_eq_take_append_cons_drop (l := rows) (i := id) (a := rows[id])
  rw [List.set_getElem_self,ite_eq_left bound] at split
  have left := congrArg packed split
  simp only [packed,List.flatMap_append,List.flatMap_cons] at left
  rw [List.set_eq_take_append_cons_drop,ite_eq_left bound]
  simp only [packed,List.flatMap_append,List.flatMap_cons]
  rw [left,← List.append_assoc]
  apply (slhdsa.setSlice_mid' _ _ _ _ _ ?_ (by simp)).trans (List.append_assoc ..)
  change id*N.val = (packed (rows.take id)).length
  rw [packed_length,List.length_take,Nat.min_eq_left (Nat.le_of_lt bound)]

/-- Writing serialized signature bytes and writing recovery rows implement the same indexed table. -/
theorem sig_rows {N W : Usize} (batch : Slice Usize) (values : Array (Array U8 N) W)
    (orig : List (Array U8 N)) (sig : alloc.vec.Vec U8) (init : sig.val = orig.flatMap (·.val))
    (count : batch.length ≤ W.val) (valid : ∀ i < batch.length, batch.val[i]!.val < orig.length)
    (limit : orig.length ≤ Usize.max) :
    cell_sig batch values sig ⦃ t => t.val =
      (writes orig (fun data i => data.set batch.val[i]!.val values.val[i]!) batch.length).flatMap (·.val) ⦄ := by
  have size : sig.length = orig.length*N.val := by
    change sig.val.length = _
    rw [init]; exact packed_length orig
  let put := fun (data : List (Array U8 N)) (i : Nat) => data.set batch.val[i]!.val values.val[i]!
  have len (k : Nat) : (writes orig put k).length = orig.length := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [writes,put,List.length_set] using ih
  have eq (k : Nat) (hk : k ≤ batch.length) : writes sig.val
      (fun data i => data.setSlice! (batch.val[i]!.val*N.val) values.val[i]!.val) k =
      packed (writes orig put k) := by
    induction k with
    | zero => exact init
    | succ k ih =>
      rw [writes,ih (by omega),writes]
      apply packed_set
      rw [len]
      exact valid k (by omega)
  let* ⟨t,h⟩ ← sig_spec batch values sig count (by
    intro i hi
    refine ⟨lt_of_lt_of_le (valid i hi) limit,?_⟩
    rw [size]
    exact Nat.mul_le_mul_right _ (valid i hi))
  exact h.trans (eq _ (Nat.le_refl _))

/-- Extensional postcondition for the table shared by the signing and recovery scatters.
It applies to every initial table, allowing successive batches to be composed. -/
theorem writes_at {α : Type} (orig : List α) (ids : Nat → Nat) (values ref : Nat → α)
    (k : Nat) (valid : ∀ i < k, ids i < orig.length) (correct : ∀ i < k, values i = ref (ids i))
    (j : Nat) :
    letI := Classical.propDecidable
    (writes orig (fun rows i => rows.set (ids i) (values i)) k)[j]? =
      if ∃ i < k, ids i = j then some (ref j) else orig[j]? := by
  classical
  let put := fun (rows : List α) (i : Nat) => rows.set (ids i) (values i)
  have length (t : Nat) : (writes orig put t).length = orig.length := by
    induction t with
    | zero => rfl
    | succ t ih => simpa only [writes,put,List.length_set] using ih
  induction k with
  | zero => simp [writes]
  | succ k ih =>
    rw [writes]
    by_cases last : ids k = j
    · have pos : ids k < (writes orig put k).length := (length k) ▸ valid k (by omega)
      rw [← last,List.getElem?_set_self pos,correct k (by omega),ite_eq_left ⟨k,by omega,rfl⟩]
    · have same : (∃ i < k+1, ids i = j) ↔ (∃ i < k, ids i = j) := by
        constructor
        · rintro ⟨i,hi,eq⟩
          exact ⟨i,by by_contra! h; exact last ((show i=k by omega) ▸ eq),eq⟩
        · rintro ⟨i,hi,eq⟩; exact ⟨i,by omega,eq⟩
      rw [List.getElem?_set_ne last,propext same]
      exact ih (fun i hi => valid i (by omega)) (fun i hi => correct i (by omega))

end CacheopsRust.WotsScatter
