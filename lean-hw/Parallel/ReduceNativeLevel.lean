import Parallel.ReduceNativeProgram
import ForsDriver.ForsIndices
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelReduceNative
open ShakeBatch
variable [family : Family]

abbrev Rows (N : Usize) := alloc.vec.Vec (Array U8 N)

theorem level_spec {N} (seed : family.Seed N) (a : address.Adrs) (lvl base : U32)
    (rows : Rows N) (n : Usize) (size : rows.length=2*n.val)
    (room : base.val+n.val≤2^32) (parent : Nat → Spec.Bytes)
    (hash : ∀ (i : Nat), i<n.val → ∀ (idx : U32), idx.val=base.val+i →
      family.hash seed {a with word2:=lvl,word3:=idx} rows.val[2*i]! rows.val[2*i+1]!
        ⦃ out => bytes out.val=parent i ⦄) :
    reduce_tree_loop0_loop0 ⟨0#usize,n⟩ seed a rows lvl base ⦃ out =>
      out.length=rows.length ∧ ∀ i<n.val, bytes out.val[i]!.val=parent i ⦄ := by
  unfold reduce_tree_loop0_loop0
  apply WP.spec_mono (range_fold (reduce_tree_loop0_loop0.body seed a lvl base) n rows
    (fun j out => out.length=rows.length ∧ (∀ i<j, bytes out.val[i]!.val=parent i) ∧
      ∀ i, j ≤ i → i<rows.length → out.val[i]! = rows.val[i]!) (by simp) ?_ ?_)
  · rintro out ⟨l,parents,_⟩; exact ⟨l,parents⟩
  · intro it current stop live prior
    obtain ⟨length,earlier,later⟩ := prior
    have fit := rows.len_ineq
    change rows.length ≤ Usize.max at fit
    have cast : (UScalar.cast .U32 it.start).val=it.start.val := cast_u32_usize_val _ (by omega)
    unfold reduce_tree_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag,address.Adrs.with_word2,address.Adrs.with_word3,lift,bind_ok]
    step as ⟨idx,iv⟩
    step as ⟨lo,loV⟩
    step as ⟨left,readL⟩
    step as ⟨hi,hiV⟩
    step as ⟨right,readR⟩
    have lv : left=rows.val[2*it.start.val]! := by
      rw [readL,←getElem!_pos,loV];exact later _ (by omega) (by omega)
    have rv : right=rows.val[2*it.start.val+1]! := by
      rw [readR,←getElem!_pos,hiV,loV];exact later _ (by omega) (by omega)
    rw [lv,rv]
    step with hash it.start.val live idx (by rw [iv,cast]) as ⟨node,val⟩
    step as ⟨_,back,_,backEq⟩
    refine ⟨next,back node,rfl,ends.trans stop,inc,?_,?_,?_⟩
    · rw [backEq];simpa using length
    · intro i bound
      rw [backEq,alloc.vec.Vec.set_val_eq]
      by_cases eq : i=it.start.val
      · subst i
        rw [setSame _ _ _ (by change _<current.length;omega)]
        exact val
      · rw [setOther _ _ _ _ (Ne.symm eq)]
        exact earlier i (by omega)
    · intro i low high
      rw [backEq,alloc.vec.Vec.set_val_eq,setOther _ _ _ _ (by omega)]
      exact later _ (by omega) high
  · intro it current last stop
    obtain ⟨_,no⟩ := ForsDriver.range_done it _ stop last
    simp [reduce_tree_loop0_loop0.body,no]
end slhdsa.ParallelReduceNative
