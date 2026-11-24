import Xmsskeys.Step
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssKeys

theorem chunk_none {N} (it : Groups N) (stop : it.iter.slice.length ≤ it.iter.offset) :
    nextGroup it = ok (none,it,fun e _ => e) := by
  unfold nextGroup XmssKeysRust.core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [XmssKeysRust.core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice,
    XmssKeysRust.core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next,
    if_neg (Nat.not_lt_of_ge stop),bind_tc_eq,bind_ok]

theorem chunk_some {N} (it : Groups N) (more : it.iter.offset < it.iter.slice.length)
    (space : it.count.val < Usize.max) :
    ∃ part next restore, nextGroup it = ok (some (it.count,part),next,restore) ∧
      next.iter.slice=it.iter.slice ∧ next.iter.width=it.iter.width ∧ next.count.val=it.count.val+1 ∧
      part.length=min it.iter.width.val (it.iter.slice.length-it.iter.offset) ∧
      next.iter.offset=it.iter.offset+part.length ∧
      ∀ (e : Groups N) x, (restore e (some (it.count,x))).iter.slice=e.iter.slice.setSlice! it.iter.offset x.val := by
  obtain ⟨count,add,val⟩ := spec_imp_exists (Usize.add_spec (x := it.count) (y := 1#usize) (by scalar_tac))
  unfold nextGroup XmssKeysRust.core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [XmssKeysRust.core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice,
    XmssKeysRust.core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next,
    if_pos more,bind_tc_eq,bind_ok,add]
  refine ⟨_,_,_,rfl,rfl,rfl,val,?_,by simp [Slice.length,Slice.from_val],fun _ _ => rfl⟩
  simp [Slice.length,Slice.from_val]

end slhdsa.X86.XmssKeys
