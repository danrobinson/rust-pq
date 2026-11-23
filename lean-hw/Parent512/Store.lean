import Parent512.Load
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Parents
open ParentsRust.sha512.x86
def be (w : U64) : List U8 := w.bv.toBEBytes.map fun b => ⟨b⟩

private theorem write_one (N i count : Usize) (word : U64) (xs : List U64) (out : Slice (Array U8 N))
    (hc : count.val < out.length) (hb : 8*i.val+8 ≤ N.val) :
    compress_parents_loop0_loop0.body i ⟨word::xs,count⟩ out ⦃ cf =>
      ∃ next out', ∃ row : Array U8 N, cf = .cont (⟨xs,next⟩,out') ∧ next.val = count.val+1 ∧
        out'.val = out.val.set count.val row ∧ row.val = out.val[count.val]!.val.setSlice! (8*i.val) (be word) ⦄ := by
  simp only [compress_parents_loop0_loop0.body, core.iter.adapters.enumerate.IteratorEnumerate.next,
    ParentsRust.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next, bind_ok]
  step*
  all_goals try scalar_tac
  refine ⟨x, _, index_mut_back1 s2, rfl, x_post, ?_, ?_⟩
  · simp [index_mut_back_post, Slice.set_val_eq]
  · rw [s_post2,s2_post,s1_post, Array.val_to_slice, a1_post, i1_post, a_post,
      getElem!_pos out.val count.val hc]
    rfl

theorem write_column (N : Usize) (i : Usize) (xs : List U64) (count : Usize) (out : Slice (Array U8 N))
    (hc : count.val+xs.length ≤ out.length) (hb : 8*i.val+8 ≤ N.val) :
    compress_parents_loop0_loop0 ⟨xs,count⟩ out i ⦃ r =>
      r.length = out.length ∧ ∀ j, j < out.length → r.val[j]!.val =
        if count.val ≤ j ∧ j < count.val+xs.length then
          out.val[j]!.val.setSlice! (8*i.val) (be xs[j-count.val]!)
        else out.val[j]!.val ⦄ := by
  induction xs generalizing count out with
  | nil =>
    unfold compress_parents_loop0_loop0
    rw [loop]
    simp [compress_parents_loop0_loop0.body, core.iter.adapters.enumerate.IteratorEnumerate.next,
      ParentsRust.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator,
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next, step_simps]
  | cons x xs ih =>
    unfold compress_parents_loop0_loop0
    rw [loop]
    apply WP.spec_bind (write_one N i count x xs out (by scalar_tac) hb)
    rintro _ ⟨next,out',row,rfl,hn,ho,hr⟩
    have hlen : out'.length = out.length := by simp [Slice.length,ho]
    apply WP.spec_mono (ih next out' (by scalar_tac))
    rintro r ⟨hl,hw⟩
    refine ⟨hl.trans hlen, ?_⟩
    intro j hj
    rw [hw j (by omega),ho,hn]
    by_cases he : j = count.val
    · subst j
      have hrow : (out.val.set count.val row)[count.val]! = row := by
        rw [getElem!_pos _ _ (by simp; scalar_tac), List.getElem_set_self]
      rw [hrow, hr]
      simp
    · have hread : (out.val.set count.val row)[j]! = out.val[j]! := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm he)]
      rw [hread]
      by_cases active : count.val+1 ≤ j ∧ j < count.val+1+xs.length
      · have ha : count.val ≤ j ∧ j < count.val+(x::xs).length := by simp; omega
        rw [if_pos active, if_pos ha, show j-count.val = j-(count.val+1)+1 by omega, List.getElem!_cons_succ]
      · have ha : ¬(count.val ≤ j ∧ j < count.val+(x::xs).length) := by simp; omega
        rw [if_neg active, if_neg ha]

end slhdsa.X86.S512.Parents
