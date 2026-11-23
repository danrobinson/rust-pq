import Gather512.Funs
import Parent512.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Gather
open GatherRust.sha512.x86
open Parents (be encoded digestWords)

private def Column {N : Usize} (orig out : Slice (Array U8 N)) (i : Nat) (w : Array U64 8#usize) (n : Nat) :=
  out.length = orig.length ∧ ∀ j, j < orig.length → out.val[j]!.val =
    if j < n then orig.val[j]!.val.setSlice! (8*i) (be w.val[j]!) else orig.val[j]!.val

theorem write_column {N : Usize} (orig : Slice (Array U8 N)) (i : Usize) (w : Array U64 8#usize)
    (hsize : orig.length ≤ 8) (hi : 8*i.val+8 ≤ N.val) :
    digest_groups_loop1_loop0 ⟨0#usize,orig.len⟩ orig i w ⦃ r =>
      r.length = orig.length ∧ ∀ j, j < orig.length → r.val[j]!.val =
        orig.val[j]!.val.setSlice! (8*i.val) (be w.val[j]!) ⦄ := by
  unfold digest_groups_loop1_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Slice (Array U8 N) => orig.length-p.1.start.val)
    (inv := fun p => p.1.end = orig.len ∧ p.1.start.val ≤ orig.length ∧ Column orig p.2 i.val w p.1.start.val)
  · rintro ⟨it,out⟩ ⟨he,hn,hl,hrows⟩
    simp only at he hn hl hrows
    unfold digest_groups_loop1_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · have hj : it.start.val < orig.length := by rw [he] at hlt; exact hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨o,next,ho,hs,hend⟩
      simp only [ho]
      step*
      all_goals try scalar_tac
      refine ⟨hend.trans he, by omega, ⟨?_,?_⟩, by omega⟩
      · simpa [index_mut_back_post,Slice.length] using hl
      · intro j hj'
        rw [index_mut_back_post, Slice.set_val_eq]
        by_cases eq : j = it.start.val
        · subst j
          have hset : (out.val.set it.start.val (index_mut_back1 s2))[it.start.val]! = index_mut_back1 s2 := by
            rw [getElem!_pos _ _ (by scalar_tac), List.getElem_set_self]
          rw [hset,s_post2,s2_post,s1_post, Array.val_to_slice, a1_post,i1_post, a_post,i3_post,
              ← getElem!_pos, ← getElem!_pos, hrows _ hj, if_neg (Nat.lt_irrefl _), if_pos (by omega)]
          rfl
        · have hset : (out.val.set it.start.val (index_mut_back1 s2))[j]! = out.val[j]! := by
            simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm eq)]
          rw [hset,hrows j hj']
          by_cases h : j < it.start.val <;> simp [h, show (j < next.start.val) ↔ j < it.start.val by omega]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,hi'⟩
      simp only [ho,step_simps]
      refine ⟨hl,fun j hj => ?_⟩
      have h : j < it.start.val := by rw [he] at hlt; change ¬it.start.val < orig.length at hlt; omega
      simpa only [h, if_true] using hrows j hj
  · simp [Column]

private abbrev LaneArray := Array U64 8#usize

private theorem cast_lane (v : Reg) (j : Fin 8) : (LaneRepr.castBits v : LaneArray).val[j.val]!.bv = word64 v j := by
  have h : (LaneRepr.castBits v : LaneArray).val = List.ofFn (fun k : Fin 8 => (⟨word64 v k⟩ : U64)) := Array.from_val _ _
  rw [h,List.getElem!_ofFn _ j.val j.isLt]

private def Written {N : Usize} (orig out : Slice (Array U8 N)) (d : Array Reg 8#usize) (t : Nat) :=
  out.length = orig.length ∧ ∀ j : Fin 8, j.val < orig.length →
    out.val[j.val]!.val.take (8*t) = encoded ((digestWords d j).take t)

theorem write_spec (N : Usize) (orig : Slice (Array U8 N)) (d : Array Reg 8#usize) (last : Usize)
    (hlast : last.val = N.val/8) (hsize : orig.length ≤ 8) (hn : N.val = 24 ∨ N.val = 32) :
    digest_groups_loop1 ⟨0#usize,last⟩ orig d ⦃ r =>
      r.length = orig.length ∧ ∀ j : Fin 8, j.val < orig.length →
        r.val[j.val]!.val = encoded ((stateWords (laneState d j)).take (N.val/8)) ⦄ := by
  unfold digest_groups_loop1
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Slice (Array U8 N) => last.val-p.1.start.val)
    (inv := fun p => p.1.end = last ∧ p.1.start.val ≤ last.val ∧ Written orig p.2 d p.1.start.val)
  · rintro ⟨it,out⟩ ⟨he,hi,hl,hrows⟩
    simp only at he hi hl hrows
    unfold digest_groups_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · have hb : it.start.val < last.val := he ▸ hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨o,next,ho,hs,hend⟩
      simp only [ho]
      step as ⟨reg,hreg⟩
      all_goals try scalar_tac
      simp only [core.intrinsics.transmute,bind_ok]
      step with write_column out it.start _ (by omega) (by omega) as ⟨r,hr,hw⟩
      refine ⟨hend.trans he,by omega,⟨hr.trans hl,?_⟩,by omega⟩
      intro j hj
      rw [hw _ (by omega)]
      let w := (LaneRepr.castBits reg : LaneArray).val[j.val]!
      have len : (be w).length = 8 := by simp [be]
      rw [show 8*next.start.val = 8*it.start.val+(be w).length by omega,Parents.prefix_write _ _ _ (by scalar_tac),
        hrows j hj,hs,List.take_succ_eq_append_getElem (by simp [digestWords]; omega)]
      have hv : w.bv = word64 d.val[it.start.val]! j := by rw [← getElem!_pos] at hreg; exact hreg ▸ cast_lane reg j
      change _ ++ be w = _
      simp (disch := scalar_tac) [encoded,digestWords,be,hv, getElem!_pos]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,hit⟩
      simp only [ho,step_simps]
      refine ⟨hl,fun j hj => ?_⟩
      have eqn : it.start.val = N.val/8 := by rw [he] at hlt; omega
      have ht := hrows j hj
      rw [eqn, show 8*(N.val/8) = out.val[j.val]!.val.length by scalar_tac, List.take_length, Parents.digest_words] at ht
      exact ht
  · simp [Written,encoded]

#print axioms write_spec
end slhdsa.X86.S512.Gather
