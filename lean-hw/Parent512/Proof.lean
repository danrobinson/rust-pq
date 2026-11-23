import Parent512.Compress
import Parent512.Store
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Parents
open ParentsRust.sha512.x86
def encoded (words : List (BitVec 64)) := words.flatMap fun w => be (⟨w⟩ : U64)
def digestWords (d : Array Reg 8#usize) (j : Fin 8) := d.val.map (word64 · j)

private theorem prefix_write (x s : List U8) (i : Nat) (h : i+s.length ≤ x.length) :
    (x.setSlice! i s).take (i+s.length) = x.take i ++ s := by
  simp only [List.setSlice!, min_eq_left (by omega : s.length ≤ x.length-i), List.take_length]
  have he : i+s.length = (x.take i ++ s).length := by simp [List.length_take, min_eq_left (by omega : i ≤ x.length)]
  rw [he, List.take_append_length]

def Written {N : Usize} (out orig : Slice (Array U8 N)) (d : Array Reg 8#usize) (n : Nat) :=
  out.length = orig.length ∧
    (∀ j : Fin 8, out.val[j.val]!.val.take (8*n) = encoded ((digestWords d j).take n)) ∧
    ∀ j, 8 ≤ j → j < orig.length → out.val[j]!.val = orig.val[j]!.val

private def column (reg : Reg) : List U64 := List.ofFn fun j : Fin 8 => ⟨word64 reg j⟩

private abbrev LaneArray := Array U64 8#usize

private theorem cast_column (v : Reg) : (LaneRepr.castBits v : LaneArray).val = column v :=
  Array.from_val _ _

private theorem advance (N i : Usize) (d : Array Reg 8#usize) (out orig : Slice (Array U8 N))
    (h8 : 8 ≤ orig.length) (hi : i.val < 8) (hb : 8*i.val+8 ≤ N.val) (hw : Written out orig d i.val) :
    compress_parents_loop0_loop0 ⟨column d.val[i.val]!,0#usize⟩ out i
      ⦃ r => Written r orig d (i.val+1) ⦄ := by
  obtain ⟨hlen,hprev,hsuffix⟩ := hw
  have cLen : (column d.val[i.val]!).length = 8 := by simp [column]
  apply WP.spec_mono (write_column N i _ 0#usize out (by rw [cLen,hlen]; exact h8) hb)
  rintro r ⟨hl,hm⟩
  refine ⟨hl.trans hlen, ?_, ?_⟩
  · intro j
    have hj := hm j.val (by omega)
    simp only [show (0#usize).val = 0 by rfl, Nat.zero_le, true_and, Nat.zero_add, cLen,
      j.isLt, ↓reduceIte, Nat.sub_zero] at hj
    rw [hj]
    let v : U64 := ⟨word64 d.val[i.val]! j⟩
    have len : (be v).length = 8 := by simp [be]
    have read : (column d.val[i.val]!)[j.val]! = v := by unfold column v; exact List.getElem!_ofFn _ j.val j.isLt
    rw [read]
    change ((out.val[j.val]!.val.setSlice! (8*i.val) (be v)).take (8*(i.val+1))) = _
    rw [show 8*(i.val+1) = 8*i.val + (be v).length by omega, prefix_write _ _ _ (by scalar_tac), hprev j,
      List.take_succ_eq_append_getElem (by simp [digestWords]; exact hi)]
    simp (disch := scalar_tac) [encoded,digestWords,v,getElem!_pos]
  · intro j lo hj
    have hx := hm j (by omega)
    apply Eq.trans _ (hsuffix j lo hj)
    simpa only [show (0#usize).val = 0 by rfl,cLen,Nat.zero_add, show ¬j < 8 by omega,and_false, ↓reduceIte] using hx

private theorem store_spec (N : Usize) (orig : Slice (Array U8 N)) (d : Array Reg 8#usize)
    (h8 : 8 ≤ orig.length) (hn : N.val = 24 ∨ N.val = 32) (last : Usize) (hlast : last.val = N.val/8) :
    compress_parents_loop0 ⟨0#usize,last⟩ orig d ⦃ r => Written r orig d (N.val/8) ⦄ := by
  unfold compress_parents_loop0
  apply loop.spec_decr_nat
    (measure := fun p : core.ops.range.Range Usize × Slice (Array U8 N) => last.val-p.1.start.val)
    (inv := fun p => p.1.end = last ∧ p.1.start.val ≤ last.val ∧ Written p.2 orig d p.1.start.val)
  · rintro ⟨range,out⟩ ⟨he,hi,hw⟩
    simp only at he hi hw
    unfold compress_parents_loop0.body
    by_cases hlt : range.start.val < range.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec range hlt as ⟨o,rng,ho,hs,hr⟩
      try simp only [ho]
      step as ⟨reg,hreg⟩
      all_goals try scalar_tac
      have bound : range.start.val < last.val := he ▸ hlt
      have idx : reg = d.val[range.start.val]! := by rw [getElem!_pos _ _ (by scalar_tac)]; exact hreg
      rw [idx]
      simp only [core.intrinsics.transmute, Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
        core.iter.traits.iterator.Iterator.enumerate.trait_default, core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
      rw [cast_column]
      step with advance N range.start d out orig h8 (by scalar_tac) (by scalar_tac) hw as ⟨res,hres⟩
      exact ⟨hr.trans he, by omega, hs.symm ▸ hres, by omega⟩
    · step with core.iter.range.IteratorRange.next_Usize_none_spec range (by omega) as ⟨o,rng,ho,hs⟩
      simp only [ho,step_simps]
      have eqn : range.start.val = N.val/8 := by rw [he] at hlt; omega
      simpa [eqn] using hw
  · simp [Written,encoded]

private theorem digest_words (d : Array Reg 8#usize) (j : Fin 8) :
    digestWords d j = stateWords (laneState d j) := by
  unfold digestWords laneState stateWords
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi8 : i < 8 := by simpa using hi
    rw [List.getElem_map]
    interval_cases i <;> simp [getElem!_pos]

/-- Eight separate FIPS 180-4 block compressions, including input transposition,
big-endian serialization, truncation, and preservation of subsequent output rows. -/
theorem parents_spec (N : Usize) (st : Array U64 8#usize) (bs : Blocks) (out : Slice (Array U8 N))
    (hn : N.val = 24 ∨ N.val = 32) (h8 : 8 ≤ out.length) :
    compress_parents st bs out ⦃ r => r.length = out.length ∧
      (∀ j : Fin 8, r.val[j.val]!.val =
        encoded ((Spec.SHA512.compress (st.val.map (·.bv)) (block bs j)).take (N.val/8))) ∧
      ∀ j, 8 ≤ j → j < out.length → r.val[j]!.val = out.val[j]!.val ⦄ := by
  unfold compress_parents
  step with initial_spec N st as ⟨initial,hi⟩
  step with words_spec N bs as ⟨w,hw⟩
  rw [compress_eq]
  step with compress_block_spec initial w (block bs) hw as ⟨d,hd⟩
  step as ⟨last,hl⟩
  apply WP.spec_mono (store_spec N out d h8 hn last hl)
  rintro r ⟨hr,hrows,hsuffix⟩
  refine ⟨hr, fun j => ?_, hsuffix⟩
  have hj := hrows j
  have len : 8*(N.val/8) = r.val[j.val]!.val.length := by scalar_tac
  rw [len, List.take_length,digest_words,hd,initial_words initial st hi] at hj
  exact hj

#print axioms parents_spec
end slhdsa.X86.S512.Parents
