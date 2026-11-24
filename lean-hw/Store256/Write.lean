import Store256.Transpose
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Store
open StoreRust

abbrev RowIter (N : Usize) := core.slice.iter.IterMut (Array U8 N)
def WriteRow {N : Usize} (o w : Usize) (t : Rows) (j : Nat) (before after : Array U8 N) :=
  after.val = before.val.setSlice! o.val ((rowAt t j).val.take w.val)

private def Invariant {N : Usize} (a : Slice (Array U8 N)) (o w : Usize) (t : Rows)
    (it : RowIter N) (back : RowIter N → RowIter N) (j : Usize) :=
  it.slice = a ∧ it.i = j.val ∧ it.i ≤ a.length ∧
  ∀ other : RowIter N, other.slice.length = a.length →
    (back other).slice.length = a.length ∧
    (∀ k < it.i, WriteRow o w t k a.val[k]! (back other).slice.val[k]!) ∧
    (∀ k, it.i ≤ k → k < a.length → (back other).slice.val[k]! = other.slice.val[k]!)

theorem write_rows {N : Usize} (a : Slice (Array U8 N)) (o w : Usize) (t : Rows)
    (hn : a.length ≤ 16) (hw : w.val ≤ 16) (hend : o.val + w.val ≤ N.val) :
    sha256.x86.avx512.write_words_loop0_loop0 ⟨a,0⟩ (fun x => x) o t w 0#usize ⦃ it back =>
      (back it).slice.length = a.length ∧ ∀ k < a.length, WriteRow o w t k a.val[k]! (back it).slice.val[k]! ⦄ := by
  unfold sha256.x86.avx512.write_words_loop0_loop0
  apply loop.spec_decr_nat (measure := fun p : RowIter N × (RowIter N → RowIter N) × Usize => a.length - p.1.i)
    (inv := fun p => Invariant a o w t p.1 p.2.1 p.2.2)
  · rintro ⟨it,back,j⟩ ⟨hs,hj,hi,hb⟩
    simp only at hs hj hi hb
    unfold sha256.x86.avx512.write_words_loop0_loop0.body
    apply WP.spec_bind (core.slice.iter.IteratorIterMut.next.spec it)
    rintro ⟨opt,it1,next_back⟩ ⟨hsl,hnone,ho⟩
    simp only [uncurry]
    cases opt with
    | none =>
      obtain ⟨h1,h2,-⟩ := hb it1 (by rw [hsl,hs])
      simp only [step_simps,hnone]
      exact ⟨h1,fun k hk => h2 k (by rw [hs] at ho; omega)⟩
    | some x =>
      obtain ⟨hlt,rfl,hnext,hback⟩ := ho
      have hlt' : it.i < a.length := hs ▸ hlt
      step*
      all_goals try scalar_tac
      refine ⟨⟨hsl.trans hs, by omega, by omega, fun other hl => ?_⟩, by omega⟩
      simp only [hback]
      obtain ⟨h1,h2,h3⟩ := hb {slice := other.slice.setAtNat it.i (index_mut_back s2), i := other.i} (by simp [hl])
      have hset := fun k => Slice.getElem!_Nat_setAtNat other.slice it.i k (index_mut_back s2) (by simpa [hl] using hlt')
      refine ⟨h1, fun k hk => ?_, fun k hk hk' => ?_⟩
      · by_cases eq : k = it.i
        · subst k
          rw [h3 _ (by omega) hlt', hset]
          simp only [ite_true]
          unfold WriteRow rowAt
          rw [s_post2,s2_post,s1_post]
          simp only [Array.val_to_slice,hs,List.slice,List.drop_zero,Nat.sub_zero,a1_post,a_post,
            ← getElem!_pos,i1_post,i2_post,← hj]
        · exact h2 k (by omega)
      · rw [h3 k (by omega) hk',hset]
        simp [show k ≠ it.i by omega]
  · simp [Invariant]

end slhdsa.X86.Store
