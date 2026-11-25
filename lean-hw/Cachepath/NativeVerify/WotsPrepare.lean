import Cachepath.NativeVerify.WotsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch

/-- The dynamic verifier skips exactly chains at digit 15 and retains their original signature blocks. -/
def Prepared {N : Usize} (sig : Slice U8) (digits : Slice U32) (i : Nat)
    (tips : Array (Array U8 N) 67#usize) (remaining : Array U32 67#usize) : Prop :=
  ∀ j < i, remaining.val[j]!.val = 15-digits.val[j]!.val ∧
    (digits.val[j]!.val=15 → tips.val[j]!.val=(sig.val.drop (j*N.val)).take N.val)

theorem prepare {N : Usize} (sig : Slice U8) (digits : Slice U32)
    (tips : Array (Array U8 N) 67#usize) (remaining : Array U32 67#usize)
    (length : digits.length≤67) (fits : digits.length*N.val ≤ sig.length)
    (bounded : ∀ j < digits.length, digits.val[j]!.val ≤ 15) :
    recover_loop0 ⟨0#usize,digits.len⟩ sig digits tips remaining ⦃ out =>
      Prepared sig digits digits.length out.1 out.2 ⦄ := by
  unfold recover_loop0
  apply range_fold (fun it (st : Array (Array U8 N) 67#usize × Array U32 67#usize) =>
    recover_loop0.body sig digits it st.1 st.2) digits.len (tips,remaining)
    (fun i st => Prepared sig digits i st.1 st.2)
  · simp [Prepared]
  · rintro it ⟨tips,remaining⟩ stop more prior
    have live : it.start.val < digits.length := by simpa using more
    have inBounds := bounded _ live
    unfold recover_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using more) as ⟨_,next,tag,idx,ends⟩
    simp only [tag,W_eq]
    have sub : (16#u32 - 1#u32 : Result U32) = ok 15#u32 := rfl
    simp only [sub,bind_ok]
    step as ⟨digit,hd⟩
    rw [← getElem!_pos] at hd
    step as ⟨rem,hr⟩
    step as ⟨_,back,_,save⟩
    have hr' : rem.val=15-digits.val[it.start.val]!.val := by simpa [hd] using hr
    have update (j : Nat) (hj : j < next.start.val) :
        (back rem).val[j]!.val=15-digits.val[j]!.val := by
      rw [save,Array.set_val_eq]
      by_cases eq : it.start.val=j
      · subst j; rw [setSame _ _ _ (by simp;omega)]; exact hr'
      · rw [setOther _ _ _ _ eq]; exact (prior j (by omega)).1
    split
    · rename_i zero
      step with block_spec N sig it.start ((Nat.mul_le_mul_right N.val live).trans fits) as ⟨block,hb⟩
      step as ⟨newTips,upd⟩
      refine ⟨next,(newTips,back rem),rfl,ends.trans stop,idx,?_⟩
      intro j hj
      refine ⟨update j hj,?_⟩
      intro last
      rw [upd,Array.set_val_eq]
      by_cases eq : it.start.val=j
      · subst j; rw [setSame _ _ _ (by simp;omega)]; exact hb
      · rw [setOther _ _ _ _ eq]; exact (prior j (by omega)).2 last
    · rename_i nonzero
      simp only [WP.spec_ok]
      refine ⟨next,(tips,back rem),rfl,ends.trans stop,idx,?_⟩
      intro j hj
      refine ⟨update j hj,?_⟩
      intro last
      have positive : rem.val ≠ 0 := by
        intro zero
        exact nonzero (UScalar.eq_of_val_eq (by simpa using zero))
      have ne : j ≠ it.start.val := by
        intro eq
        rw [eq] at last
        omega
      exact (prior j (by omega)).2 last
  · rintro it ⟨tips,remaining⟩ last stop
    unfold recover_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Wots
