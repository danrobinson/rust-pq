import Mathlib.Tactic.IntervalCases
import Avx2.Proof
import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result
namespace slhdsa.Avx2
open Spec.SHA256 Avx2Rust.sha256.x86.avx2 core.core_arch.x86.avx

theorem be_four (a b c d : U8) :
    (core.num.U32.from_be_bytes (Array.make 4#usize [a,b,c,d])).bv = a.bv ++ b.bv ++ c.bv ++ d.bv := by
  change (BitVec.fromLEBytes [d.bv,c.bv,b.bv,a.bv]).cast (by rfl) = _
  simp only [BitVec.fromLEBytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, BitVec.cast_eq]
  ext i hi
  simp only [BitVec.getElem_append (x := a.bv ++ b.bv ++ c.bv) (y := d.bv),
    BitVec.getElem_append (x := a.bv ++ b.bv) (y := c.bv), BitVec.getElem_append (x := a.bv) (y := b.bv)]
  interval_cases i <;> simp [ BitVec.getElem_or, BitVec.getElem_shiftLeft,
    BitVec.getElem_setWidth]

@[step] theorem word_spec (b : Array U8 64#usize) (pos : Usize) (hp : pos.val+4 ≤ 64) :
    read_word b pos ⦃ r => r.bv = word (bytes b.val) pos.val ⦄ := by
  unfold read_word
  step*
  simp only [word]
  repeat rw [bytes_getElem! _ _ (by scalar_tac)]
  subst_vars
  simp only [← getElem!_pos, i1_post, i3_post, i5_post]
  exact be_four _ _ _ _

def Words (w : Array Reg 16#usize) (bs : Array (Array U8 64#usize) 8#usize) (n : Nat) :=
  ∀ k, k < n → ∀ j : Fin 8, w.val[k]! j = word (bytes bs.val[j.val]!.val) (4*k)

theorem load_spec (bs : Array (Array U8 64#usize) 8#usize) (w : Array Reg 16#usize) :
    compress8_loop bs w 0#usize ⦃ r => Words r bs 16 ⦄ := by
  unfold compress8_loop
  apply loop.spec_decr_nat (measure := fun (p : Array Reg 16#usize × Usize) => 16-p.2.val)
    (inv := fun p => p.2.val ≤ 16 ∧ Words p.1 bs p.2.val)
  · rintro ⟨w,i⟩ ⟨hi,hw⟩
    simp only at hi hw
    simp only [compress8_loop.body, _mm256_set_epi32, lift, bind_ok]
    split
    · step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro k hk j
      by_cases eq : k = i.val
      · subst k
        rw [a8_post, Array.set_val_eq, setSame _ _ _ (by scalar_tac)]
        have cast (x : U32) : I32.bv (UScalar.hcast .I32 x) = x.bv := rfl
        simp only [cast, i1_post, i3_post, i5_post, i7_post, i9_post, i11_post, i13_post,
          i15_post, a_post, a1_post, a2_post, a3_post, a4_post, a5_post, a6_post, a7_post, pos_post]
        rw [getElem!_pos bs.val j.val (by scalar_tac)]
        fin_cases j <;> rfl
      · rw [a8_post, Array.set_val_eq, setOther _ _ _ _ (Ne.symm eq)]
        exact hw k (by omega) j
    · have he : i.val = 16 := by scalar_tac
      simpa [step_simps, he] using hw
  · refine ⟨by change 0 ≤ 16; decide, ?_⟩
    intro k hk; exact False.elim (Nat.not_lt_zero k hk)

end slhdsa.Avx2
