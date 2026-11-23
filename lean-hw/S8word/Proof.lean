import S8word.Funs
import Streamround.Schedule
import Platform.Rounds
open Aeneas Aeneas.Std Result
open core.core_arch.x86 core.core_arch.x86.avx core.core_arch.x86.avx2
open S8wordRust.core.core_arch.x86.avx512f
namespace slhdsa.X86.Stream.Eight
open Spec.SHA256
set_option maxHeartbeats 1800000
def ring (w : Array __m256i 16#usize) (W : Fin 8 → List Word) (t : Nat) :=
  ∀ k, t-16 ≤ k → k < max 16 t → ∀ j, w.val[k%16]! j = (W j)[k]!
private theorem reorder {n} (a b c d : BitVec n) : a+b+(c+d)=b+d+a+c := by ac_rfl

private theorem setSame {α} [Inhabited α] (xs : List α) (i : Nat) (x : α) (hi : i < xs.length) :
    (xs.set i x)[i]! = x := by simp [hi]
private theorem setOther {α} [Inhabited α] (xs : List α) (i k : Nat) (x : α) (hne : i ≠ k) :
    (xs.set i x)[k]! = xs[k]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]

theorem expand_fips (t : Usize) (w : Array __m256i 16#usize)
    (blocks : Array (Array U8 64#usize) 8#usize) (ht : t.val < 64)
    (old : ring w (fun j => schedule (bytes blocks.val[j.val]!.val)) t.val) :
    S8wordRust.sha256.stream.expand t w ⦃ out =>
      ring out.1 (fun j => schedule (bytes blocks.val[j.val]!.val)) (t.val+1) ∧
      ∀ j : Fin 8, out.2.val[j.val]!.bv = K[t.val]! + (schedule (bytes blocks.val[j.val]!.val))[t.val]! ⦄ := by
  let W := fun j : Fin 8 => schedule (bytes blocks.val[j.val]!.val)
  have hr : ring w W t.val := old
  have recurrence (k : Nat) (lo : 16 ≤ k) (hi : k < 64) (j : Fin 8) : (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! + ssig0 (W j)[k-15]! + (W j)[k-16]! := slhdsa.schedule_rec (bytes blocks.val[j.val]!.val) k lo hi
  unfold S8wordRust.sha256.stream.expand
  apply WP.spec_bind (Pₘ := fun r => ring r W (t.val+1) ∧ ∀ j, r.val[t.val%16]! j = (W j)[t.val]!)
  · split
    · rename_i hi
      have late : 16 ≤ t.val := by scalar_tac
      simp only [_mm256_ror_epi32, _mm256_srli_epi32, _mm256_ternarylogic_epi32,
        _mm256_add_epi32, bind_ok]
      step*
      have readSlot (v : __m256i) (idx : Usize) (k : Nat) (ev : v = w.val[idx.val]!)
          (ei : idx.val = k % 16) (hlo : t.val - 16 ≤ k) (hk : k < t.val) (j : Fin 8) :
          v j = (W j)[k]! := by rw [ev, ei]; exact hr k hlo (by omega) j
      have hx := readSlot x i1 (t.val-15) (by rw [getElem!_pos w.val i1.val (by scalar_tac)]; exact x_post) (by omega) (by omega) (by omega)
      have hy := readSlot y i3 (t.val-2) (by rw [getElem!_pos w.val i3.val (by scalar_tac)]; exact y_post) (by omega) (by omega) (by omega)
      have h16 := readSlot mi7 i4 (t.val-16) (by rw [getElem!_pos w.val i4.val (by scalar_tac)]; exact mi7_post) (by omega) (by omega) (by omega)
      have h7 := readSlot mi8 i6 (t.val-7) (by rw [getElem!_pos w.val i6.val (by scalar_tac)]; exact mi8_post) (by omega) (by omega) (by omega)
      have hn : ∀ j, r.val[t.val%16]! j = (W j)[t.val]! := by
        intro j
        rw [r_post, Array.set_val_eq, i4_post]
        have bound : t.val % 16 < w.val.length := by simp; omega
        rw [setSame _ _ _ bound]
        rw [recurrence _ late ht j]
        simp only [show (150#i32).bv.toNat % 256 = 150 by decide,
          show (7#i32).bv.toNat % 32 = 7 by decide,
          show (18#i32).bv.toNat % 32 = 18 by decide,
          show (17#i32).bv.toNat % 32 = 17 by decide,
          show (19#i32).bv.toNat % 32 = 19 by decide,
          show (3#i32).bv.toNat % 256 = 3 by decide,
          show (10#i32).bv.toNat % 256 = 10 by decide, xor3, hx, hy, h16, h7, ssig0, ssig1]
        exact reorder _ _ _ _
      refine ⟨?_, hn⟩
      intro k hlo hhi j
      by_cases he : k = t.val
      · subst k; exact hn j
      · have hnslot : i4.val ≠ k%16 := by omega
        rw [r_post, Array.set_val_eq]
        rw [setOther _ _ _ _ hnslot]
        exact hr k (by omega) (by omega) j
    · rename_i hi
      have late : t.val < 16 := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, hr t.val (by omega) (by omega)⟩
      intro k hlo hhi j
      exact hr k (by omega) (by omega) j
  · rintro r ⟨ring,word⟩
    simp only [_mm256_set1_epi32,_mm256_add_epi32,lift,bind_ok,S8wordRust.core.intrinsics.transmute]
    step as ⟨idx,hi⟩
    step as ⟨v,hv⟩
    step as ⟨key,hk⟩
    have keyEq : key.bv = Spec.SHA256.K[t.val]! := by
      have same : S8wordRust.sha256.K = slhdsa.sha256.K := by unfold S8wordRust.sha256.K slhdsa.sha256.K; rfl
      rw [hk,same,← slhdsa.K_eq,slhdsa.wv_getElem! _ _ (by simpa using ht)]
    refine ⟨ring,?_⟩
    intro j
    have read := word j
    rw [← hi,getElem!_pos _ _ (by scalar_tac),← hv] at read
    rw [Array.from_val,List.getElem!_ofFn _ j.val j.isLt]
    change v j + key.bv = Spec.SHA256.K[t.val]! + (W j)[t.val]!
    rw [keyEq,read,BitVec.add_comm]
end slhdsa.X86.Stream.Eight
