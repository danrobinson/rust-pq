import Avx2.Funs
import Platform.Compress

open Aeneas Aeneas.Std Result
open core.core_arch.x86.avx core.core_arch.x86.avx2
namespace slhdsa.Avx2
open Spec.SHA256

abbrev Reg := core.core_arch.x86.__m256i

def laneState (a : Array Reg 8#usize) (j : Fin 8) : State :=
  (a.val[0]! j, a.val[1]! j, a.val[2]! j, a.val[3]! j,
   a.val[4]! j, a.val[5]! j, a.val[6]! j, a.val[7]! j)

theorem laneState_make (a b c d e f g h : Reg) (j : Fin 8) :
    laneState (Array.make 8#usize [a,b,c,d,e,f,g,h]) j =
      (a j, b j, c j, d j, e j, f j, g j, h j) := rfl

private theorem readSlotOk {α} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize) (h : i.val < n.val) :
    a.index_usize i = ok (a.val[i.val]!) := by
  have hi : i.val < a.val.length := by simpa using h
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, getElem?_pos a.val i.val hi, getElem!_pos a.val i.val hi]

private theorem majority (a b c : Word) : (a &&& b) ^^^ (c &&& (a ^^^ b)) = maj a b c := by
  ext i hi
  simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> decide

def Ring (w : Array Reg 16#usize) (W : Fin 8 → List Word) (t : Nat) : Prop :=
  ∀ k, t - 16 ≤ k → k < max 16 t → ∀ j, w.val[k % 16]! j = (W j)[k]!

def Trace (s : Array Reg 8#usize) (W : Fin 8 → List Word) (initial : Fin 8 → State) (t : Nat) : Prop :=
  ∀ j, laneState s j = (List.range t).foldl (round (W j)) (initial j)

theorem setSame {α} [Inhabited α] (xs : List α) (i : Nat) (x : α) (hi : i < xs.length) :
    (xs.set i x)[i]! = x := by simp [hi]

theorem setOther {α} [Inhabited α] (xs : List α) (i k : Nat) (x : α) (hne : i ≠ k) :
    (xs.set i x)[k]! = xs[k]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]

private theorem constants : ∀ i : Fin 64,
    (Avx2Rust.sha256.K.val[i.val]!).bv = Spec.SHA256.K[i.val]! := by
  unfold Avx2Rust.sha256.K Spec.SHA256.K
  decide

set_option maxHeartbeats 1800000 in
theorem step_spec (t : Usize) (state : Array Reg 8#usize) (w : Array Reg 16#usize)
    (W : Fin 8 → List Word) (initial : Fin 8 → State) (ht : t.val < 64)
    (hr : Ring w W t.val) (hs : Trace state W initial t.val)
    (rec : ∀ k, 16 ≤ k → k < 64 → ∀ j, (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! +
      ssig0 (W j)[k-15]! + (W j)[k-16]!) :
    Avx2Rust.sha256.x86.avx2.compression_step t state w ⦃ s r =>
      Trace s W initial (t.val+1) ∧ Ring r W (t.val+1) ⦄ := by
  unfold Avx2Rust.sha256.x86.avx2.compression_step
  simp (disch := first | decide | exact ht) only [readSlotOk, bind_ok]
  step as ⟨kword, hkword⟩
  step as ⟨slot, hslot⟩
  apply WP.spec_bind (Pₘ := fun r => Ring r W (t.val+1) ∧ ∀ j, r.val[t.val%16]! j = (W j)[t.val]!)
  · split
    · rename_i hi
      have ht16 : 16 ≤ t.val := by scalar_tac
      simp only [_mm256_srli_epi32, _mm256_slli_epi32, _mm256_or_si256, _mm256_xor_si256, _mm256_add_epi32, bind_ok]
      step*
      have readSlot (v : Reg) (idx : Usize) (k : Nat) (ev : v = w.val[idx.val]!)
          (ei : idx.val = k % 16) (hlo : t.val - 16 ≤ k) (hk : k < t.val) (j : Fin 8) :
          v j = (W j)[k]! := by rw [ev, ei]; exact hr k hlo (by omega) j
      have hx := readSlot x i2 (t.val-15) (by rw [getElem!_pos w.val i2.val (by scalar_tac)]; exact x_post) (by omega) (by omega) (by omega)
      have hy := readSlot y i4 (t.val-2) (by rw [getElem!_pos w.val i4.val (by scalar_tac)]; exact y_post) (by omega) (by omega) (by omega)
      have h16 := readSlot mi17 slot (t.val-16) (by rw [getElem!_pos w.val slot.val (by scalar_tac)]; exact mi17_post) (by omega) (by omega) (by omega)
      have h7 := readSlot mi18 i6 (t.val-7) (by rw [getElem!_pos w.val i6.val (by scalar_tac)]; exact mi18_post) (by omega) (by omega) (by omega)
      have hn : ∀ j, r.val[t.val%16]! j = (W j)[t.val]! := by
        intro j
        rw [r_post, Array.set_val_eq, hslot]
        have bound : t.val % 16 < w.val.length := by simp; omega
        rw [setSame _ _ _ bound]
        rw [rec _ ht16 ht]
        simp only [hx, hy, h16, h7]
        have algebra (a b c d : Word) : (a+b)+(c+d) = b+d+a+c := by ac_rfl
        exact algebra (ssig0 (W j)[t.val-15]!) (ssig1 (W j)[t.val-2]!) _ _
      refine ⟨?_, hn⟩
      intro k hlo hhi j
      by_cases he : k = t.val
      · subst k; exact hn j
      · have hnslot : slot.val ≠ k%16 := by omega
        rw [r_post, Array.set_val_eq]
        rw [setOther _ _ _ _ hnslot]
        exact hr k (by omega) (by omega) j
    · rename_i hi
      have ht16 : t.val < 16 := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, hr t.val (by omega) (by omega)⟩
      intro k hlo hhi j
      exact hr k (by omega) (by omega) j
  · rintro r ⟨hnext, hget⟩
    simp only [_mm256_srli_epi32, _mm256_slli_epi32, _mm256_or_si256, _mm256_xor_si256,
      _mm256_and_si256, _mm256_andnot_si256, _mm256_set1_epi32, _mm256_add_epi32, lift, bind_ok]
    simp (disch := scalar_tac) only [readSlotOk, bind_ok, step_simps]
    refine ⟨?_, hnext⟩
    intro j
    have hk := constants ⟨t.val,ht⟩
    have hw := hget j
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hs j]
    rw [laneState_make]
    have kc : I32.bv (UScalar.hcast .I32 kword) = K[t.val]! := by
      change kword.bv = _
      change (Avx2Rust.sha256.K.val[t.val]!).bv = _ at hk
      rw [getElem!_pos _ _ (by scalar_tac)] at hk
      rw [hkword]
      exact hk
    simp only [laneState, round, show (0#usize).val = 0 by rfl, show (1#usize).val = 1 by rfl, show (2#usize).val = 2 by rfl, show (3#usize).val = 3 by rfl, show (4#usize).val = 4 by rfl, show (5#usize).val = 5 by rfl, show (6#usize).val = 6 by rfl, show (7#usize).val = 7 by rfl, majority, hslot, hw, kc]
    have rearrange (h s c w k : Word) : (h+s)+(c+(w+k)) = h+s+c+k+w := by ac_rfl
    simp only [rearrange]
    rfl

#print axioms step_spec

theorem compress_spec (iv : Array Reg 8#usize) (w : Array Reg 16#usize)
    (W : Fin 8 → List Word) (hr : Ring w W 0)
    (rec : ∀ k, 16 ≤ k → k < 64 → ∀ j, (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! +
      ssig0 (W j)[k-15]! + (W j)[k-16]!) :
    Avx2Rust.sha256.x86.avx2.compress_words iv w ⦃ out => ∀ j,
      laneState out j = slhdsa.X86.feedForward (laneState iv j)
        ((List.range 64).foldl (round (W j)) (laneState iv j)) ⦄ := by
  unfold Avx2Rust.sha256.x86.avx2.compress_words
  apply WP.spec_bind (Pₘ := fun state => Trace state W (laneState iv) 64)
  · unfold Avx2Rust.sha256.x86.avx2.compress_words_loop
    apply loop.spec_decr_nat
      (measure := fun (p : Array Reg 16#usize × Array Reg 8#usize × Usize) => 64 - p.2.2.val)
      (inv := fun p => p.2.2.val ≤ 64 ∧ Ring p.1 W p.2.2.val ∧ Trace p.2.1 W (laneState iv) p.2.2.val)
    · rintro ⟨w,s,i⟩ ⟨hi,hr,hs⟩
      simp only [Avx2Rust.sha256.x86.avx2.compress_words_loop.body]
      simp only at hi hr hs
      split
      · have ht : i.val < 64 := by scalar_tac
        step with step_spec i s w W (laneState iv) ht hr hs rec as ⟨s',w',hs',hr'⟩
        step*
      · have he : i.val = 64 := by scalar_tac
        simpa [step_simps, he] using hs
    · exact ⟨by change 0 ≤ 64; decide, hr, fun _ => rfl⟩
  · intro s hs
    simp (disch := decide) only [readSlotOk, _mm256_add_epi32, bind_ok, step_simps]
    intro j
    rw [laneState_make, ← hs j]
    rfl

#print axioms compress_spec
end slhdsa.Avx2
