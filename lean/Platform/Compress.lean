import Platform.Rounds

open Aeneas Aeneas.Std Result
open core.core_arch.x86.avx512f
namespace slhdsa.X86
open Spec.SHA256

def Ring (w : Array Reg 16#usize) (W : Fin 16 → List Word) (t : Nat) : Prop :=
  ∀ k, t - 16 ≤ k → k < max 16 t → ∀ j, w.val[k % 16]! j = (W j)[k]!

def Trace (s : Array Reg 8#usize) (W : Fin 16 → List Word) (initial : Fin 16 → State) (t : Nat) : Prop :=
  ∀ j, laneState s j = (List.range t).foldl (round (W j)) (initial j)

private theorem setSame {α} [Inhabited α] (xs : List α) (i : Nat) (x : α) (hi : i < xs.length) :
    (xs.set i x)[i]! = x := by simp [hi]

private theorem setOther {α} [Inhabited α] (xs : List α) (i k : Nat) (x : α) (hne : i ≠ k) :
    (xs.set i x)[k]! = xs[k]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]

private theorem constants : ∀ i : Fin 64,
    (PlatformRust.sha256.K.val[i.val]!).bv = Spec.SHA256.K[i.val]! := by
  unfold PlatformRust.sha256.K Spec.SHA256.K
  decide

theorem step_spec (t : Usize) (state : Array Reg 8#usize) (w : Array Reg 16#usize)
    (W : Fin 16 → List Word) (initial : Fin 16 → State) (ht : t.val < 64)
    (hr : Ring w W t.val) (hs : Trace state W initial t.val)
    (rec : ∀ k, 16 ≤ k → k < 64 → ∀ j, (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! +
      ssig0 (W j)[k-15]! + (W j)[k-16]!) :
    PlatformRust.sha256.x86.avx512.compression_step t state w ⦃ s r =>
      Trace s W initial (t.val+1) ∧ Ring r W (t.val+1) ⦄ := by
  unfold PlatformRust.sha256.x86.avx512.compression_step
  apply WP.spec_bind (Pₘ := fun r => Ring r W (t.val+1) ∧ ∀ j, r.val[t.val%16]! j = (W j)[t.val]!)
  · split
    · rename_i hi
      have ht16 : 16 ≤ t.val := by scalar_tac
      simp only [_mm512_ror_epi32, _mm512_srli_epi32, _mm512_ternarylogic_epi32,
        _mm512_add_epi32, bind_ok]
      step*
      have readSlot (v : Reg) (idx : Usize) (k : Nat) (ev : v = w.val[idx.val]!)
          (ei : idx.val = k % 16) (hlo : t.val - 16 ≤ k) (hk : k < t.val) (j : Fin 16) :
          v j = (W j)[k]! := by rw [ev, ei]; exact hr k hlo (by omega) j
      have hx := readSlot x i1 (t.val-15) (by rw [getElem!_pos w.val i1.val (by scalar_tac)]; exact x_post) (by omega) (by omega) (by omega)
      have hy := readSlot y i3 (t.val-2) (by rw [getElem!_pos w.val i3.val (by scalar_tac)]; exact y_post) (by omega) (by omega) (by omega)
      have h16 := readSlot mi6 i4 (t.val-16) (by rw [getElem!_pos w.val i4.val (by scalar_tac)]; exact mi6_post) (by omega) (by omega) (by omega)
      have h7 := readSlot mi7 i6 (t.val-7) (by rw [getElem!_pos w.val i6.val (by scalar_tac)]; exact mi7_post) (by omega) (by omega) (by omega)
      have hn : ∀ j, r.val[t.val%16]! j = (W j)[t.val]! := by
        intro j
        rw [r_post, Array.set_val_eq, i4_post]
        have bound : t.val % 16 < w.val.length := by simp; omega
        rw [setSame _ _ _ bound]
        rw [rec _ ht16 ht]
        simp only [show (150#i32).bv.toNat % 256 = 150 by decide,
          show (7#i32).bv.toNat % 32 = 7 by decide,
          show (18#i32).bv.toNat % 32 = 18 by decide,
          show (17#i32).bv.toNat % 32 = 17 by decide,
          show (19#i32).bv.toNat % 32 = 19 by decide,
          show (3#u32).bv.toNat % 256 = 3 by decide,
          show (10#u32).bv.toNat % 256 = 10 by decide, xor3, hx, hy, h16, h7, ssig0, ssig1]
        ac_rfl
      refine ⟨?_, hn⟩
      intro k hlo hhi j
      by_cases he : k = t.val
      · subst k; exact hn j
      · have hnslot : i4.val ≠ k%16 := by omega
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
    step*
    have hk := constants ⟨t.val,ht⟩
    change (PlatformRust.sha256.K.val[t.val]!).bv = _ at hk
    have hk' : i1.bv = K[t.val]! := by
      rw [getElem!_pos _ _ (by scalar_tac)] at hk
      simpa only [i1_post] using hk
    have hw : ∀ j, mi j = (W j)[t.val]! := by
      intro j
      have hv : mi = r.val[i.val]! := by rw [getElem!_pos _ _ (by scalar_tac)]; exact mi_post
      rw [hv, i_post]; exact hget j
    let* ⟨s, H⟩ ← round_spec state mi i1 W t.val hk' hw
    refine ⟨?_, hnext⟩
    intro j
    rw [H, hs j, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

def feedForward (left right : State) : State :=
  let (a,b,c,d,e,f,g,h) := left
  let (u,v,w,x,y,z,r,s) := right
  (a+u,b+v,c+w,d+x,e+y,f+z,g+r,h+s)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem compress_spec (iv state : Array Reg 8#usize) (w : Array Reg 16#usize)
    (W : Fin 16 → List Word) (hr : Ring w W 4)
    (hs : Trace state W (laneState iv) 4)
    (rec : ∀ k, 16 ≤ k → k < 64 → ∀ j, (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! +
      ssig0 (W j)[k-15]! + (W j)[k-16]!) :
    PlatformRust.sha256.x86.avx512.compress iv state w ⦃ out => ∀ j,
      laneState out j = feedForward (laneState iv j)
        ((List.range 64).foldl (round (W j)) (laneState iv j)) ⦄ := by
  unfold PlatformRust.sha256.x86.avx512.compress
  iterate 60
    apply WP.spec_bind (step_spec _ _ _ W (laneState iv) (by decide) (by assumption) (by assumption) rec)
    rintro ⟨s,r⟩ ⟨hs,hr⟩
  simp (disch := decide) only [read_lane, _mm512_add_epi32, bind_ok, step_simps]
  intro j
  have done := hs j
  simp only [show (63#usize).val + 1 = 64 by rfl] at done
  rw [laneState_make, ← done]
  rfl

#print axioms compress_spec
end slhdsa.X86
