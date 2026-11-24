import Platform.Compress
import Spec.Sha512

open Aeneas Aeneas.Std Result
open core.core_arch.x86.avx512f
namespace slhdsa.X86.S512
open Spec.SHA512

def laneState (a : Array Reg 8#usize) (j : Fin 8) : State :=
  (word64 a.val[0]! j, word64 a.val[1]! j, word64 a.val[2]! j, word64 a.val[3]! j,
   word64 a.val[4]! j, word64 a.val[5]! j, word64 a.val[6]! j, word64 a.val[7]! j)

theorem laneState_make (a b c d e f g h : Reg) (j : Fin 8) :
    laneState (Array.make 8#usize [a,b,c,d,e,f,g,h]) j =
      (word64 a j,word64 b j,word64 c j,word64 d j,word64 e j,word64 f j,word64 g j,word64 h j) := rfl

def Ring (w : Array Reg 16#usize) (W : Fin 8 → List Word) (t : Nat) : Prop :=
  ∀ k, t - 16 ≤ k → k < max 16 t → ∀ j, word64 w.val[k % 16]! j = (W j)[k]!

def Trace (s : Array Reg 8#usize) (W : Fin 8 → List Word) (initial : Fin 8 → State) (t : Nat) : Prop :=
  ∀ j, laneState s j = (List.range t).foldl (round (W j)) (initial j)

private theorem setSame {α} [Inhabited α] (xs : List α) (i : Nat) (x : α) (hi : i < xs.length) :
    (xs.set i x)[i]! = x := by simp [hi]

private theorem setOther {α} [Inhabited α] (xs : List α) (i k : Nat) (x : α) (hne : i ≠ k) :
    (xs.set i x)[k]! = xs[k]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]

set_option maxRecDepth 8000 in
private theorem constants : ∀ i : Fin 80,
    (PlatformRust.sha512.K.val[i.val]!).bv = Spec.SHA512.K[i.val]! := by
  unfold PlatformRust.sha512.K Spec.SHA512.K
  decide

theorem step_spec (t : Usize) (state : Array Reg 8#usize) (w : Array Reg 16#usize)
    (W : Fin 8 → List Word) (initial : Fin 8 → State) (ht : t.val < 80)
    (hr : Ring w W t.val) (hs : Trace state W initial t.val)
    (rec : ∀ k, 16 ≤ k → k < 80 → ∀ j, (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! +
      ssig0 (W j)[k-15]! + (W j)[k-16]!) :
    PlatformRust.sha512.x86.compression_step t state w ⦃ s r =>
      Trace s W initial (t.val+1) ∧ Ring r W (t.val+1) ⦄ := by
  unfold PlatformRust.sha512.x86.compression_step
  apply WP.spec_bind (Pₘ := fun r => Ring r W (t.val+1) ∧ ∀ j, word64 r.val[t.val%16]! j = (W j)[t.val]!)
  · split
    · rename_i hi
      have ht16 : 16 ≤ t.val := by scalar_tac
      simp only [_mm512_ror_epi64, _mm512_srli_epi64, _mm512_ternarylogic_epi64,
        _mm512_add_epi64, bind_ok]
      step*
      have readSlot (v : Reg) (idx : Usize) (k : Nat) (ev : v = w.val[idx.val]!)
          (ei : idx.val = k % 16) (hlo : t.val - 16 ≤ k) (hk : k < t.val) (j : Fin 8) :
          word64 v j = (W j)[k]! := by rw [ev, ei]; exact hr k hlo (by omega) j
      have hx := readSlot x i1 (t.val-15) (by rw [getElem!_pos w.val i1.val (by scalar_tac)]; exact x_post) (by omega) (by omega) (by omega)
      have hy := readSlot y i3 (t.val-2) (by rw [getElem!_pos w.val i3.val (by scalar_tac)]; exact y_post) (by omega) (by omega) (by omega)
      have h16 := readSlot mi6 i4 (t.val-16) (by rw [getElem!_pos w.val i4.val (by scalar_tac)]; exact mi6_post) (by omega) (by omega) (by omega)
      have h7 := readSlot mi7 i6 (t.val-7) (by rw [getElem!_pos w.val i6.val (by scalar_tac)]; exact mi7_post) (by omega) (by omega) (by omega)
      have hn : ∀ j, word64 r.val[t.val%16]! j = (W j)[t.val]! := by
        intro j
        rw [r_post, Array.set_val_eq, i4_post]
        have bound : t.val % 16 < w.val.length := by simp; omega
        rw [setSame _ _ _ bound]
        rw [rec _ ht16 ht]
        simp only [show (150#i32).bv.toNat % 256 = 150 by decide,
          show (1#i32).bv.toNat % 64 = 1 by decide,
          show (8#i32).bv.toNat % 64 = 8 by decide,
          show (19#i32).bv.toNat % 64 = 19 by decide,
          show (61#i32).bv.toNat % 64 = 61 by decide,
          show (7#u32).bv.toNat % 256 = 7 by decide,
          show (6#u32).bv.toNat % 256 = 6 by decide, word64_ofWords64, xor3, hx, hy, h16, h7, ssig0, ssig1]
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
    simp (disch := decide) only [read_lane, _mm512_ror_epi64, _mm512_ternarylogic_epi64,
      _mm512_set1_epi64, _mm512_add_epi64, lift, bind_ok]
    step*
    refine ⟨?_, hnext⟩
    intro j
    have hk := constants ⟨t.val,ht⟩
    change (PlatformRust.sha512.K.val[t.val]!).bv = _ at hk
    rw [getElem!_pos _ _ (by scalar_tac)] at hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hs j]
    rw [laneState_make]
    simp only [word64_ofWords64, show (14#i32).bv.toNat % 64 = 14 by decide,
      show (18#i32).bv.toNat % 64 = 18 by decide,
      show (41#i32).bv.toNat % 64 = 41 by decide,
      show (28#i32).bv.toNat % 64 = 28 by decide,
      show (34#i32).bv.toNat % 64 = 34 by decide,
      show (39#i32).bv.toNat % 64 = 39 by decide,
      show (150#i32).bv.toNat % 256 = 150 by decide,
      show (202#i32).bv.toNat % 256 = 202 by decide,
      show (232#i32).bv.toNat % 256 = 232 by decide,
      show (0#usize).val = 0 by rfl,
      show (1#usize).val = 1 by rfl,
      show (2#usize).val = 2 by rfl,
      show (3#usize).val = 3 by rfl,
      show (4#usize).val = 4 by rfl,
      show (5#usize).val = 5 by rfl,
      show (6#usize).val = 6 by rfl,
      show (7#usize).val = 7 by rfl, xor3, chooseWord, majorityWord,
      round, laneState, bsig0, bsig1, ch, maj]
    have wk : word64 mi3 j = (W j)[t.val]! := by
      have ev : mi3 = r.val[i.val]! := by rw [getElem!_pos _ _ (by scalar_tac)]; exact mi3_post
      rw [ev, i_post]; exact hget j
    have kc : I64.bv (UScalar.hcast .I64 i1) = K[t.val]! := by
      change i1.bv = _
      rw [i1_post]; exact hk
    rw [wk, kc]
    generalize word64 state.val[0]! j = a
    generalize word64 state.val[1]! j = b
    generalize word64 state.val[2]! j = c
    generalize word64 state.val[3]! j = d
    generalize word64 state.val[4]! j = e
    generalize word64 state.val[5]! j = f
    generalize word64 state.val[6]! j = g
    generalize word64 state.val[7]! j = h
    generalize K[t.val]! = k
    generalize (W j)[t.val]! = m
    generalize (e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41) = s1
    generalize (a.rotateRight 28 ^^^ a.rotateRight 34 ^^^ a.rotateRight 39) = s0
    generalize (e &&& f ^^^ (~~~e) &&& g) = choose
    generalize (a &&& b ^^^ a &&& c ^^^ b &&& c) = majority
    simp only [Prod.mk.injEq, true_and, and_true]
    constructor <;> ac_rfl

def feedForward (left right : State) : State :=
  let (a,b,c,d,e,f,g,h) := left
  let (u,v,w,x,y,z,r,s) := right
  (a+u,b+v,c+w,d+x,e+y,f+z,g+r,h+s)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem compress_spec (iv : Array Reg 8#usize) (w : Array Reg 16#usize)
    (W : Fin 8 → List Word) (hr : Ring w W 0)
    (rec : ∀ k, 16 ≤ k → k < 80 → ∀ j, (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! +
      ssig0 (W j)[k-15]! + (W j)[k-16]!) :
    PlatformRust.sha512.x86.compress iv w ⦃ out => ∀ j,
      laneState out j = feedForward (laneState iv j)
        ((List.range 80).foldl (round (W j)) (laneState iv j)) ⦄ := by
  unfold PlatformRust.sha512.x86.compress
  have hs : Trace iv W (laneState iv) 0 := fun _ => rfl
  iterate 80
    apply WP.spec_bind (step_spec _ _ _ W (laneState iv) (by decide) (by assumption) (by assumption) rec)
    rintro ⟨s,r⟩ ⟨hs,hr⟩
  simp (disch := decide) only [read_lane, _mm512_add_epi64, bind_ok, step_simps]
  intro j
  have done := hs j
  simp only [show (79#usize).val + 1 = 80 by rfl] at done
  rw [laneState_make, ← done]
  simp only [word64_ofWords64]
  rfl

#print axioms compress_spec
end slhdsa.X86.S512
