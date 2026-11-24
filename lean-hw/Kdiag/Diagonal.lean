import Kdiag.Theta
open Aeneas Aeneas.Std Result
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
open KdiagRust.core.core_arch.x86.avx512f
set_option maxHeartbeats 2500000
theorem diagonal_spec (t : Usize) (ht : t.val<5) (c : Grid) :
    diagonal t c ⦃ out => ∀ j : Fin 8, out j = c.val[j.val%5]! (col t.val 1 j.val) ⦄ := by
  unfold diagonal
  step as ⟨v0,h0⟩
  step as ⟨a1,ha1⟩
  step as ⟨b1,hb1⟩
  step as ⟨m1,_,hm1⟩
  step as ⟨v1,h1⟩
  try simp only [_mm512_mask_blend_epi64,bind_ok]
  step as ⟨a2,ha2⟩
  step as ⟨b2,hb2⟩
  step as ⟨m2,_,hm2⟩
  step as ⟨v2,h2⟩
  try simp only [_mm512_mask_blend_epi64,bind_ok]
  step as ⟨a3,ha3⟩
  step as ⟨b3,hb3⟩
  step as ⟨m3,_,hm3⟩
  step as ⟨v3,h3⟩
  try simp only [_mm512_mask_blend_epi64,bind_ok]
  step as ⟨a4,ha4⟩
  step as ⟨b4,hb4⟩
  step as ⟨m4,_,hm4⟩
  step as ⟨v4,h4⟩
  try simp only [_mm512_mask_blend_epi64,bind_ok]
  apply WP.spec_mono (move_spec t 1#usize ht (by decide) _)
  intro out ho j
  rw [ho j]
  have tg : t.val=0 ∨ t.val=1 ∨ t.val=2 ∨ t.val=3 ∨ t.val=4 := by omega
  rcases tg with t0|t0|t0|t0|t0 <;> fin_cases j <;>
    simp [col,t0,h0,h1,h2,h3,h4,hm1,hm2,hm3,hm4,hb1,hb2,hb3,hb4,ha1,ha2,ha3,ha4,getElem!_pos] <;> rfl
end slhdsa.Kdiag
