import Kdiag.Rho
open Aeneas Aeneas.Std Result
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
open KdiagRust.core.core_arch.x86.avx512f

def parity (a : Grid) (j : Fin 8) :=
  a.val[0]! j ^^^ a.val[1]! j ^^^ a.val[2]! j ^^^ a.val[3]! j ^^^ a.val[4]! j

def theta (a : Grid) (j : Fin 8) :=
  parity a (col 4 1 j.val) ^^^ (parity a (col 1 1 j.val)).rotateLeft 1

theorem delta_spec (a : Grid) : delta a ⦃ out => ∀ j, out j = theta a j ⦄ := by
  unfold delta
  step as ⟨a0,h0⟩
  step as ⟨a1,h1⟩
  step as ⟨a2,h2⟩
  simp only [_mm512_ternarylogic_epi64,KavxRust.core.core_arch.x86.avx512f._mm512_ternarylogic_epi64,bind_ok]
  step as ⟨a3,h3⟩
  step as ⟨a4,h4⟩
  step with move_spec 4#usize 1#usize (by decide) (by decide) _ as ⟨left,hl⟩
  simp only [_mm512_rol_epi64,KavxRust.core.core_arch.x86.avx512f._mm512_rol_epi64,bind_ok]
  step with move_spec 1#usize 1#usize (by decide) (by decide) _ as ⟨right,hr⟩
  simp only [_mm512_xor_si512,KavxRust.core.core_arch.x86.avx512f._mm512_xor_si512,step_simps]
  intro j
  simp only [hl,hr,theta,parity,h0,h1,h2,h3,h4,
    show (150#i32).bv.toNat%256=150 from rfl, X86.xor3]
  simp [getElem!_pos]
end slhdsa.Kdiag
