import Rcni.Funs
import Shani.Digest
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel.RustCrypto
open RcNiRust.sha256.x86_sha
set_option maxRecDepth 8192

private theorem constants : RcNiRust.consts.K32.val.map (·.bv)=Spec.SHA256.K := by
  unfold RcNiRust.consts.K32 Spec.SHA256.K
  rfl

theorem rounds {W : List Word} (init : State) (t : Usize) (ht : t.val<16) :
    rounds4 t (abef (after W init (4*t.val))) (cdgh (after W init (4*t.val))) (group W (4*t.val))
      ⦃ a b => a=abef (after W init (4*t.val+4)) ∧ b=cdgh (after W init (4*t.val+4)) ⦄ := by
  unfold rounds4
  simp only [core.core_arch.x86.sse2._mm_set_epi32,lift,bind_ok]
  step as ⟨idx,hidx⟩
  step as ⟨i1,hi1⟩
  step as ⟨k3,h3⟩
  step as ⟨i2,hi2⟩
  step as ⟨k2,h2⟩
  step as ⟨i3,hi3⟩
  step as ⟨k1,h1⟩
  step as ⟨k0,h0⟩
  have read (x : U32) (i : Usize) (bound : i.val < 64)
      (ev : x = RcNiRust.consts.K32.val[i.val]'(by scalar_tac)) :
      I32.bv (UScalar.hcast .I32 x) = Spec.SHA256.K[i.val]! := by
    change x.bv = _
    rw [← constants, getElem!_pos _ _ (by simp; scalar_tac), List.getElem_map, ev]
  have kg : (⟨I32.bv (UScalar.hcast .I32 k0),I32.bv (UScalar.hcast .I32 k1),
      I32.bv (UScalar.hcast .I32 k2),I32.bv (UScalar.hcast .I32 k3)⟩ : Reg) = group Spec.SHA256.K (4*t.val) := by
    simp only [read k0 idx (by scalar_tac) h0, read k1 i3 (by scalar_tac) h1,
      read k2 i2 (by scalar_tac) h2, read k3 i1 (by scalar_tac) h3, group, hi1,hi2,hi3,hidx]
  rw [kg,abef_rounds]
  simp only [step_simps]
end slhdsa.Intel.RustCrypto
