import Kdiag.Layout
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem even_fips (a : Grid) (rc : U64) : even a rc ⦃ out =>
    gridView true out = round (gridView false a) rc.bv ⦄ := by
  apply WP.spec_mono (even_spec a rc)
  intro out h
  apply ext25 _ _ (by simp [gridView]) (by simp [round])
  intro i hi
  rw [gridAt _ _ _ hi,roundAt _ _ _ hi]
  simp (disch := omega) only [ite_true,h,evenCell,evenC,evenB,rhoPi_view]
  generalize rotated a false = f
  interval_cases i <;> rfl

theorem odd_fips (a : Grid) (rc : U64) : odd a rc ⦃ out =>
    gridView false out = round (gridView true a) rc.bv ⦄ := by
  apply WP.spec_mono (odd_spec a rc)
  intro out h
  apply ext25 _ _ (by simp [gridView]) (by simp [round])
  intro i hi
  rw [gridAt _ _ _ hi,roundAt _ _ _ hi]
  simp (disch := omega) only [Bool.false_eq_true,ite_false,h,oddCell,rhoPi_view,oddB]
  generalize rotated a true = f
  interval_cases i <;> rfl

end slhdsa.Kdiag
