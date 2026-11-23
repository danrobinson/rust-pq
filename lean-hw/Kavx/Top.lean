import Kavx.Round
import Kavx.Fips
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kavx
theorem round_fips (a : Rows) (rc : U64) :
    KavxRust.shake256.parallel.avx512.round a rc ⦃ out => ∀ j, lane out j = round (lane a j) rc.bv ⦄ := by
  rw [round_plain]
  apply (WP.spec_ok _).mpr
  exact lanes_fips a rc
end slhdsa.Kavx
