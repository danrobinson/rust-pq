import Kneon.Round
import Kneon.Fips
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kneon
open Ksha3 (Rows)
theorem round_fips (a : Rows) (rc : U64) :
    KneonRust.shake256.parallel.neon.round a rc ⦃ out => ∀ j, lane out j = round (lane a j) rc.bv ⦄ := by
  rw [round_plain]
  apply (WP.spec_ok _).mpr
  exact lanes_fips a rc
end slhdsa.Kneon
