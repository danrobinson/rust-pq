import Ksha3.Round
import Ksha3.Fips
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Ksha3
theorem round_fips (a : Rows) (rc : U64) :
    Ksha3Rust.shake256.parallel.sha3.round a rc ⦃ out => ∀ j, lane out j = round (lane a j) rc.bv ⦄ := by
  rw [round_plain]
  apply (WP.spec_ok _).mpr
  exact lanes_fips a rc
end slhdsa.Ksha3
