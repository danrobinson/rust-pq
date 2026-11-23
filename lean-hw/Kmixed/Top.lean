import Kmixed.CompactRound
import Kmixed.Agreement
import Kmixed.Fips
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kmixed

theorem round_fips (a : Rows) (rc : U64) :
    KmixedRust.shake256.parallel.mixed.round a rc ⦃ out => ∀ j, lane out j = round (lane a j) rc.bv ⦄ := by
  rw [round_compact,compactEq]
  apply (WP.spec_ok _).mpr
  exact lanes_fips a rc
end slhdsa.Kmixed
