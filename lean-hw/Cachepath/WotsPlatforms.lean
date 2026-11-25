import Cachepath.WotsCallbacks
import Shakebatch.LinuxRound
import Kxdispatch.Proof

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.WotsCallbacks
open slhdsa.ShakeBatch
set_option linter.concreteInstances false

/-- The production Linux Arm three-lane mixed scalar/NEON kernel supplies Keccak for both callers. -/
theorem linux_fields [stream : Stream] [StreamCorrect] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) :
    @Fields Kldisp.machine stream N :=
  @fields Kldisp.machine stream _ N p hp (by decide) Kldisp.permutation_correct

/-- The production Linux x86 eight-lane AVX-512 kernel supplies Keccak when selected. -/
theorem x86_fields [stream : Stream] [StreamCorrect] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (enabled : GatherRust.avx512Available = true) : @Fields Kxdispatch.machine stream N :=
  @fields Kxdispatch.machine stream _ N p hp (by decide) (Kxdispatch.permutation_correct enabled)

end CacheopsRust.WotsCallbacks
