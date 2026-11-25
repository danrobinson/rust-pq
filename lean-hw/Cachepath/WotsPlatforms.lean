import Cachepath.WotsCallbacks
import Shakebatch.LinuxStream
import Shakebatch.X86Stream
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

/-- Both the packed rounds and incremental sponge are the Linux Arm implementations. -/
theorem linux_native_fields {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) :
    @Fields Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream N :=
  @linux_fields ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect _ p hp

theorem x86_native_fields {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (enabled : GatherRust.avx512Available = true) :
    @Fields Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream N :=
  @x86_fields ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect _ p hp enabled

end CacheopsRust.WotsCallbacks
