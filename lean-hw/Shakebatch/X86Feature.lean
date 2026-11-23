import Shakebatch.Available
import Kxdispatch.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.X86
noncomputable section

abbrev available := ShakeBatch.shake.batch.available KxdispatchRust.shake256.parallel.available

theorem available_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) :
    available N=.ok GatherRust.avx512Available := by
  rw [available,available_for_fips _ p hp]
  rfl

theorem permutation (enabled : GatherRust.avx512Available=true) :
    @PermutationCorrect Kxdispatch.machine := Kxdispatch.permutation_correct enabled

end
end slhdsa.ShakeBatch.X86
