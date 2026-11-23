import Kxdispatch.Funs
import Kavxperm.Proof
import Shakebatch.Lanes
open Aeneas Aeneas.Std Result
namespace slhdsa.Kxdispatch
open KxdispatchRust
def machine : ShakeBatch.Machine := ⟨8#usize,shake256.parallel.permute⟩
theorem permutation_correct (available : GatherRust.avx512Available = true) : @ShakeBatch.PermutationCorrect machine := by
  intro s
  change shake256.parallel.permute s ⦃ _ => _ ⦄
  unfold shake256.parallel.permute
  simp only [shake256.parallel.available,KxdispatchRust.sha256.x86.avx512_available,GatherRust.sha256.x86.avx512_available,available,bind_ok,massert,ite_true]
  apply WP.spec_mono (Kavxperm.permute_fips s)
  intro out eq j hj
  exact eq ⟨j,hj⟩
end slhdsa.Kxdispatch
