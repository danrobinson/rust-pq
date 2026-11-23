import Kadisp.Funs
import Kappleperm.Proof
import Shakebatch.Lanes
open Aeneas Aeneas.Std Result
namespace slhdsa.Kadisp
open KadispRust
def machine : ShakeBatch.Machine := ⟨2#usize,shake256.parallel.permute⟩
theorem permutation_correct : @ShakeBatch.PermutationCorrect machine := by
  intro s
  change shake256.parallel.permute s ⦃ _ => _ ⦄
  unfold shake256.parallel.permute
  simp only [shake256.parallel.available,KadispRust.sha512.hw.arm.available,bind_ok,massert,ite_true]
  apply WP.spec_mono (Kappleperm.permute_fips s)
  intro out eq j hj
  exact eq ⟨j,hj⟩
end slhdsa.Kadisp
