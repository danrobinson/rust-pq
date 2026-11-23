import Kmixedperm.Bridge
import Shakebatch.Lanes
open Aeneas Aeneas.Std Result
namespace KldispRust
abbrev shake256.parallel.mixed.permute := KmixedpermRust.shake256.parallel.mixed.permute

/-- [slhdsa::shake256::parallel::available]:
    Source: 'src/shake256/parallel.rs', lines 311:0-320:1 -/
def shake256.parallel.available : Result Bool := do
  ok true

/-- [slhdsa::shake256::parallel::permute]:
    Source: 'src/shake256/parallel.rs', lines 322:0-339:1 -/
def shake256.parallel.permute
  (words : Array (Array Std.U64 3#usize) 25#usize) :
  Result (Array (Array Std.U64 3#usize) 25#usize)
  := do
  let b ← shake256.parallel.available
  massert b
  shake256.parallel.mixed.permute words
end KldispRust

namespace slhdsa.Kldisp

def machine : ShakeBatch.Machine := ⟨3#usize, KldispRust.shake256.parallel.permute⟩

abbrev RoundCorrect := ∀ (a : Kmixed.Rows) (rc : U64),
  KmixedRust.shake256.parallel.mixed.round a rc ⦃ out => ∀ j,
    Kmixed.lane out j = Spec.Keccak.round (Kmixed.lane a j) rc.bv ⦄

theorem permutation_of_round (one : RoundCorrect) : @ShakeBatch.PermutationCorrect machine := by
  intro s
  change KldispRust.shake256.parallel.permute s ⦃ _ => _ ⦄
  unfold KldispRust.shake256.parallel.permute
  simp only [KldispRust.shake256.parallel.available, bind_ok, massert, ite_true]
  apply WP.spec_mono (Kmixedperm.permute_of_native one s)
  intro out eq j hj
  exact eq ⟨j,hj⟩

end slhdsa.Kldisp
