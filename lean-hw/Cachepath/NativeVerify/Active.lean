import Cachepath.AppleHybrid
import Shakebatch.LinuxRound
import Kxdispatch.Proof

open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify
open ShakeBatch
set_option linter.concreteInstances false

abbrev Active (m : Machine) := Matrix m.width → Usize → Result (Matrix m.width)

def ActiveCorrect (m : Machine) (f : Active m) : Prop :=
  ∀ s n, n.val ≤ m.width.val → f s n ⦃ out => ∀ j < n.val,
    @ShakeBatch.lane m out j = Spec.Keccak.permute (@ShakeBatch.lane m s j) ⦄

def fullActive (m : Machine) (probe : Result Bool) (words : Matrix m.width) (active : Usize) :
    Result (Matrix m.width) := do
  if active = 0#usize then ok words
  else
    let b ← probe
    massert b
    m.permute words

theorem full_correct (m : Machine) (probe : Result Bool) (available : probe=ok true)
    (permutation : @PermutationCorrect m) : ActiveCorrect m (fullActive m probe) := by
  intro s n le
  by_cases empty : n=0#usize
  · simp [fullActive,empty]
  · simp only [fullActive,empty,ite_false,available,bind_ok,massert,ite_true]
    apply WP.spec_mono (permutation s)
    intro out h j hj; exact h j (hj.trans_le le)

theorem linux : ActiveCorrect Kldisp.machine (fullActive Kldisp.machine KldispRust.shake256.parallel.available) :=
  full_correct _ _ rfl Kldisp.permutation_correct

theorem x86 (enabled : GatherRust.avx512Available=true) :
    ActiveCorrect Kxdispatch.machine (fullActive Kxdispatch.machine KxdispatchRust.shake256.parallel.available) :=
  full_correct _ _ (congrArg ok enabled) (Kxdispatch.permutation_correct enabled)

def appleActive (sha3 : Bool) (words : Matrix 8#usize) (active : Usize) : Result (Matrix 8#usize) := do
  if active = 0#usize then ok words
  else
    let b ← ok true
    massert b
    let b1 ← ok sha3
    if b1 then ok (AppleHybrid.packed ⟨min active.val 8,by omega⟩ true words)
    else ok (AppleHybrid.packed ⟨min active.val 8,by omega⟩ false words)

theorem apple (sha3 : Bool) : ActiveCorrect (AppleHybrid.machine sha3) (appleActive sha3) := by
  intro s n le
  change n.val ≤ 8 at le
  by_cases zero : n=0#usize
  · simp [appleActive,zero]
  · cases sha3 <;> simp only [appleActive,zero,ite_false,bind_ok,massert,ite_true,Bool.false_eq_true,↓reduceIte,WP.spec_ok] <;>
      intro j hj <;> apply AppleHybrid.active_correct _ _ _ ⟨j,by omega⟩ <;>
      change j < min n.val 8 <;> omega

end slhdsa.NativeVerify
