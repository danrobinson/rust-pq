import Fused.AuthTail
import Parallel.KeygenPlatforms
import Shakebatch.WidthThreeProgram
import Cachepath.NativeShakeWots.KeyEntry
import Cachepath.NativeVerify.HostedRecovery

open Aeneas Aeneas.Std Result
namespace slhdsa.Fused.Host
open ShakeBatch NativeVerify ParallelKeygenHost
set_option linter.concreteInstances false
noncomputable section

@[instance_reducible] private noncomputable def wots (m : Machine) (act : Active m) (stream : ShakeBatch.Stream) : WidthThree.Wots where
  keygen := @NativeShakeWots.keygen m ⟨act⟩ stream
  sign := @NativeShakeWots.sign m ⟨act⟩

/-- The subtree uses the independently replayed buffered-stack schedule and its
per-lane primitive projection. The other two callbacks occur only in the
constant-false three-lane branch of the width-eight extracted caller. -/
@[instance_reducible] noncomputable def kernel (p : params.Params) (perm : Matrix 8#usize → Result (Matrix 8#usize))
    (act : Active ⟨8#usize,perm⟩) (stream : ShakeBatch.Stream) : Kernel :=
  let m : Machine := ⟨8#usize,perm⟩
  { permute := perm, active := act
    subtree := @tree (@ShNode.primitives m stream p true)
    fallback := @WidthThree.shake.batch.xmss_subtree_fallback (wots m act stream)
    narrowSign := @NativeShakeWots.sign m ⟨act⟩ }

theorem subtree {N : Usize} (p : params.Params) (hp : PN p N)
    (perm : Matrix 8#usize → Result (Matrix 8#usize)) (act : Active ⟨8#usize,perm⟩)
    (stream : ShakeBatch.Stream) (streamLaw : @StreamCorrect stream)
    (correct : @PermutationCorrect ⟨8#usize,perm⟩)
    (sk seed : Array U8 N) (a : address.Adrs) :
    @SubtreeAt (kernel p perm act stream) N p sk seed a := by
  intro i z lo hi room
  exact @tree_spec (@ShNode.primitives ⟨8#usize,perm⟩ stream p true) N p (@ShNode.primitives_correct ⟨8#usize,perm⟩ stream streamLaw N p hp true
    (by change 0<8; decide) (by change 8≤8; decide) correct) sk seed i z a (by omega) hi room

@[instance_reducible] noncomputable def apple (sha3 : Bool) (p : params.Params) : Kernel := kernel p
  (AppleHybrid.machine sha3).permute (appleActive sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream

@[instance_reducible] noncomputable def x86 (p : params.Params) : Kernel := kernel p Kxdispatch.machine.permute
  (fullActive Kxdispatch.machine KxdispatchRust.shake256.parallel.available) ShakeForestX86.slhdsa.ShakeBatch.scalarStream

theorem apple_subtree {N : Usize} (sha3 : Bool) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) : @SubtreeAt (apple sha3 p) N p sk seed a :=
  subtree p hp _ _ _ ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect
    (AppleHybrid.permutation_correct sha3) sk seed a

theorem x86_subtree {N : Usize} (on : GatherRust.avx512Available=true) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) : @SubtreeAt (x86 p) N p sk seed a :=
  subtree p hp _ _ _ ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect (Kxdispatch.permutation_correct on) sk seed a

end
end slhdsa.Fused.Host
