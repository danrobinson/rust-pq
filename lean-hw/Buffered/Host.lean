import Buffered.Full
import Fused.Hosted

open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered.Host
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
noncomputable section

abbrev Small := ∀ {N : Usize} (K : Usize), Array U8 N → Array U8 N → U32 → address.Adrs → Result (Array (Array U8 N) K)

/-- Both batch sizes share a native permutation implementation. The eight-key
entry runs its complete extracted PRF, chain and streaming sponge loops. -/
@[instance_reducible] noncomputable def kernel (k : Fused.Kernel) (small : Small) : Kernel where
  active := k.active
  leaves := @Full.leaves k
  small := @small
  fallback := k.fallback

theorem all_eight (k : Fused.Kernel) (small : Small) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (perms : Fused.Permutes k) :
    @FullLeaves (kernel k @small) N p sk seed a := by
  intro first room
  exact @Full.leaves_spec k N p hp sk seed first a (by omega) perms

theorem apple_eight (sha3 : Bool) (small : Small) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) :
    @FullLeaves (kernel (FusedApple.slhdsa.Fused.Host.apple sha3 p) @small) N p sk seed a :=
  all_eight _ @small p hp sk seed a (AppleHybrid.permutation_correct sha3)

theorem x86_eight (on : GatherRust.avx512Available=true) (small : Small) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) :
    @FullLeaves (kernel (FusedX86.slhdsa.Fused.Host.x86 p) @small) N p sk seed a :=
  all_eight _ @small p hp sk seed a (Kxdispatch.permutation_correct on)

theorem apple_active (sha3 : Bool) (p : params.Params) (small : Small) :
    let k := kernel (FusedApple.slhdsa.Fused.Host.apple sha3 p) @small
    ActiveCorrect (machine k) k.active := NativeVerify.apple sha3

theorem x86_active (on : GatherRust.avx512Available=true) (p : params.Params) (small : Small) :
    let k := kernel (FusedX86.slhdsa.Fused.Host.x86 p) @small
    ActiveCorrect (machine k) k.active := NativeVerify.x86 on

end
end slhdsa.Buffered.Host
