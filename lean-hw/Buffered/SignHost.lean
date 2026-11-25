import Buffered.Host
import Buffered.SmallWotsProgram
import Buffered.Process
import Buffered.Large

open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered.Host
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
noncomputable section

@[instance_reducible] noncomputable def ops (k : Fused.Kernel) : Buffered.Kernel :=
  kernel k (@SmallWots.leaves k)

/-- Production subtree calls in the wide signing branch start at height three. -/
@[instance_reducible] noncomputable def signing (k : Fused.Kernel) : Fused.Kernel :=
  {k with subtree := @subtree (ops k)}

theorem signing_subtree (k : Fused.Kernel) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (perms : Fused.Permutes k)
    (active : ActiveCorrect (Fused.machine k) k.active) :
    @Fused.SubtreeAt (signing k) N p sk seed a := by
  intro i z lo hi room
  have lanes : @FullLeaves (ops k) N p sk seed a := all_eight k (@SmallWots.leaves k) p hp sk seed a perms
  have mixed : ActiveCorrect (machine (ops k)) (ops k).active := active
  exact @large_spec (ops k) N p sk seed a i z lo hi room
    (@process_at (ops k) N p hp sk seed a i z lo hi room lanes mixed)

@[instance_reducible] noncomputable def apple (sha3 : Bool) (p : params.Params) := signing (FusedApple.slhdsa.Fused.Host.apple sha3 p)
@[instance_reducible] noncomputable def x86 (p : params.Params) := signing (FusedX86.slhdsa.Fused.Host.x86 p)

theorem apple_nodes {N : Usize} (sha3 : Bool) (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs) :
    @Fused.SubtreeAt (apple sha3 p) N p sk seed a :=
  signing_subtree _ p hp sk seed a (AppleHybrid.permutation_correct sha3) (NativeVerify.apple sha3)

theorem x86_nodes {N : Usize} (on : GatherRust.avx512Available=true) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) : @Fused.SubtreeAt (x86 p) N p sk seed a :=
  signing_subtree _ p hp sk seed a (Kxdispatch.permutation_correct on) (NativeVerify.x86 on)

end
end slhdsa.Buffered.Host
