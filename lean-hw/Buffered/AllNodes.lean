import Buffered.KeyNodes
import Buffered.SmallWots

open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered.Host
open ShakeBatch NativeVerify
set_option linter.concreteInstances false

theorem every_height (k : Fused.Kernel) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (i z : U32) (a : address.Adrs) (lo : 1≤z.val) (hi : z.val≤9)
    (room : (i.val+1)*2^z.val≤512) (perms : Fused.Permutes k) (active : ActiveCorrect (Fused.machine k) k.active) :
    (signing k).subtree sk seed i z a ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p)
      (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄ := by
  apply nodes k p hp sk seed i z a lo hi room perms active
  intro K width first fits
  exact @SmallWots.leaves_spec k N p hp sk seed a K first (by rcases width with rfl|rfl <;> decide) fits active

theorem apple_all {N : Usize} (sha3 : Bool) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (i z : U32) (a : address.Adrs) (lo : 1≤z.val) (hi : z.val≤9) (room : (i.val+1)*2^z.val≤512) :
    (apple sha3 p).subtree sk seed i z a ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p)
      (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄ :=
  every_height _ p hp sk seed i z a lo hi room (AppleHybrid.permutation_correct sha3) (NativeVerify.apple sha3)

theorem x86_all {N : Usize} (on : GatherRust.avx512Available=true) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (i z : U32) (a : address.Adrs) (lo : 1≤z.val) (hi : z.val≤9) (room : (i.val+1)*2^z.val≤512) :
    (x86 p).subtree sk seed i z a ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p)
      (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄ :=
  every_height _ p hp sk seed i z a lo hi room (Kxdispatch.permutation_correct on) (NativeVerify.x86 on)

end slhdsa.Buffered.Host
