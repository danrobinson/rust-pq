import Buffered.SignHost
import Buffered.Entry

open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered.Host
open ShakeBatch NativeVerify
set_option linter.concreteInstances false

/-- Key generation also requests the two- and four-key bottom subtrees. Every
positive height uses the same extracted dispatcher as the signing path. -/
theorem nodes (k : Fused.Kernel) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (i z : U32) (a : address.Adrs) (lo : 1≤z.val) (hi : z.val≤9)
    (room : (i.val+1)*2^z.val≤512) (perms : Fused.Permutes k)
    (active : ActiveCorrect (Fused.machine k) k.active) (small : @SmallLeaves (ops k) N p sk seed a) :
    (signing k).subtree sk seed i z a ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p)
      (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄ := by
  have large : @FullLeaves (ops k) N p sk seed a := all_eight k (@SmallWots.leaves k) p hp sk seed a perms
  have mixed : ActiveCorrect (machine (ops k)) (ops k).active := active
  exact @subtree_spec (ops k) N p hp sk seed i z a lo hi room small mixed
    (fun height => @process_at (ops k) N p hp sk seed a i z height hi room large mixed)

end slhdsa.Buffered.Host
