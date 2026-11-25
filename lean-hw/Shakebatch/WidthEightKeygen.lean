import Shakebatch.WidthEightOuter
import Fused.OuterNode
import Cachepath.NativeShakeWots.KeyEntry

open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight
open ParallelKeygenHost
set_option linter.concreteInstances false

abbrev NodeResult {N : Usize} (p : params.Params) (sk seed : Array U8 N) (i z : U32)
    (a : address.Adrs) (r : Result (Array U8 N)) :=
  r ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄

def AllNodes (host : Platform) {N : Usize} (p : params.Params) :=
  ∀ (sk seed : Array U8 N) (i z : U32) (a : address.Adrs), host.available N=true →
    1≤z.val → z.val≤9 → (i.val+1)*2^z.val≤512 →
    NodeResult p sk seed i z a ((host.fused p).subtree sk seed i z a)

@[instance_reducible] noncomputable def sourceEngine (host : Platform) (p : params.Params) : Engine ShakeSeed :=
  Fused.Outer.keyEngine (host.outer p)

theorem source_keys {N : Usize} (p : params.Params) (hp : PN p N) (host : Platform)
    (x86 : Bool) (threads : Nat) (pool : PoolOutcome) (nodes : AllNodes host (N:=N) p) :
    ShNode.KeyPair (sourceEngine host p) x86 threads pool (N:=N) p := by
  apply Fused.Outer.keypair (host.outer p) p hp x86 threads pool
  intro sk i z seed a room
  apply @Fused.Outer.node_spec (host.outer p) N p hp sk seed i z a (host.available N) (probe_eq host N) room
  · intro enabled addr typ w2 w3
    cases host with
    | apple sha3 =>
      exact @NativeShakeWots.keygen_spec (AppleHybrid.machine sha3) ⟨NativeVerify.appleActive sha3⟩
        AppleSingleStream.ShakeForestApple.slhdsa.ShakeBatch.scalarStream
        AppleSingleStream.ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect N p hp sk seed addr
        ⟨typ,w2,w3⟩ (by change 0<8; decide) (NativeVerify.apple sha3)
    | x86 =>
      exact @NativeShakeWots.keygen_spec Kxdispatch.machine
        ⟨NativeVerify.fullActive _ KxdispatchRust.shake256.parallel.available⟩
        ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect
        N p hp sk seed addr ⟨typ,w2,w3⟩ (by decide) (NativeVerify.x86 (Bool.and_eq_true_iff.mp enabled).2)
  · intro on pos cap
    exact nodes sk seed i z a on pos cap room

end slhdsa.WidthEight
