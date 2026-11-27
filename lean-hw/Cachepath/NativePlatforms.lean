import Cachepath.NativeSession
import Cachepath.WotsFused
import Cachepath.WotsPlatforms
import Cachepath.WotsRows
import Shakebatch.Available
import Shakebatch.AppleStream
import Cachepath.AppleHybrid

open Aeneas Aeneas.Std Result slhdsa slhdsa.ShakeBatch slhdsa.cache.builder
namespace CacheopsRust.NativeSession
open nativeShake CacheopsRust.Public CacheopsRust.cache.generatedKeys slhdsa.cache.endtoend
set_option linter.concreteInstances false

/-- Seeded key generation, optional eager precomputation, signing and portable verification. -/
def RoundTrip [machine : Machine] [stream : Stream] (b : nativeShake.Backend) {N : Usize}
    (p : CacheopsRust.params.Params) : Prop :=
  ∀ (eager : Bool) (seeds sk pk m ctx : Slice U8) (rnd : Array U8 N),
    seeds.length = 3*N.val → sk.length = 4*N.val → pk.length = 2*N.val →
    ctx.length ≤ 255 → Room m.length (msgSlack N.val+257) →
    (do let (c,secret,pub) ← keygen N slhdsa.cache.sha2_ops.build_xmss_tree
          (@nativeShake.build_xmss_tree b N) .Shake p seeds sk pk
        let c ← if eager then (@cache.TopTreeCache.precompute_layer_d2 N
          (@extractedBuilders N b) c p secret) else ok c
        let sig ← @cache.sign_cached (@backend machine stream b Vector.single) N p m ctx secret rnd c
        match sig with
        | none => ok false
        | some signature => @verifyGenerated N .Shake (toSlhParams p) m signature.deref ctx pub) = ok true

private theorem roundTrip [machine : Machine] [stream : Stream] [StreamCorrect] [Vector.Leaves machine] {N : Usize}
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (hardware : Bool) (probe : Result Bool) (probed : probe = ok hardware)
    (pos : 0 < machine.width.val) (width : machine.width.val ≤ 8)
    (permutation : hardware = true → PermutationCorrect)
    (leaves : hardware = true → ∀ q, PN q N → Vector.LeavesCorrect (N:=N) q) :
    RoundTrip (N:=N) (Vector.backend (ShakeBatch.shake.batch.available probe)) p := by
  have det : (Vector.backend (ShakeBatch.shake.batch.available probe)).available N = ok hardware :=
    (available_for_fips probe _ hp).trans probed
  have active (h : (Vector.backend (ShakeBatch.shake.batch.available probe)).available N = ok true) : hardware = true :=
    Result.ok_injective (det.symm.trans h)
  intro eager seeds sk pk m ctx rnd ss ks ps short room
  apply @keygen_sign_verify_with_precompute machine stream (Vector.backend (ShakeBatch.shake.batch.available probe)) Vector.single _ eager N p hp
    ⟨hardware,det⟩ (fun _ => pos) (fun h => permutation (active h)) _ .Shake seeds sk pk m ctx rnd ss ks ps short room
  intro h q hq
  exact Vector.ops q hq pos width (permutation (active h)) (leaves (active h) q hq) _

theorem linuxArm [Vector.Leaves Kldisp.machine] {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (leaves : ∀ q, PN q N → @Vector.LeavesCorrect Kldisp.machine _ N q) :
    @RoundTrip Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream
      (@Vector.backend Kldisp.machine _ (ShakeBatch.shake.batch.available KldispRust.shake256.parallel.available)) N p :=
  @roundTrip Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect _ N p hp true _
    rfl (by decide) (by decide) (fun _ => Kldisp.permutation_correct) (fun _ => leaves)

theorem linuxX86 [Vector.Leaves Kxdispatch.machine] {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (leaves : GatherRust.avx512Available = true → ∀ q, PN q N → @Vector.LeavesCorrect Kxdispatch.machine _ N q) :
    @RoundTrip Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream
      (@Vector.backend Kxdispatch.machine _ (ShakeBatch.shake.batch.available KxdispatchRust.shake256.parallel.available)) N p :=
  @roundTrip Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect _ N p hp
    GatherRust.avx512Available _ rfl (by decide) (by decide) Kxdispatch.permutation_correct leaves

theorem appleArm (sha3 : Bool) [Vector.Leaves (AppleHybrid.machine sha3)] {N : Usize}
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (leaves : ∀ q, PN q N → @Vector.LeavesCorrect (AppleHybrid.machine sha3) _ N q) :
    @RoundTrip (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream
      (@Vector.backend (AppleHybrid.machine sha3) _ (ShakeBatch.shake.batch.available (ok true))) N p :=
  @roundTrip (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream
    ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect _ N p hp true _ rfl (by change 0 < 8; decide) (by change 8 ≤ 8; decide)
    (fun _ => AppleHybrid.permutation_correct sha3) (fun _ => leaves)

/-- The verified fused WOTS generator discharges the last batched leaf premise. -/
theorem linuxArmFull {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @RoundTrip Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream
      (@Vector.backend Kldisp.machine (@Vector.Fused.leaves Kldisp.machine) (ShakeBatch.shake.batch.available KldispRust.shake256.parallel.available)) N p :=
  @linuxArm (@Vector.Fused.leaves Kldisp.machine) N p hp (fun q hq => @Vector.Fused.correct Kldisp.machine N q hq Kldisp.permutation_correct)

theorem linuxX86Full {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @RoundTrip Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream
      (@Vector.backend Kxdispatch.machine (@Vector.Fused.leaves Kxdispatch.machine) (ShakeBatch.shake.batch.available KxdispatchRust.shake256.parallel.available)) N p :=
  @linuxX86 (@Vector.Fused.leaves Kxdispatch.machine) N p hp (fun enabled q hq => @Vector.Fused.correct Kxdispatch.machine N q hq (Kxdispatch.permutation_correct enabled))

theorem appleFull (sha3 : Bool) {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @RoundTrip (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream
      (@Vector.backend (AppleHybrid.machine sha3) (@Vector.Fused.leaves (AppleHybrid.machine sha3)) (ShakeBatch.shake.batch.available (ok true))) N p :=
  @appleArm sha3 (@Vector.Fused.leaves (AppleHybrid.machine sha3)) N p hp (fun q hq => @Vector.Fused.correct (AppleHybrid.machine sha3) N q hq (AppleHybrid.permutation_correct sha3))

end CacheopsRust.NativeSession
