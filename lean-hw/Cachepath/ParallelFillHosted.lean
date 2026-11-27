import Cachepath.ParallelFillWorkers
import Cachepath.NativeReuse
open Aeneas Aeneas.Std Result slhdsa slhdsa.ShakeBatch slhdsa.cache.builder
namespace CacheopsRust.NativeSession
open nativeShake CacheopsRust.Public slhdsa.cache.endtoend workers
set_option linter.concreteInstances false

/-- The constructor uses the parallel-feature tree builders. The cache miss path
during later requests uses the same constructors. -/
noncomputable def ParallelBuild [machine : Machine] [stream : Stream] (probe : Result Bool) {N : Usize}
    (p : CacheopsRust.params.Params) : Prop :=
  let b := @Vector.backend machine (@Vector.Fused.leaves machine) (ShakeBatch.shake.batch.available probe)
  ∀ (threads : Usize) (family : CacheopsRust.cache.HashFamily)
    (capacity : Usize) (sk : Slice U8) (qs : List (Request N)), sk.length = 4*N.val →
    Spec.KeyOk (familyParams p family) (bytes sk.val) →
    (∀ q∈qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) →
    let pool := @fill.pool b threads
    let builders : Builders N := ⟨@sha2Tree pool N,@shakeTree pool b N⟩
    (do let c ← CacheopsRust.cache.constructor.newCache N (@sha2Tree pool N) (@shakeTree pool b N) family p sk
        let c' ← CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity c capacity
        @runRequests (@backend machine stream b Vector.single) N builders p sk c' qs) ⦃ out =>
      out.1.map (fun v => v.map fun sig => bytes sig.val) = qs.map (requestSpec (familyParams p family) sk) ∧
      out.2.family=family ∧ out.2.layer_d2_capacity=capacity ∧
      CacheValid out.2 (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
        (Spec.block (familyParams p family) (bytes sk.val) 2) ⦄

private theorem parallelBuild [machine : Machine] [stream : Stream] [StreamCorrect] {N : Usize}
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) (probe : Result Bool) (flag : Bool)
    (actual : probe = ok flag) (pos : 0<machine.width.val) (width : machine.width.val≤8)
    (permutes : flag=true → PermutationCorrect) : ParallelBuild (N:=N) probe p := by
  let b := @Vector.backend machine (@Vector.Fused.leaves machine) (ShakeBatch.shake.batch.available probe)
  have det : b.available N = ok flag := (available_for_fips probe _ hp).trans actual
  have active (h : b.available N = ok true) := Result.ok_injective (det.symm.trans h)
  have ops (h : b.available N = ok true) (q : slhdsa.params.Params) (hq : PN q N) :
      Subtree.Ops b Vector.single (N:=N) q :=
    @Vector.ops machine (@Vector.Fused.leaves machine) stream _ N q hq pos width (permutes (active h))
      (Vector.Fused.correct q hq (permutes (active h))) _
  intro threads family capacity sk qs size key room
  apply @parallel_build_and_sign_many (@backend machine stream b Vector.single) (@fill.pool b threads) b N
    (@dispatch machine stream b Vector.single _ N _ hp ⟨flag,det⟩ (fun _ => pos) (fun h => permutes (active h))
      (fun h => ops h _ hp)) p hp family (@fill.pool_correct b Vector.single threads N ⟨flag,det⟩ ops)
    (fun _ => @builder b Vector.single N ⟨flag,det⟩ ops) capacity sk size key qs room

theorem linuxArm_parallelBuild {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @ParallelBuild Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream KldispRust.shake256.parallel.available N p :=
  @parallelBuild Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect
    N p hp _ true rfl (by decide) (by decide) (fun _ => Kldisp.permutation_correct)

theorem linuxX86_parallelBuild {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @ParallelBuild Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream KxdispatchRust.shake256.parallel.available N p :=
  @parallelBuild Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect
    N p hp _ GatherRust.avx512Available rfl (by decide) (by decide) Kxdispatch.permutation_correct

theorem apple_parallelBuild (sha3 : Bool) {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @ParallelBuild (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream (ok true) N p :=
  @parallelBuild (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect
    N p hp _ true rfl (by change 0 < 8; decide) (by change 8 ≤ 8; decide) (fun _ => AppleHybrid.permutation_correct sha3)

end CacheopsRust.NativeSession
