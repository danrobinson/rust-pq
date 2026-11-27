import Cachepath.NativePlatforms

open Aeneas Aeneas.Std Result slhdsa slhdsa.ShakeBatch slhdsa.cache.builder
namespace CacheopsRust.NativeSession
open nativeShake CacheopsRust.Public CacheopsRust.cache.generatedKeys slhdsa.cache.endtoend
set_option linter.concreteInstances false

/-- Production packed callbacks and tree builders persist the cache across an arbitrary request list. -/
noncomputable def Reuse [machine : Machine] [stream : Stream] (probe : Result Bool) {N : Usize}
    (p : CacheopsRust.params.Params) : Prop :=
  let b := @Vector.backend machine (@Vector.Fused.leaves machine) (ShakeBatch.shake.batch.available probe)
  ∀ (seeds sk pk : Slice U8) (capacity : Usize) (qs : List (Request N)),
    seeds.length = 3*N.val → sk.length = 4*N.val → pk.length = 2*N.val →
    @generatedSession N (@backend machine stream b Vector.single) (@extractedBuilders N b)
      .Shake p seeds sk pk capacity qs ⦃ out => generatedSessionPost (familyParams p .Shake) .Shake seeds capacity qs out ⦄

private theorem reuse [machine : Machine] [stream : Stream] [StreamCorrect] {N : Usize}
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) (probe : Result Bool) (flag : Bool)
    (actual : probe = ok flag) (pos : 0<machine.width.val) (width : machine.width.val≤8)
    (permutes : flag=true → PermutationCorrect) : Reuse (N:=N) probe p := by
  let b := @Vector.backend machine (@Vector.Fused.leaves machine) (ShakeBatch.shake.batch.available probe)
  have det : b.available N = ok flag := (available_for_fips probe _ hp).trans actual
  have active (h : b.available N = ok true) := Result.ok_injective (det.symm.trans h)
  have rows (h : b.available N = ok true) (q : slhdsa.params.Params) (hq : PN q N) :
      Subtree.Ops b Vector.single (N:=N) q :=
    @Vector.ops machine (@Vector.Fused.leaves machine) stream _ N q hq pos width (permutes (active h))
      (Vector.Fused.correct q hq (permutes (active h))) _
  intro seeds sk pk capacity qs ss ks ps
  exact @keygen_sign_many machine stream b Vector.single _ N p hp ⟨flag,det⟩ (fun _ => pos)
    (fun h => permutes (active h)) rows .Shake seeds sk pk ss ks ps capacity qs (by simp)

theorem linuxArm_reuse {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @Reuse Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream KldispRust.shake256.parallel.available N p :=
  @reuse Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect
    N p hp _ true rfl (by decide) (by decide) (fun _ => Kldisp.permutation_correct)

theorem linuxX86_reuse {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @Reuse Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream KxdispatchRust.shake256.parallel.available N p :=
  @reuse Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect
    N p hp _ GatherRust.avx512Available rfl (by decide) (by decide) Kxdispatch.permutation_correct

theorem apple_reuse (sha3 : Bool) {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) :
    @Reuse (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream (ok true) N p :=
  @reuse (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect
    N p hp _ true rfl (by change 0 < 8; decide) (by change 8 ≤ 8; decide) (fun _ => AppleHybrid.permutation_correct sha3)

end CacheopsRust.NativeSession
