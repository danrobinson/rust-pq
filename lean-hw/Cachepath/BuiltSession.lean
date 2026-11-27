import Cachepath.PublicReuse
import Cachepath.Session
import Cachepath.BuilderSha2
import Cachepath.BuilderShake

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.Public
set_option linter.concreteInstances false
/-- Both the constructor and miss path use the actual extracted serial tree builders. -/
@[instance_reducible] def extractedBuilders (N : Usize) [slhdsa.cache.builder.nativeShake.Backend] : Builders N :=
  ⟨slhdsa.cache.sha2_ops.build_xmss_tree, slhdsa.cache.builder.nativeShake.build_xmss_tree⟩

section
variable [backend : Closed.Backend] [trees : slhdsa.cache.builder.nativeShake.Backend]

/-- Construct the cache and produce the FIPS signature for the same well-formed
private key. Neither tree validity nor a whole-tree builder contract is supplied
by the caller. SHAKE batch contracts apply only when the selected detector enables them. -/
theorem build_and_sign {N : Usize} [Closed.DispatchCorrect backend N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (family : CacheopsRust.cache.HashFamily)
    (shakeKernels : family = .Shake → slhdsa.cache.builder.nativeShake.Correct trees N)
    (m ctx sk : Slice U8) (rnd : Array U8 N) (hs : sk.length = 4 * N.val)
    (room : family = .Sha2 → Room m.length (msgSlack N.val + 257))
    (key : Spec.KeyOk (familyParams p family) (bytes sk.val)) :
    (do let c ← CacheopsRust.cache.constructor.newCache N
          slhdsa.cache.sha2_ops.build_xmss_tree slhdsa.cache.builder.nativeShake.build_xmss_tree family p sk
        cache.sign_cached p m ctx sk rnd c) ⦃ sig =>
      sig.map (fun v => bytes v.val) = Spec.slhSign (familyParams p family)
        (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes rnd.val) ⦄ := by
  apply new_then_sign _ hp
  · rintro rfl
    exact slhdsa.cache.builder.sha2_kernel _ hp
  · rintro rfl
    exact slhdsa.cache.builder.nativeShake.kernel (shakeKernels rfl) _ hp
  all_goals assumption


section
local instance (N : Usize) : Builders N := extractedBuilders N

theorem build_and_sign_many {N : Usize} [Closed.DispatchCorrect backend N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) (family : CacheopsRust.cache.HashFamily)
    (shakeKernels : family = .Shake → slhdsa.cache.builder.nativeShake.Correct trees N)
    (capacity : Usize) (sk : Slice U8) (hs : sk.length = 4*N.val)
    (key : Spec.KeyOk (familyParams p family) (bytes sk.val)) (qs : List (Request N))
    (room : ∀ q ∈ qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) :
    (do let c ← CacheopsRust.cache.constructor.newCache N slhdsa.cache.sha2_ops.build_xmss_tree
          slhdsa.cache.builder.nativeShake.build_xmss_tree family p sk
        let c' ← CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity c capacity
        runRequests p sk c' qs) ⦃ out =>
      out.1.map (fun v => v.map fun sig => bytes sig.val) = qs.map (requestSpec (familyParams p family) sk) ∧
      out.2.family = family ∧ out.2.layer_d2_capacity = capacity ∧
      slhdsa.cache.endtoend.CacheValid out.2 (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
        (Spec.block (familyParams p family) (bytes sk.val) 2) ⦄ := by
  apply new_then_sign_many p hp family _ _ capacity sk hs key qs room
  · rintro rfl; exact slhdsa.cache.builder.sha2_kernel _ hp
  · rintro rfl; exact slhdsa.cache.builder.nativeShake.kernel (shakeKernels rfl) _ hp

end

end

/-- The concrete scalar configuration satisfies both dispatch interfaces unconditionally. -/
theorem scalar_build_and_sign_many {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N) (family : CacheopsRust.cache.HashFamily)
    (capacity : Usize) (sk : Slice U8) (hs : sk.length = 4*N.val)
    (key : Spec.KeyOk (familyParams p family) (bytes sk.val)) (qs : List (Request N))
    (room : ∀ q ∈ qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) :
    (do let c ← CacheopsRust.cache.constructor.newCache N slhdsa.cache.sha2_ops.build_xmss_tree
          (@slhdsa.cache.builder.nativeShake.build_xmss_tree slhdsa.cache.builder.nativeShake.scalar N) family p sk
        let c' ← CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity c capacity
        @runRequests Closed.scalar N (@extractedBuilders N slhdsa.cache.builder.nativeShake.scalar) p sk c' qs) ⦃ out =>
      out.1.map (fun v => v.map fun sig => bytes sig.val) = qs.map (requestSpec (familyParams p family) sk) ∧
      out.2.family = family ∧ out.2.layer_d2_capacity = capacity ∧
      slhdsa.cache.endtoend.CacheValid out.2 (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
        (Spec.block (familyParams p family) (bytes sk.val) 2) ⦄ :=
  @build_and_sign_many Closed.scalar slhdsa.cache.builder.nativeShake.scalar N _ p hp family
    (fun _ => slhdsa.cache.builder.nativeShake.scalar_correct N) capacity sk hs key qs room

end CacheopsRust.Public
