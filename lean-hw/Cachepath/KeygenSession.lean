import Cachepath.Keygen

open Aeneas Aeneas.Std Result slhdsa slhdsa.cache.endtoend
namespace CacheopsRust.Public
open CacheopsRust.cache.generatedKeys
set_option linter.concreteInstances false

theorem familyParams_valid {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (family : CacheopsRust.cache.HashFamily) : (familyParams p family).Valid := by
  have hv := hp.valid
  cases family
  · exact hv
  · cases hv; constructor <;> assumption

/-- Outputs include both generated key buffers and every signature returned to the caller. -/
def generatedSession {N : Usize} [Closed.Backend] [b : Builders N]
    (family : CacheopsRust.cache.HashFamily) (p : CacheopsRust.params.Params)
    (seeds sk pk : Slice U8) (capacity : Usize) (qs : List (Request N)) : Result (Slice U8 × Slice U8 × List (Option (alloc.vec.Vec U8)) × CacheopsRust.cache.TopTreeCache N) := do
  let (c,secret,pub) ← keygen N b.sha2 b.shake family p seeds sk pk
  let next ← CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity c capacity
  let (sigs,last) ← runRequests p secret next qs
  ok (secret,pub,sigs,last)

def generatedSessionPost {N : Usize} (P : Spec.Params) (family : CacheopsRust.cache.HashFamily)
    (seeds : Slice U8) (capacity : Usize) (qs : List (Request N))
    (out : Slice U8 × Slice U8 × List (Option (alloc.vec.Vec U8)) × CacheopsRust.cache.TopTreeCache N) :=
  let (sk,pk,sigs,last) := out
  (bytes sk.val,bytes pk.val) = specKeys P seeds ∧
  sigs.map (fun (v : Option (alloc.vec.Vec U8)) => v.map fun (sig : alloc.vec.Vec U8) => bytes sig.val) = qs.map (fun (q : Request N) =>
    let secret := (specKeys P seeds).1
    Spec.slhSign P (bytes q.message.val) (bytes q.context.val) secret
      (q.randomness.elim (Spec.block P secret 2) fun r => bytes r.val)) ∧
  last.family = family ∧ last.layer_d2_capacity = capacity ∧
  CacheValid last P (Spec.block P (specKeys P seeds).1 0) (Spec.block P (specKeys P seeds).1 2)

set_option maxHeartbeats 2000000 in
theorem keygen_then_sign_many {N : Usize} [backend : Closed.Backend] [Closed.DispatchCorrect backend N] [b : Builders N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) (family : CacheopsRust.cache.HashFamily)
    (sha2 : family = .Sha2 → CacheopsRust.cache.constructor.TreeKernel b.sha2 (familyParams p family))
    (shake : family = .Shake → CacheopsRust.cache.constructor.TreeKernel b.shake (familyParams p family))
    (seeds sk pk : Slice U8) (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val)
    (ps : pk.length = 2*N.val) (capacity : Usize) (qs : List (Request N))
    (room : ∀ q ∈ qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) :
    generatedSession family p seeds sk pk capacity qs ⦃ out => generatedSessionPost (familyParams p family) family seeds capacity qs out ⦄ := by
  have hn : (familyParams p family).n = N.val := by cases family <;> exact hp.n
  have hd : p.d.val = (familyParams p family).d := by cases family <;> rfl
  have ht : p.hp.val = (familyParams p family).hp := by cases family <;> rfl
  have pv := familyParams_valid p hp family
  have build : BuildersCorrect (N:=N) p family := by
    intro s k idx layer eq
    cases h : family with
    | Sha2 => simpa only [h,eq] using sha2 h p.hp layer idx s k ht
    | Shake => simpa only [h,eq] using shake h p.hp layer idx s k ht
  obtain ⟨⟨c,secret,pub⟩,gen,g⟩ := spec_imp_exists (keygen_spec b.sha2 b.shake family p _
    hp.n_eq.symm hn hd ht pv sha2 shake seeds sk pk ss ks ps)
  obtain ⟨next,configure,va,cap,_⟩ := spec_imp_exists (with_capacity_preserves_valid g.valid capacity)
  have hf : next.family = family := by
    unfold CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity CacheopsRust.cache.TopTreeCache.set_layer_d2_capacity at configure
    dsimp only at configure
    split at configure <;> simp [alloc.vec.Vec.truncate,bind_ok] at configure <;> subst next <;> exact g.familyEq
  obtain ⟨⟨sigs,last⟩,run,sg,lastFamily,lastCap,lastValid⟩ :=
    spec_imp_exists (runRequests_spec p hp family build secret g.secretLength g.wellFormed next hf va qs room)
  simp only [generatedSession,gen,configure,run,bind_ok,uncurry,WP.spec_ok,generatedSessionPost]
  have keyEq : bytes secret.val = (specKeys (familyParams p family) seeds).1 := congrArg Prod.fst g.keys
  refine ⟨g.keys,?_,lastFamily,lastCap.trans cap,?_⟩ <;> rw [← keyEq]
  · exact sg
  · exact lastValid

/-- On the portable scalar backend no tree, feature-dispatch, cache-validity, or well-formed-key hypothesis is needed. -/
theorem scalar_keygen_then_sign_many {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N) (family : CacheopsRust.cache.HashFamily)
    (seeds sk pk : Slice U8) (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val)
    (ps : pk.length = 2*N.val) (capacity : Usize) (qs : List (Request N))
    (room : ∀ q ∈ qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) :
    @generatedSession N Closed.scalar (@extractedBuilders N slhdsa.cache.builder.nativeShake.scalar)
      family p seeds sk pk capacity qs ⦃ out => generatedSessionPost (familyParams p family) family seeds capacity qs out ⦄ := by
  apply @keygen_then_sign_many N Closed.scalar _ (@extractedBuilders N slhdsa.cache.builder.nativeShake.scalar) p hp
  · rintro rfl; exact slhdsa.cache.builder.sha2_kernel _ hp
  · rintro rfl; exact @slhdsa.cache.builder.nativeShake.kernel N slhdsa.cache.builder.nativeShake.scalar (slhdsa.cache.builder.nativeShake.scalar_correct N) _ hp
  all_goals assumption

end CacheopsRust.Public
