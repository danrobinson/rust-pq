import Cachepath.PublicMut
import Cachepath.Constructor

open Aeneas Aeneas.Std Result slhdsa slhdsa.cache.endtoend
namespace CacheopsRust.Public
set_option linter.concreteInstances false
variable [backend : Closed.Backend]

structure Request (N : Usize) where
  message : Slice U8
  context : Slice U8
  randomness : Option (Array U8 N)

/-- The application can alternate deterministic and hedged messages on the same mutable cache. -/
def runRequests {N : Usize} [Builders N] (p : CacheopsRust.params.Params) (sk : Slice U8)
    (c : CacheopsRust.cache.TopTreeCache N) : List (Request N) →
    Result (List (Option (alloc.vec.Vec U8)) × CacheopsRust.cache.TopTreeCache N)
  | [] => ok ([],c)
  | q :: rest => do
    let (sig,next) ← match q.randomness with
      | some rnd => cache.sign_cached_mut p q.message q.context sk rnd c
      | none => cache.sign_deterministic_cached_mut p q.message q.context sk c
    let (sigs,last) ← runRequests p sk next rest
    ok (sig :: sigs,last)

def requestSpec {N : Usize} (P : Spec.Params) (sk : Slice U8) (q : Request N) :=
  Spec.slhSign P (bytes q.message.val) (bytes q.context.val) (bytes sk.val)
    (q.randomness.elim (Spec.block P (bytes sk.val) 2) fun r => bytes r.val)

theorem runRequests_spec {N : Usize} [Closed.DispatchCorrect backend N] [Builders N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (family : CacheopsRust.cache.HashFamily) (build : BuildersCorrect (N:=N) p family)
    (sk : Slice U8) (hs : sk.length = 4*N.val) (key : Spec.KeyOk (familyParams p family) (bytes sk.val))
    (c : CacheopsRust.cache.TopTreeCache N) (familyEq : c.family = family)
    (valid : CacheValid c (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
      (Spec.block (familyParams p family) (bytes sk.val) 2))
    (qs : List (Request N)) (room : ∀ q ∈ qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) :
    runRequests p sk c qs ⦃ out =>
      out.1.map (fun v => v.map fun sig => bytes sig.val) = qs.map (requestSpec (familyParams p family) sk) ∧
      out.2.family = family ∧ out.2.layer_d2_capacity = c.layer_d2_capacity ∧
      CacheValid out.2 (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
        (Spec.block (familyParams p family) (bytes sk.val) 2) ⦄ := by
  induction qs generalizing c with
  | nil => simp [runRequests, familyEq, valid]
  | cons q qs ih =>
    have one :
        (match q.randomness with
        | some rnd => cache.sign_cached_mut p q.message q.context sk rnd c
        | none => cache.sign_deterministic_cached_mut p q.message q.context sk c) ⦃ out =>
          out.1.map (fun v => bytes v.val) = requestSpec (familyParams p family) sk q ∧
          out.2.family = family ∧ out.2.layer_d2_capacity = c.layer_d2_capacity ∧
          CacheValid out.2 (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
            (Spec.block (familyParams p family) (bytes sk.val) 2) ⦄ := by
      subst family
      cases h : q.randomness with
      | some rnd => simpa only [requestSpec,h,Option.elim,MutPost] using
          sign_cached_mut_spec p hp c q.message q.context sk rnd build hs (room q (by simp)) key valid
      | none => simpa only [requestSpec,h,Option.elim,MutPost] using
          sign_deterministic_cached_mut_spec p hp c q.message q.context sk build hs (room q (by simp)) key valid
    obtain ⟨⟨sig,next⟩,h,exactSig,hf,hcap,hvalid⟩ := spec_imp_exists one
    obtain ⟨⟨sigs,last⟩,e,exactSigs,hf',hcap',hvalid'⟩ :=
      spec_imp_exists (ih next hf hvalid (fun item mem => room item (by simp [mem])))
    simp only [runRequests,h,e,bind_ok,uncurry,WP.spec_ok,List.map_cons,exactSig,exactSigs]
    exact ⟨trivial,hf',hcap'.trans hcap,hvalid'⟩

/-- Construct once with the given key, choose an MRU capacity, and produce the FIPS bytes for
every finite sequence of public messages, contexts, and deterministic or hedged randomness. -/
theorem new_then_sign_many {N : Usize} [Closed.DispatchCorrect backend N] [b : Builders N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) (family : CacheopsRust.cache.HashFamily)
    (sha2 : family = .Sha2 → CacheopsRust.cache.constructor.TreeKernel b.sha2 (familyParams p family))
    (shake : family = .Shake → CacheopsRust.cache.constructor.TreeKernel b.shake (familyParams p family))
    (capacity : Usize) (sk : Slice U8) (hs : sk.length = 4*N.val)
    (key : Spec.KeyOk (familyParams p family) (bytes sk.val))
    (qs : List (Request N)) (room : ∀ q ∈ qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) :
    (do let c ← CacheopsRust.cache.constructor.newCache N b.sha2 b.shake family p sk
        let c' ← CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity c capacity
        runRequests p sk c' qs) ⦃ out =>
      out.1.map (fun v => v.map fun sig => bytes sig.val) = qs.map (requestSpec (familyParams p family) sk) ∧
      out.2.family = family ∧ out.2.layer_d2_capacity = capacity ∧
      CacheValid out.2 (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
        (Spec.block (familyParams p family) (bytes sk.val) 2) ⦄ := by
  have hn : (familyParams p family).n = N.val := by cases family <;> exact hp.n
  have hd : p.d.val = (familyParams p family).d := by cases family <;> rfl
  have ht : p.hp.val = (familyParams p family).hp := by cases family <;> rfl
  have pos : 0 < (familyParams p family).d := by cases family <;> exact Nat.lt_of_lt_of_le (by decide : 0 < 2) hp.valid.d_ge
  have build : BuildersCorrect (N:=N) p family := by
    intro s k idx layer eq
    cases h : family with
    | Sha2 => simpa only [h,eq] using sha2 h p.hp layer idx s k ht
    | Shake => simpa only [h,eq] using shake h p.hp layer idx s k ht
  let* ⟨c,valid,hf,_,_,_⟩ ← CacheopsRust.cache.constructor.valid b.sha2 b.shake family p (familyParams p family)
    hp.n_eq.symm hn hd ht pos sk hs key sha2 shake
  have configure : CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity c capacity ⦃ next =>
      CacheValid next (familyParams p family) (Spec.block (familyParams p family) (bytes sk.val) 0)
        (Spec.block (familyParams p family) (bytes sk.val) 2) ∧
      next.layer_d2_capacity = capacity ∧ next.family = family ⦄ := by
    obtain ⟨next,he,va,cap,_⟩ := spec_imp_exists (with_capacity_preserves_valid valid capacity)
    rw [he, WP.spec_ok]
    refine ⟨va,cap,?_⟩
    unfold CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity CacheopsRust.cache.TopTreeCache.set_layer_d2_capacity at he
    dsimp only at he
    split at he <;> simp [alloc.vec.Vec.truncate,bind_ok] at he <;> subst next <;> exact hf
  let* ⟨next,va,cap,hf'⟩ ← configure
  simpa only [← cap] using runRequests_spec p hp family build sk hs key next hf' va qs room

end CacheopsRust.Public
