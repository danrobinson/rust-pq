import Cachepath.Constructor
import Cachepath.Public

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.Public

set_option linter.concreteInstances false
variable [backend : Closed.Backend]

/-- Construct the cache from the same secret key that is passed to the public
signer. Only the kernel selected by the constructor owes a tree contract. -/
theorem new_then_sign {N : Usize} [Closed.DispatchCorrect backend N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (family : CacheopsRust.cache.HashFamily) (sha2 shake : CacheopsRust.cache.mutation.Builder N)
    (buildSha2 : family = .Sha2 → CacheopsRust.cache.constructor.TreeKernel sha2 (familyParams p family))
    (buildShake : family = .Shake → CacheopsRust.cache.constructor.TreeKernel shake (familyParams p family))
    (m ctx sk : Slice U8) (rnd : Array U8 N) (hs : sk.length = 4 * N.val)
    (room : family = .Sha2 → Room m.length (msgSlack N.val + 257))
    (key : Spec.KeyOk (familyParams p family) (bytes sk.val)) :
    (do let c ← CacheopsRust.cache.constructor.newCache N sha2 shake family p sk
        cache.sign_cached p m ctx sk rnd c) ⦃ sig =>
      sig.map (fun v => bytes v.val) = Spec.slhSign (familyParams p family)
        (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes rnd.val) ⦄ := by
  have hn : (familyParams p family).n = N.val := by cases family <;> exact hp.n
  have hd : p.d.val = (familyParams p family).d := by cases family <;> rfl
  have height : p.hp.val = (familyParams p family).hp := by cases family <;> rfl
  have pos : 0 < (familyParams p family).d := by cases family <;> exact Nat.lt_of_lt_of_le (by decide : 0 < 2) hp.valid.d_ge
  let* ⟨c,valid,hf,_,_,_⟩ ← CacheopsRust.cache.constructor.valid sha2 shake family p (familyParams p family)
    hp.n_eq.symm hn hd height pos sk hs key buildSha2 buildShake
  subst family
  exact sign_cached_spec p hp c m ctx sk rnd hs room key valid

end CacheopsRust.Public
