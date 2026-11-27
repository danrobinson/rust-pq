import Cachepath.ForsCallbacks
import Cachepath.WotsCallbacks
import Cachepath.Subtree
import Cachepath.KeygenVerify

open Aeneas Aeneas.Std Result slhdsa slhdsa.ShakeBatch slhdsa.cache.builder
namespace CacheopsRust.NativeSession
open nativeShake
set_option linter.concreteInstances false

variable [machine : Machine] [stream : Stream] [b : nativeShake.Backend] [s : Subtree.Single]

/-- Select the extracted packed WOTS, FORS and iterative XMSS programs together. -/
@[instance_reducible] noncomputable def backend : Closed.Backend where
  available := b.available
  wots_sign := ShakeBatch.shake.batch.sign
  wots_pk_from_sig := ShakeBatch.shake.batch.recover
  fors_sign := ShakeBatch.shake.fors_batch.sign
  fors_pk_from_sig := ShakeBatch.shake.fors_batch.recover
  subtree := fun sk i z seed a => Subtree.node sk i z seed (toSlhAdrs a)

variable [StreamCorrect]

theorem dispatch {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (detector : ∃ flag, b.available N = ok flag)
    (positive : b.available N = ok true → 0 < machine.width.val)
    (permutation : b.available N = ok true → PermutationCorrect)
    (rows : b.available N = ok true → Subtree.Ops b s (N:=N) p) :
    Closed.DispatchCorrect backend N := by
  refine ⟨detector, fun enabled => ?_⟩
  change b.available N = ok true at enabled
  exact ⟨WotsCallbacks.sign_eq p hp (positive enabled) (permutation enabled),
    WotsCallbacks.recover_eq p hp (positive enabled) (permutation enabled),
    fun q md sk seed a h size => ForsCallbacks.sign_eq q h (positive enabled) (permutation enabled) md sk seed a size,
    fun q sig md seed a h size len => ForsCallbacks.recover_eq q h (positive enabled) (permutation enabled) sig md seed a size len,
    fun sk i z seed a => Subtree.node_eq_scalar p hp (rows enabled) sk i z seed (toSlhAdrs a)⟩

omit machine stream [StreamCorrect] in
theorem builder {N : Usize} (detector : ∃ flag, b.available N = ok flag)
    (rows : b.available N = ok true → ∀ p, PN p N → Subtree.Ops b s (N:=N) p) :
    nativeShake.Correct b N := by
  refine ⟨detector, ?_, ?_⟩
  · intro enabled p hp sk pk a out size
    have bound : 2^p.hp.val ≤ 512 := Nat.pow_le_pow_right (by decide : 0 < 2) hp.valid.hp_le
    simpa using (rows enabled p hp).leaves sk pk a 0#usize out (by simpa [size] using bound)
  · intro enabled p hp sk pk a z children out pos le input size
    have bound : 2^p.hp.val ≤ 512 := Nat.pow_le_pow_right (by decide : 0 < 2) hp.valid.hp_le
    have fits : out.length * 2^z.val ≤ 512 := by
      rw [size,width,← pow_add,Nat.sub_add_cancel le]
      exact bound
    simpa using (rows enabled p hp).parents sk pk a z 0#usize children out pos
      (le.trans hp.valid.hp_le) (by simpa using fits) (by simpa [size] using input)

open CacheopsRust.Public CacheopsRust.cache.generatedKeys slhdsa.cache.endtoend

theorem keygen_sign_many {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (detector : ∃ flag, b.available N = ok flag)
    (positive : b.available N = ok true → 0 < machine.width.val)
    (permutation : b.available N = ok true → PermutationCorrect)
    (rows : b.available N = ok true → ∀ q, PN q N → Subtree.Ops b s (N:=N) q)
    (family : CacheopsRust.cache.HashFamily) (seeds sk pk : Slice U8)
    (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val) (ps : pk.length = 2*N.val)
    (capacity : Usize) (qs : List (Request N))
    (room : ∀ q ∈ qs, family = .Sha2 → Room q.message.length (msgSlack N.val+257)) :
    @generatedSession N backend (@extractedBuilders N b) family p seeds sk pk capacity qs
      ⦃ out => generatedSessionPost (familyParams p family) family seeds capacity qs out ⦄ := by
  apply @keygen_then_sign_many N backend (dispatch _ hp detector positive permutation (fun e => rows e _ hp))
    (@extractedBuilders N b) p hp
  · rintro rfl; exact sha2_kernel _ hp
  · rintro rfl; exact nativeShake.kernel (builder detector rows) _ hp
  all_goals assumption

theorem keygen_sign_verify_with_precompute (eager : Bool) {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (detector : ∃ flag, b.available N = ok flag)
    (positive : b.available N = ok true → 0 < machine.width.val)
    (permutation : b.available N = ok true → PermutationCorrect)
    (rows : b.available N = ok true → ∀ q, PN q N → Subtree.Ops b s (N:=N) q)
    (family : CacheopsRust.cache.HashFamily) (seeds sk pk m ctx : Slice U8) (rnd : Array U8 N)
    (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val) (ps : pk.length = 2*N.val)
    (short : ctx.length ≤ 255) (room : Room m.length (msgSlack N.val+257)) :
    (do let (c,secret,pub) ← keygen N slhdsa.cache.sha2_ops.build_xmss_tree
          (@slhdsa.cache.builder.nativeShake.build_xmss_tree b N) family p seeds sk pk
        let c ← if eager then (@cache.TopTreeCache.precompute_layer_d2 N
          (@extractedBuilders N b) c p secret) else ok c
        let sig ← @cache.sign_cached backend N p m ctx secret rnd c
        match sig with
        | none => ok false
        | some signature => @verifyGenerated N family (toSlhParams p) m signature.deref ctx pub) = ok true :=
  @Public.keygen_sign_verify_with_precompute eager N backend (dispatch _ hp detector positive permutation (fun e => rows e _ hp)) b
    (builder detector rows) p hp family seeds sk pk m ctx rnd ss ks ps short room

end CacheopsRust.NativeSession
