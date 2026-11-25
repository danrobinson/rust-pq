import Cachepath.KeygenSession
import Cachepath.Precompute
import Portableplatform.Public
import Shakebatch.PortableSegmented

open Aeneas Aeneas.Std Result slhdsa slhdsa.cache.endtoend
namespace CacheopsRust.Public
open CacheopsRust.cache.generatedKeys

/-- Run the segmented portable verifier for the same hash family as key generation. -/
noncomputable def verifyGenerated {N : Usize} (family : CacheopsRust.cache.HashFamily)
    (p : slhdsa.params.Params) (m sig ctx pk : Slice U8) : Result Bool :=
  match family with
  | .Sha2 => PortableMessage.slhdsa.SegmentedApi.Program.slh.slh_verify N p m sig ctx pk
  | .Shake => PortableSegmented.SegmentedPublic.slhdsa.shake.api.verify N p m sig ctx pk

theorem verifyGenerated_spec {N : Usize} (family : CacheopsRust.cache.HashFamily)
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N) (m sig ctx pk : Slice U8)
    (hpk : pk.length = 2*N.val) (room : Room m.length (msgSlack N.val+257)) :
    @verifyGenerated N family (toSlhParams p) m sig ctx pk ⦃ result => result =
      Spec.slhVerify (familyParams p family) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  cases family
  · exact PortableMessage.slhdsa.SegmentedApi.verify_spec _ hp m sig ctx pk hpk room
  · exact PortableSegmented.SegmentedPublic.slhdsa.Shake.api_verify_spec _ hp m sig ctx pk hpk room

set_option maxHeartbeats 2000000 in
theorem keygen_sign_verify_with_precompute (eager : Bool) {N : Usize}
    [dispatch : Closed.Backend] [Closed.DispatchCorrect dispatch N] [builder : slhdsa.cache.builder.nativeShake.Backend]
    (correct : slhdsa.cache.builder.nativeShake.Correct builder N) (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (family : CacheopsRust.cache.HashFamily) (seeds sk pk m ctx : Slice U8) (rnd : Array U8 N)
    (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val) (ps : pk.length = 2*N.val)
    (short : ctx.length ≤ 255) (room : Room m.length (msgSlack N.val+257)) :
    (do let (c,secret,pub) ← keygen N slhdsa.cache.sha2_ops.build_xmss_tree
          (@slhdsa.cache.builder.nativeShake.build_xmss_tree builder N) family p seeds sk pk
        let c ← if eager then (@cache.TopTreeCache.precompute_layer_d2 N
          (@extractedBuilders N builder) c p secret) else ok c
        let sig ← @cache.sign_cached dispatch N p m ctx secret rnd c
        match sig with
        | none => ok false
        | some signature => @verifyGenerated N family (toSlhParams p) m signature.deref ctx pub) = ok true := by
  have hn : (familyParams p family).n = N.val := by cases family <;> exact hp.n
  have hd : p.d.val = (familyParams p family).d := by cases family <;> rfl
  have ht : p.hp.val = (familyParams p family).hp := by cases family <;> rfl
  have pv := familyParams_valid p hp family
  obtain ⟨⟨c,secret,pub⟩,gen,g⟩ := spec_imp_exists (keygen_spec _ _ family p _ hp.n_eq.symm hn hd ht pv
    (by rintro rfl; exact slhdsa.cache.builder.sha2_kernel _ hp)
    (by rintro rfl; exact @slhdsa.cache.builder.nativeShake.kernel N builder
          (correct) _ hp) seeds sk pk ss ks ps)
  have hf := g.familyEq
  let b := @extractedBuilders N builder
  have prepare : (if eager then @cache.TopTreeCache.precompute_layer_d2 N b c p secret else ok c) ⦃ c' =>
      c'.family = family ∧ CacheValid c' (familyParams p family)
        (Spec.block (familyParams p family) (bytes secret.val) 0)
        (Spec.block (familyParams p family) (bytes secret.val) 2) ⦄ := by
    cases eager
    · simp only [Bool.false_eq_true, ite_false, WP.spec_ok]; exact ⟨hf,g.valid⟩
    · apply WP.spec_mono (@precompute_spec N b p hp c secret g.secretLength (hf ▸ g.wellFormed)
          (hf ▸ g.valid) (by intro eq; rw [eq]; exact slhdsa.cache.builder.sha2_kernel _ hp)
          (by intro eq; rw [eq]; exact @slhdsa.cache.builder.nativeShake.kernel N builder (correct) _ hp))
      rintro next ⟨valid,tag,_⟩
      exact ⟨tag.trans hf,hf ▸ valid⟩
  obtain ⟨warm,prepared,tag,valid⟩ := spec_imp_exists prepare
  obtain ⟨sig,sign,signBytes⟩ := spec_imp_exists (@sign_cached_spec dispatch N _ p hp warm m ctx secret rnd
    g.secretLength (fun _ => room) (tag ▸ g.wellFormed) (tag ▸ valid))
  rw [tag] at signBytes
  have size : (bytes ctx.val).length ≤ 255 := by simpa [bytes] using short
  obtain ⟨expected,produced,accept⟩ := Spec.slh_complete _ pv (bytes m.val) (bytes ctx.val) (bytes secret.val)
    (bytes rnd.val) size g.wellFormed
  rw [produced] at signBytes
  cases sig with
  | none => contradiction
  | some sig =>
    have eq : bytes sig.val = expected := Option.some.inj signBytes
    obtain ⟨result,verified,hr⟩ := spec_imp_exists (verifyGenerated_spec family p hp m sig.deref ctx pub g.publicLength room)
    rw [vec_deref_val,eq,g.publicKey,accept] at hr
    simp only [gen,bind_ok,uncurry,prepared,sign,verified,hr]

theorem scalar_keygen_sign_verify_with_precompute (eager : Bool) {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (family : CacheopsRust.cache.HashFamily) (seeds sk pk m ctx : Slice U8) (rnd : Array U8 N)
    (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val) (ps : pk.length = 2*N.val)
    (short : ctx.length ≤ 255) (room : Room m.length (msgSlack N.val+257)) :
    (do let (c,secret,pub) ← keygen N slhdsa.cache.sha2_ops.build_xmss_tree
          (@slhdsa.cache.builder.nativeShake.build_xmss_tree slhdsa.cache.builder.nativeShake.scalar N) family p seeds sk pk
        let c ← if eager then (@cache.TopTreeCache.precompute_layer_d2 N
          (@extractedBuilders N slhdsa.cache.builder.nativeShake.scalar) c p secret) else ok c
        let sig ← @cache.sign_cached Closed.scalar N p m ctx secret rnd c
        match sig with
        | none => ok false
        | some signature => @verifyGenerated N family (toSlhParams p) m signature.deref ctx pub) = ok true :=
  @keygen_sign_verify_with_precompute eager N Closed.scalar _ slhdsa.cache.builder.nativeShake.scalar
    (slhdsa.cache.builder.nativeShake.scalar_correct N) p hp family seeds sk pk m ctx rnd ss ks ps short room

theorem scalar_keygen_sign_verify {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (family : CacheopsRust.cache.HashFamily) (seeds sk pk m ctx : Slice U8) (rnd : Array U8 N)
    (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val) (ps : pk.length = 2*N.val)
    (short : ctx.length ≤ 255) (room : Room m.length (msgSlack N.val+257)) :
    (do let (c,secret,pub) ← keygen N slhdsa.cache.sha2_ops.build_xmss_tree
          (@slhdsa.cache.builder.nativeShake.build_xmss_tree slhdsa.cache.builder.nativeShake.scalar N) family p seeds sk pk
        let sig ← @cache.sign_cached Closed.scalar N p m ctx secret rnd c
        match sig with
        | none => ok false
        | some signature => @verifyGenerated N family (toSlhParams p) m signature.deref ctx pub) = ok true :=
  by simpa only [Bool.false_eq_true, ite_false, bind_ok] using scalar_keygen_sign_verify_with_precompute false p hp family seeds sk pk m ctx rnd ss ks ps short room

end CacheopsRust.Public
