import Armwide.CachedSession
import Armwide.PublicSignature
import Cachepath.Precompute

open Aeneas Aeneas.Std Result slhdsa CacheopsRust CacheopsRust.Public
open CacheopsRust.cache.generatedKeys slhdsa.cache.endtoend
namespace slhdsa.CachedArm
variable [cpu : Armwide.Public.Dispatcher.Cpu] [features : Armwide.Keygen.Features]

/-- The public native verifier accepts the actual cached signature with either
native cache constructor, including eager preparation of the layer-d−2 tree. -/
theorem seeded_roundtrip {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (workers : Option Usize) (eager : Bool) (seeds sk pk m ctx : Slice U8) (rnd : Array U8 N)
    (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val)
    (short : ctx.length≤255) (room : Room m.length (msgSlack N.val+257)) :
    (do let (c,secret,pub) ← keygen N (builders N workers).sha2 (builders N workers).shake .Sha2 p seeds sk pk
        let c ← if eager then @CacheopsRust.Public.cache.TopTreeCache.precompute_layer_d2 N (builders N workers) c p secret else ok c
        let sig ← @ArmCachedApi.CacheopsRust.Public.cache.sign_cached cpu features Closed.scalar N p m ctx secret rnd c
        match sig with
        | none => ok false
        | some sig => ArmSdk.AppleContext.slhdsa.SegmentedApi.Program.slh.slh_verify N (toSlhParams p) m sig.deref ctx pub) = ok true := by
  let P := paramsS (toSlhParams p)
  have kernel : CacheopsRust.cache.constructor.TreeKernel (builders N workers).sha2 P := by
    cases workers with
    | none => exact Armwide.XmssLeaves.Generate.tree_kernel _ hp
    | some t => exact Armwide.XmssLeaves.Generate.parallel_tree_kernel _ hp t
  obtain ⟨⟨c,secret,pub⟩,gen,g⟩ := spec_imp_exists (keygen_spec (builders N workers).sha2 (builders N workers).shake
    .Sha2 p P hp.n_eq.symm hp.n rfl rfl hp.valid (fun _ => kernel) (by intro h; cases h) seeds sk pk ss ks ps)
  have prepare : (if eager then @CacheopsRust.Public.cache.TopTreeCache.precompute_layer_d2 N (builders N workers) c p secret else ok c)
      ⦃ c' => c'.family = .Sha2 ∧ CacheValid c' P (Spec.block P (bytes secret.val) 0) (Spec.block P (bytes secret.val) 2) ⦄ := by
    cases eager
    · exact (WP.spec_ok _).mpr ⟨g.familyEq,g.valid⟩
    · apply WP.spec_mono (@precompute_spec N (builders N workers) p hp c secret g.secretLength
          (g.familyEq ▸ g.wellFormed) (g.familyEq ▸ g.valid)
          (by intro h; rw [h]; exact kernel) (by intro h; rw [g.familyEq] at h; cases h))
      rintro next ⟨valid,tag,_⟩
      have hf : c.family = .Sha2 := g.familyEq
      rw [hf] at valid
      exact ⟨tag.trans hf,valid⟩
  obtain ⟨warm,prepared,tag,valid⟩ := spec_imp_exists prepare
  obtain ⟨sig,sign,signBytes⟩ := spec_imp_exists (@ArmCachedApi.CacheopsRust.Public.sign_cached_spec cpu features Closed.scalar N _
    p hp warm m ctx secret rnd g.secretLength (fun _ => room) (tag ▸ g.wellFormed) (tag ▸ valid))
  rw [tag] at signBytes
  have size : (bytes ctx.val).length ≤ 255 := by simpa [bytes] using short
  obtain ⟨expected,produced,accept⟩ := Spec.slh_complete P hp.valid (bytes m.val) (bytes ctx.val) (bytes secret.val)
    (bytes rnd.val) size g.wellFormed
  change sig.map (fun s => bytes s.val) = Spec.slhSign P _ _ _ _ at signBytes
  rw [produced] at signBytes
  cases sig with
  | none => contradiction
  | some sig =>
    have eq : bytes sig.val = expected := Option.some.inj signBytes
    obtain ⟨result,verified,hr⟩ := spec_imp_exists (ArmSdk.AppleContext.slhdsa.SegmentedApi.verify_spec
      _ hp m sig.deref ctx pub g.publicLength room)
    rw [vec_deref_val,eq,g.publicKey,accept] at hr
    simp only [gen,bind_ok,uncurry,prepared,sign,verified,hr]

end slhdsa.CachedArm
