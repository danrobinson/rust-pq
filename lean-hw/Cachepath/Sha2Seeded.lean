import Cachepath.KeygenVerify

open Aeneas Aeneas.Std Result slhdsa slhdsa.cache.endtoend
namespace CacheopsRust.Public
open CacheopsRust.cache.generatedKeys

theorem sha2_seeded_roundtrip (eager : Bool) {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N) (seeds sk pk m ctx : Slice U8) (rnd : Array U8 N)
    (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val) (ps : pk.length = 2*N.val)
    (short : ctx.length ≤ 255) (room : Room m.length (msgSlack N.val+257)) :
    (do let (c,secret,pub) ← keygen N slhdsa.cache.sha2_ops.build_xmss_tree
          (@slhdsa.cache.builder.nativeShake.build_xmss_tree slhdsa.cache.builder.nativeShake.scalar N)
          .Sha2 p seeds sk pk
        let c ← if eager then (@cache.TopTreeCache.precompute_layer_d2 N
          (@extractedBuilders N slhdsa.cache.builder.nativeShake.scalar) c p secret) else ok c
        let sig ← @cache.sign_cached Closed.scalar N p m ctx secret rnd c
        match sig with
        | none => ok false
        | some signature =>
          PortableMessage.slhdsa.SegmentedApi.Program.slh.slh_verify N (toSlhParams p) m signature.deref ctx pub) = ok true :=
  scalar_keygen_sign_verify_with_precompute eager p hp .Sha2 seeds sk pk m ctx rnd ss ks ps short room

end CacheopsRust.Public
