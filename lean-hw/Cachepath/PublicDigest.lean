import Cachepath.PublicProgram

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.Public
set_option maxRecDepth 8192

/-- Both outputs of the pure-mode digest operation, including the output length. -/
def DigestOk {N : Usize} (P : Spec.Params) (key seed root rnd : Array U8 N)
    (ctx msg : Slice U8) (rd : Array U8 N × alloc.vec.Vec U8) : Prop :=
  let framed := Spec.withContext (bytes msg.val) (bytes ctx.val)
  bytes rd.1.val = Spec.PRFmsg P (bytes key.val) (bytes rnd.val) framed ∧
  bytes rd.2.val = Spec.Hmsg P (bytes rd.1.val) (bytes seed.val) (bytes root.val) framed ∧
  rd.2.length = P.m

theorem shake_digest_spec {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (key seed root rnd : Array U8 N) (ctx msg : Slice U8) (hc : ctx.length ≤ 255) :
    cache.shake_ops.pure_digest p key seed root rnd ctx msg ⦃ rd =>
      DigestOk (Shake.params (toSlhParams p)) key seed root rnd ctx msg rd ⦄ := by
  have heq : cache.shake_ops.pure_digest p key seed root rnd ctx msg =
      (do let r ← ShakeoptSeg.shake.hash.prf_msg_ctx key rnd ctx msg
          let d ← ShakeoptSeg.shake.hash.h_msg_ctx (toSlhParams p) r seed root ctx msg
          ok (r,d)) := by
    simp only [cache.shake_ops.pure_digest, ShakeoptSeg.shake.hash.prf_msg_ctx,
      ShakeoptSeg.shake.hash.h_msg_ctx, ShakeoptSeg.shake.hash.digest,
      CacheopsRust.cache.shake_ops.digest, lift, bind_tc_eq, Std.bind_assoc, bind_ok,
      ShakeoptSeg.shake256.Sponge.new, CacheopsRust.shake256.Sponge.new,
      slhdsa.shake256.Sponge.new, alloc.vec.Vec.deref_mut, Array.to_slice_mut, Prod.mk.injEq, Prod.casesOn, uncurry]
  rw [heq]
  let* ⟨r,hr⟩ ← Shakeopt.Segmented.prf_msg_ctx_params _ hp key rnd ctx msg hc
  let* ⟨d,hd,hl⟩ ← Shakeopt.Segmented.h_msg_ctx_params (toSlhParams p) r seed root ctx msg hc
  exact ⟨hr,hd,hl⟩

theorem sha2_digest_spec {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (key seed root rnd : Array U8 N) (ctx msg : Slice U8) (hc : ctx.length ≤ 255)
    (room : Room msg.length (msgSlack N.val + 257)) :
    cache.sha2_ops.pure_digest p key seed root rnd ctx msg ⦃ rd =>
      DigestOk (paramsS (toSlhParams p)) key seed root rnd ctx msg rd ⦄ := by
  have mr : Room (2 + ctx.length + msg.length) (msgSlack N.val) := by
    obtain ⟨a,b⟩ := room
    constructor <;> omega
  unfold cache.sha2_ops.pure_digest
  dsimp only
  split
  · have frame : cache.with_pure_context msg ctx = slhdsa.slh.with_context msg ctx := by
      unfold cache.with_pure_context slhdsa.slh.with_context
      have bound := room.1
      obtain ⟨i,e,hi⟩ := spec_imp_exists (@Usize.add_spec (2#usize) ctx.len (by scalar_tac))
      obtain ⟨j,f,hj⟩ := spec_imp_exists (@Usize.add_spec i msg.len (by scalar_tac))
      simp only [e,f,bind_tc_eq,bind_ok]
      rfl
    rw [frame]
    let* ⟨mp,hmp,hml⟩ ← with_context_spec msg ctx hc (by have := room.1; omega)
    have hmr : Room (alloc.vec.Vec.deref mp).length (msgSlack N.val) := by
      simpa [vec_deref_length, hml] using mr
    let* ⟨r,hr⟩ ← prf_msg_spec (paramsS (toSlhParams p)) hp.n hp.nok key rnd _ hmr
    let* ⟨d,hd,hl⟩ ← h_msg_spec (toSlhParams p) hp.valid hp.n_eq r seed root _ hmr
    exact ⟨by simpa [vec_deref_val,hmp] using hr, by simpa [vec_deref_val,hmp] using hd, hl⟩
  · let* ⟨r,hr⟩ ← SegmentedApi.randomizer_spec _ hp key rnd ctx msg hc room
    let* ⟨d,hd,hl⟩ ← Segmented.digest_spec _ hp.valid hp.n_eq r seed root ctx msg hc mr
    exact ⟨hr,hd,hl⟩

end CacheopsRust.Public
