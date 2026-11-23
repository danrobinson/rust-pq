import Slhdsa.Proofs.ShakeApi
import Slhdsa.Proofs.Adapter
open Aeneas Aeneas.Std Result
namespace slhdsa.Shake
theorem adapter_randomizer_shake_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sk : Slice U8) (has : Bool) (addrnd : Slice U8) (hsk : sk.length = 4 * N.val)
    (hr : has = true → addrnd.length = N.val) :
    shake.adapter.randomizer N sk has addrnd ⦃ a => bytes a.val = randS (paramsS p) (bytes sk.val) has addrnd ⦄ :=
  slhdsa.adapter_randomizer_spec p hp sk has addrnd hsk hr

@[step]
theorem adapter_sign_into_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (has : Bool) (addrnd : Slice U8) (sig : Slice U8)
    (hsk : sk.length = 4 * N.val) (hsig : sig.length = (paramsS p).sigBytes)
    (hr : has = true → addrnd.length = N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    shake.adapter.sign_into N p m ctx sk has addrnd sig ⦃ r =>
      (r.1 = true ↔ ctx.length ≤ 255) ∧
      (r.1 = true → Spec.slhSign (params p) (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (randS (paramsS p) (bytes sk.val) has addrnd) = some (bytes r.2.val)) ∧
      (r.1 = false → r.2 = sig) ⦄ := by
  unfold shake.adapter.sign_into
  simp only
  split
  · rename_i hc
    have : ¬ ctx.length ≤ 255 := by scalar_tac
    simp [this]
  · rename_i hc
    have hc' : ctx.length ≤ 255 := by scalar_tac
    have hm' := hm
    simp only [Room] at hm'
    let* ⟨ rand, rand_post ⟩ ← adapter_randomizer_shake_spec p hp sk has addrnd hsk hr
    let* ⟨ mp, mp_post, mp_len ⟩ ← with_context_spec m ctx hc' (by omega)
    have hl : (alloc.vec.Vec.deref mp).length = 2 + ctx.length + m.length := by
      simpa [alloc.vec.Vec.deref, Slice.length] using mp_len
    have hroom : Room (alloc.vec.Vec.deref mp).length (msgSlack N.val) := by
      simp only [Room] at hm ⊢; rw [hl]; omega
    let* ⟨ s, s_post, s_len ⟩ ← slh_sign_internal_spec p hp (alloc.vec.Vec.deref mp) sk rand hsk hroom
    step*
    have hnot : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
    refine ⟨by simp [hc'], fun _ => ?_, fun h => by simp at h⟩
    simp only [Spec.slhSign, hnot, ↓reduceIte, Option.some.injEq]
    rw [sig1_post, ← rand_post, ← mp_post]
    simpa [alloc.vec.Vec.deref] using s_post.symm

/-- The context test comes first: a long context is refused whatever the other
arguments, a randomizer of the wrong length included. -/
theorem adapter_sign_into_long_ctx (N : Usize) (p : _root_.slhdsa.params.Params) (m ctx sk : Slice U8)
    (has : Bool) (addrnd : Slice U8) (sig : Slice U8) (hc : 255 < ctx.length) :
    shake.adapter.sign_into N p m ctx sk has addrnd sig = ok (false, sig) := by
  unfold shake.adapter.sign_into
  have : Slice.len ctx > 255#usize := by simp [GT.gt, UScalar.lt_equiv]; scalar_tac
  simp [this]

/-- **Signing without context through the adapter**: `sig` receives the
signature of Algorithm 19 with the adapter's randomness. -/
@[step]
theorem adapter_sign_internal_into_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (m sk : Slice U8) (has : Bool) (addrnd : Slice U8) (sig : Slice U8)
    (hsk : sk.length = 4 * N.val) (hsig : sig.length = (paramsS p).sigBytes)
    (hr : has = true → addrnd.length = N.val) (hm : Room m.length (msgSlack N.val)) :
    shake.adapter.sign_internal_into N p m sk has addrnd sig ⦃ r =>
      bytes r.val = Spec.slhSignInternal (params p) (bytes m.val) (bytes sk.val)
        (randS (paramsS p) (bytes sk.val) has addrnd) ⦄ := by
  unfold shake.adapter.sign_internal_into
  let* ⟨ rand, rand_post ⟩ ← adapter_randomizer_shake_spec p hp sk has addrnd hsk hr
  let* ⟨ s, s_post, s_len ⟩ ← slh_sign_internal_spec p hp m sk rand hsk hm
  step*
  rw [r_post, ← rand_post, ← s_post]
  simp [alloc.vec.Vec.deref]

/-- **Key generation from three separate seeds**: Algorithm 18. -/
@[step]
theorem adapter_keygen_seeds_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sk_seed sk_prf pk_seed sk pk : Slice U8)
    (h1 : sk_seed.length = N.val) (h2 : sk_prf.length = N.val) (h3 : pk_seed.length = N.val)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    shake.adapter.keygen_seeds N p sk_seed sk_prf pk_seed sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (params p) (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold shake.adapter.keygen_seeds
  have := hp.le32
  step*
  · have e : ∀ (s : Slice U8) (b : Array U8 N), s.length = N.val →
        b.val = (s.val.drop (0 * N.val)).take N.val → bytes b.val = bytes s.val := by
      intro s b hs hb
      have hs' : s.val.length = N.val := hs
      rw [hb, Nat.zero_mul, List.drop_zero, List.take_of_length_le (by omega)]
    rw [r_post, e _ _ h1 a_post, e _ _ h2 b_post, e _ _ h3 c_post]

end slhdsa.Shake
