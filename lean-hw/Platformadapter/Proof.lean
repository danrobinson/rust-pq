import Platformadapter.Program
import Slhdsa.Proofs.Adapter
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformAdapter

@[step]
theorem sign_into_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (has : Bool) (addrnd : Slice U8) (sig : Slice U8)
    (hsk : sk.length = 4 * N.val) (hsig : sig.length = (paramsS p).sigBytes)
    (hr : has = true → addrnd.length = N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    adapter.sign_into N p m ctx sk has addrnd sig ⦃ r =>
      (r.1 = true ↔ ctx.length ≤ 255) ∧
      (r.1 = true → Spec.slhSign (paramsS p) (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (randS (paramsS p) (bytes sk.val) has addrnd) = some (bytes r.2.val)) ∧
      (r.1 = false → r.2 = sig) ⦄ := by
  unfold adapter.sign_into
  simp only
  split
  · rename_i hc
    have : ¬ ctx.length ≤ 255 := by scalar_tac
    simp [this]
  · rename_i hc
    have hc' : ctx.length ≤ 255 := by scalar_tac
    have hm' := hm
    simp only [Room] at hm'
    let* ⟨ rand, rand_post ⟩ ← adapter_randomizer_spec p hp sk has addrnd hsk hr
    split
    · step with slh_sign_spec p hp m ctx sk rand hsk hm as ⟨out,spec⟩
      have valid : ¬ (bytes ctx.val).length > 255 := by simpa using hc'
      simp only [Spec.slhSign,valid,ite_false] at spec
      cases out with
      | none => simp at spec
      | some signature =>
        simp only [Option.map_some,Option.some.injEq] at spec
        have length := congrArg List.length spec
        rw [Spec.slhSignInternal_length _ hp.valid,bytes_length] at length
        simp only [core.option.Option.unwrap,ofOption,bind_ok]
        step as ⟨written,hw⟩
        all_goals try (simpa [vec_deref_length,hsig] using length.symm)
        refine ⟨by simp [hc'],fun _ => ?_,fun h => by simp at h⟩
        simp only [Spec.slhSign,valid,ite_false,Option.some.injEq]
        rw [hw,vec_deref_val, spec,rand_post]
    · let* ⟨ mp, mp_post, mp_len ⟩ ← with_context_spec m ctx hc' (by omega)
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
theorem sign_into_long_ctx (N : Usize) (p : params.Params) (m ctx sk : Slice U8)
    (has : Bool) (addrnd : Slice U8) (sig : Slice U8) (hc : 255 < ctx.length) :
    adapter.sign_into N p m ctx sk has addrnd sig = ok (false, sig) := by
  unfold adapter.sign_into
  have : Slice.len ctx > 255#usize := by simp [GT.gt, UScalar.lt_equiv]; scalar_tac
  simp [this]

/-- For accepted contexts, malformed hedging randomness fails before any signature write. -/
theorem sign_into_bad_randomness (N : Usize) (p : params.Params) (m ctx sk rnd sig : Slice U8)
    (hc : ctx.length≤255) (wrong : rnd.length≠N.val) :
    adapter.sign_into N p m ctx sk true rnd sig = fail .assertionFailure := by
  have short : ¬ctx.len>255#usize := by scalar_tac
  simp [adapter.sign_into,short,adapter_randomizer_panic N sk rnd wrong]

end slhdsa.PlatformAdapter
