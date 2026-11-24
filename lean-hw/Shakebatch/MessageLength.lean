import Slhdsa.Proofs.ShakeApi
open Aeneas Aeneas.Std Result
namespace slhdsa.Shake
attribute [local step] slhdsa.extend_spec

/-- Context construction appends the two-byte header and the context only after validating it. -/
def ContextFits (m ctx : Slice U8) : Prop :=
  ctx.length ≤ 255 → 2 + ctx.length + m.length ≤ Usize.max

theorem context_fits_rust_slice (m ctx : Slice U8) (allocation : m.length ≤ Usize.max/2) :
    ContextFits m ctx := by
  intro limit
  have minimum : 1024 ≤ Usize.max := by scalar_tac
  omega

theorem with_context_exact (m ctx : Slice U8) (hc : ctx.length ≤ 255)
    (length : 2+ctx.length+m.length ≤ Usize.max) :
    shake.slh.with_context m ctx ⦃ r => bytes r.val = Spec.withContext (bytes m.val) (bytes ctx.val) ∧
      r.length = 2+ctx.length+m.length ⦄ := by
  unfold shake.slh.with_context
  step*
  · have : mp2.length = 2+ctx.length := by
      simp [alloc.vec.Vec.length,mp2_post,mp1_post,mp_post];scalar_tac
    scalar_tac
  · constructor
    · simp [r_post,mp2_post,mp1_post,mp_post,Spec.withContext,Spec.toByte,List.range,List.range.loop,i1_post]
      apply BitVec.eq_of_toNat_eq
      simp
    · simp [alloc.vec.Vec.length,r_post,mp2_post,mp1_post,mp_post];scalar_tac

theorem sign_full {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length=4*N.val) (fits : ContextFits m ctx) :
    shake.slh.slh_sign p m ctx sk addrnd ⦃ r => r.map (fun v => bytes v.val)=
      Spec.slhSign (params p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold shake.slh.slh_sign
  by_cases large : ctx.len > 255#usize
  · have len : ctx.val.length > 255 := by scalar_tac
    simp [large,Spec.slhSign,len]
  · have small : ctx.length ≤ 255 := by scalar_tac
    have allowed : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [large,ite_false]
    let* ⟨msg,hm,_⟩ ← with_context_exact m ctx small (fits small)
    let* ⟨out,signed,_⟩ ← slh_sign_internal_all_lengths p hp msg.deref sk addrnd hsk
    simp [Spec.slhSign,allowed,signed,hm]

theorem verify_full {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (hpk : pk.length=2*N.val) (fits : ContextFits m ctx) :
    shake.slh.slh_verify N p m sig ctx pk ⦃ b =>
      b=Spec.slhVerify (params p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold shake.slh.slh_verify
  by_cases large : ctx.len > 255#usize
  · have len : ctx.val.length > 255 := by scalar_tac
    simp [large,Spec.slhVerify,len]
  · have small : ctx.length ≤ 255 := by scalar_tac
    have allowed : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [large,ite_false]
    let* ⟨msg,hm,_⟩ ← with_context_exact m ctx small (fits small)
    let* ⟨out,verified⟩ ← slh_verify_internal_all_lengths p hp msg.deref sig pk hpk
    simp [Spec.slhVerify,allowed,verified,hm]

theorem deterministic_full {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (hsk : sk.length=4*N.val) (fits : ContextFits m ctx) :
    shake.api.sign_deterministic N p m ctx sk ⦃ r => r.map (fun v => bytes v.val) =
      Spec.slhSign (params p) (bytes m.val) (bytes ctx.val) (bytes sk.val)
        (Spec.block (paramsS p) (bytes sk.val) 2) ⦄ := by
  unfold shake.api.sign_deterministic
  let* ⟨pk_seed,hpk⟩ ← block_spec
  apply WP.spec_mono (sign_full p hp m ctx sk pk_seed hsk fits)
  intro r hr
  rw [hr,bytes_block_N p hp sk pk_seed 2 hpk]

end slhdsa.Shake
