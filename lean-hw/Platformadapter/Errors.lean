import Facade.Sign
open Aeneas Aeneas.Std Result
open slh_dsa

namespace slh_dsa.Kat

theorem original_bad_rand (N : Usize) (p : _root_.slhdsa.params.Params) (m ctx sk rnd sig : Slice U8)
    (hc : ctx.length≤255) (wrong : rnd.length≠N.val) :
    _root_.slhdsa.adapter.sign_into N p m ctx sk true rnd sig=fail .assertionFailure := by
  have short : ¬ctx.len>255#usize := by scalar_tac
  simp [_root_.slhdsa.adapter.sign_into,short,_root_.slhdsa.adapter_randomizer_panic N sk rnd wrong]

def ContextErrors {P Sk Vk Sig} (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig))
    (n : Nat) : Prop :=
  ∀ (sk : signing_key.SigningKey P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig)) (m ctx : Slice U8),
    (∀ r, ctx.length>255 → signing_key.SigningKey.try_sign_with_context C sk m ctx r=ok (.Err ())) ∧
    (∀ r : Slice U8, ctx.length≤255 → r.length≠n →
      signing_key.SigningKey.try_sign_with_context C sk m ctx (some r)=fail .assertionFailure)

theorem context_errors {P N Sk Vk Sig}
    (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig)) (p : _root_.slhdsa.params.Params)
    (skBuf : C.SigningKeyStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Sk)
    (sigBuf : C.SignatureStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Sig)
    (dispatch : ∀ m ctx sk r dest, C.sign m ctx sk r dest=
      _root_.slhdsa.adapter.sign_into N p m ctx sk r.isSome (r.getD (Std.Array.empty U8).to_slice) dest) :
    ContextErrors C N.val := by
  intro key m ctx
  let parts := (Array.make 1#usize [m]).to_slice
  have fit : (parts.val.flatMap (·.val)).length≤Usize.max := by simpa [parts,Array.make] using m.property
  obtain ⟨joined,join,_⟩ := _root_.slhdsa.spec_imp_exists (multipart.join_spec parts fit)
  constructor
  all_goals intro r hc
  all_goals unfold signing_key.SigningKey.try_sign_with_context signing_key.SigningKey.raw_try_sign_with_context
  all_goals simp only [lift,bind_ok,skBuf,sigBuf,ArrayU8N.Insts.Slh_dsaParamsBuffer.zeroed,
    ArrayU8N.Insts.Slh_dsaParamsBuffer.as_slice,ArrayU8N.Insts.Slh_dsaParamsBuffer.as_mut_slice,
    Array.to_slice_mut,uncurry]
  all_goals rw [join]
  all_goals simp only [bind_ok,dispatch]
  · rw [_root_.slhdsa.adapter_sign_into_long_ctx _ _ _ _ _ _ _ _ hc]
    simp [signature.error.Error.new]
  · intro bad
    simp [original_bad_rand N p _ _ _ r _ hc bad]
end slh_dsa.Kat
