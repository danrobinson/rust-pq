import Platformadapter.Kat
import Platformadapter.Errors
open Aeneas Aeneas.Std Result
open slhdsa (Room msgSlack bytes paramsS PN)
open slh_dsa
namespace slh_dsa.Kat

theorem shake_kat_algorithms {P N Sk Vk Sig}
    (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig))
    (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sklen : Sk.val=4*N.val) (vklen : Vk.val=2*N.val) (siglen : Sig.val=(paramsS p).sigBytes)
    (skBuf : C.SigningKeyStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Sk)
    (vkBuf : C.VerifyingKeyStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Vk)
    (sigBuf : C.SignatureStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Sig)
    (kg : C.keygen_seeds=_root_.slhdsa.shake.adapter.keygen_seeds N p)
    (sg : ∀ m sk r dest, C.sign_internal m sk r dest=
      _root_.slhdsa.shake.adapter.sign_internal_into N p m sk r.isSome (r.getD (Std.Array.empty U8).to_slice) dest)
    (vf : C.verify_internal=_root_.slhdsa.shake.slh.slh_verify_internal N p) :
    Algorithms C (_root_.slhdsa.Shake.params p) := by
  have hn : (_root_.slhdsa.Shake.params p).n = N.val := hp.n
  have hv : (_root_.slhdsa.Shake.params p).Valid := _root_.slhdsa.Suite.valid .shake hp
  have hs : Sig.val = (_root_.slhdsa.Shake.params p).sigBytes := siglen
  refine ⟨?_,?_,?_⟩
  · intro a b c ha hb hc
    exact slh_dsa.seeded_spec .shake C p hp sklen vklen skBuf vkBuf kg a b c (hp.n ▸ ha) (hp.n ▸ hb) (hp.n ▸ hc)
  · intro sk parts rnd valid room
    unfold signing_key.SigningKey.slh_sign_internal
    rw [skBuf,sigBuf]
    have fits := room.1
    obtain ⟨m,join,mval⟩ := _root_.slhdsa.spec_imp_exists (multipart.join_spec parts (by omega))
    rw [join]
    simp only [ArrayU8N.Insts.Slh_dsaParamsBuffer.zeroed,ArrayU8N.Insts.Slh_dsaParamsBuffer.as_slice,
      ArrayU8N.Insts.Slh_dsaParamsBuffer.as_mut_slice,Array.to_slice_mut,bind_ok,uncurry,sg]
    let rndBytes := rnd.getD (Std.Array.empty U8).to_slice
    have validRnd : rnd.isSome = true → rndBytes.length=N.val := by
      cases rnd with
      | none => simp
      | some r => intro _; exact (valid r (by simp)).trans hp.n
    obtain ⟨out,eq,data⟩ := _root_.slhdsa.spec_imp_exists (_root_.slhdsa.Shake.adapter_sign_internal_into_spec p hp m.deref
      sk.bytes.to_slice rnd.isSome rndBytes (Array.repeat Sig 0#u8).to_slice
      (by simpa [Slice.length] using sklen) (by simpa [Slice.length] using siglen) validRnd
      (by simpa only [Slice.length,_root_.slhdsa.vec_deref_val,mval,hn] using room))
    rw [eq]
    simp only [_root_.slhdsa.vec_deref_val,Array.val_to_slice,mval] at data
    have sized := congrArg List.length data
    rw [_root_.slhdsa.bytes_length,Spec.slhSignInternal_length _ hv,←hs] at sized
    simp only [bind_ok,WP.spec_ok,Array.from_slice_val _ _ sized,data]
    cases rnd <;> simp [rndBytes,_root_.slhdsa.randS, Spec.block, _root_.slhdsa.Shake.params]
  · intro pk parts sig room
    unfold verifying_key.VerifyingKey.slh_verify_internal
    have fits := room.1
    obtain ⟨m,join,mval⟩ := _root_.slhdsa.spec_imp_exists (multipart.join_spec parts (by omega))
    rw [join,vkBuf,sigBuf]
    simp only [ArrayU8N.Insts.Slh_dsaParamsBuffer.as_slice,bind_ok,vf]
    obtain ⟨b,eq,correct⟩ := _root_.slhdsa.spec_imp_exists (_root_.slhdsa.Shake.slh_verify_internal_spec p hp m.deref
      sig.bytes.to_slice pk.bytes.to_slice (by simpa [Slice.length] using vklen)
      (by simpa only [Slice.length,_root_.slhdsa.vec_deref_val,mval,hn] using room))
    simp only [_root_.slhdsa.vec_deref_val,Array.val_to_slice,mval] at correct
    rw [eq,←correct]
    cases b <;> simp [core.bool.Bool.then_some, signature.error.Error.new,Std.core.option.Option.ok_or]
theorem shake_bad_rand (N : Usize) (p : _root_.slhdsa.params.Params) (m ctx sk rnd sig : Slice U8)
    (hc : ctx.length≤255) (wrong : rnd.length≠N.val) :
    _root_.slhdsa.shake.adapter.sign_into N p m ctx sk true rnd sig=fail .assertionFailure := by
  have short : ¬ctx.len>255#usize := by scalar_tac
  simp [_root_.slhdsa.shake.adapter.sign_into,short,show _root_.slhdsa.shake.adapter.randomizer = _root_.slhdsa.adapter.randomizer from rfl,_root_.slhdsa.adapter_randomizer_panic N sk rnd wrong]

theorem shake_context_errors {P N Sk Vk Sig}
    (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig)) (p : _root_.slhdsa.params.Params)
    (skBuf : C.SigningKeyStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Sk)
    (sigBuf : C.SignatureStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Sig)
    (dispatch : ∀ m ctx sk r dest, C.sign m ctx sk r dest=
      _root_.slhdsa.shake.adapter.sign_into N p m ctx sk r.isSome (r.getD (Std.Array.empty U8).to_slice) dest) :
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
  · rw [_root_.slhdsa.Shake.adapter_sign_into_long_ctx _ _ _ _ _ _ _ _ hc]
    simp [signature.error.Error.new]
  · intro bad
    simp [shake_bad_rand N p _ _ _ r _ hc bad]
local macro "set_checks " alg:ident err:ident coreId:ident pn:ident param:ident spec:ident pEq:ident n:term:max : command => do
  let shape := Lean.mkIdent (pEq.getId.getPrefix ++ `shape)
  let kg := Lean.mkIdent (coreId.getId ++ `keygen_seeds)
  let sign := Lean.mkIdent (coreId.getId ++ `sign_internal)
  let verify := Lean.mkIdent (coreId.getId ++ `verify_internal)
  let context := Lean.mkIdent (coreId.getId ++ `sign)
  `(section
    theorem $alg : Algorithms $coreId $spec := by
      rw [←$pEq:term]
      apply shake_kat_algorithms _ _ $pn (by decide) (by decide) (by rw [$shape:term]; decide) rfl rfl rfl
      · funext a b c sk pk
        change $kg:ident a b c sk pk = _
        unfold $kg:ident
        simp only [$param:term,bind_ok,scrub_returns]
        exact Std.bind_pure _
      · intro m sk r dest
        change $sign:ident m sk r dest = _
        unfold $sign:ident
        cases r <;> simp only [params.split,$param:term,lift,bind_ok,uncurry,scrub_returns,
          Option.isSome, Option.getD]
        all_goals exact Std.bind_pure _
      · funext m sig pk
        change $verify:ident m sig pk = _
        unfold $verify:ident
        simp [$param:term]
    theorem $err : ContextErrors $coreId (UScalar.val $n) := by
      apply shake_context_errors (N:=$n) $coreId _ rfl rfl
      intro m ctx sk r dest
      change $context:ident m ctx sk r dest = _
      unfold $context:ident
      cases r <;> simp only [params.split,$param:term,lift,bind_ok,uncurry,scrub_returns,
        Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _
    end)

set_checks shake_128s_algorithms shake_128s_errors params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
  _root_.slhdsa.shake_128s.pn slh_dsa.slhdsa.sets.shake_128s.params.PARAMS
  Spec.shake_128s _root_.slhdsa.shake_128s.hP 16#usize

set_checks shake_128f_algorithms shake_128f_errors params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
  _root_.slhdsa.shake_128f.pn slh_dsa.slhdsa.sets.shake_128f.params.PARAMS
  Spec.shake_128f _root_.slhdsa.shake_128f.hP 16#usize

set_checks shake_192s_algorithms shake_192s_errors params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
  _root_.slhdsa.shake_192s.pn slh_dsa.slhdsa.sets.shake_192s.params.PARAMS
  Spec.shake_192s _root_.slhdsa.shake_192s.hP 24#usize

set_checks shake_192f_algorithms shake_192f_errors params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
  _root_.slhdsa.shake_192f.pn slh_dsa.slhdsa.sets.shake_192f.params.PARAMS
  Spec.shake_192f _root_.slhdsa.shake_192f.hP 24#usize

set_checks shake_256s_algorithms shake_256s_errors params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
  _root_.slhdsa.shake_256s.pn slh_dsa.slhdsa.sets.shake_256s.params.PARAMS
  Spec.shake_256s _root_.slhdsa.shake_256s.hP 32#usize

set_checks shake_256f_algorithms shake_256f_errors params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
  _root_.slhdsa.shake_256f.pn slh_dsa.slhdsa.sets.shake_256f.params.PARAMS
  Spec.shake_256f _root_.slhdsa.shake_256f.hP 32#usize
end slh_dsa.Kat
