import Shakeabs.Top
import Armplatform.Replay
import Slhdsa.Proofs.ShakeApi
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake
abbrev view (s : ShakeAbsRust.shake256.Sponge) := Keccak.view (asScalar s)

theorem new_spec : ShakeAbsRust.shake256.Sponge.new ⦃ s => view s = Spec.Keccak.initial ∧ s.pos.val<136 ⦄ := by
  simp [ShakeAbsRust.shake256.Sponge.new,view,asScalar,Keccak.view,Keccak.words,Spec.Keccak.initial,Array.repeat_val]
  rfl

theorem absorb_spec (s : ShakeAbsRust.shake256.Sponge) (data : Slice U8) (rate : s.pos.val<136) :
    ShakeAbsRust.shake256.Sponge.absorb s data ⦃ out => view out=(bytes data.val).foldl Spec.Keccak.feed (view s) ∧
      out.pos.val<136 ⦄ := by
  apply WP.spec_mono (absorb s data rate)
  exact fun _ h => h.symm

theorem finish_spec (s : ShakeAbsRust.shake256.Sponge) (out : Slice U8) (rate : s.pos.val<136) :
    ShakeAbsRust.shake256.Sponge.finish s out ⦃ r => bytes r.val =
      Spec.Keccak.squeeze (Spec.Keccak.finalize (view s)) 0 out.length ⦄ := by
  rw [finish_eq]
  exact Keccak.finish_spec (asScalar s) out rate
end slhdsa.PlatformShake

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `PortableShake [
  (`slhdsa.shake256.Sponge, `ShakeAbsRust.shake256.Sponge),
  (`slhdsa.shake256.Sponge.pos, `ShakeAbsRust.shake256.Sponge.pos),
  (`slhdsa.shake256.Sponge.lanes, `ShakeAbsRust.shake256.Sponge.lanes),
  (`slhdsa.shake256.Sponge.new, `ShakeAbsRust.shake256.Sponge.new),
  (`slhdsa.shake256.Sponge.absorb, `ShakeAbsRust.shake256.Sponge.absorb),
  (`slhdsa.shake256.Sponge.finish, `ShakeAbsRust.shake256.Sponge.finish),
  (`slhdsa.Keccak.view, `slhdsa.PlatformShake.view),
  (`slhdsa.Keccak.new_spec, `slhdsa.PlatformShake.new_spec),
  (`slhdsa.Keccak.absorb_spec, `slhdsa.PlatformShake.absorb_spec),
  (`slhdsa.Keccak.finish_spec, `slhdsa.PlatformShake.finish_spec)
    ]
    #[`slhdsa.Shake.api_keygen_spec,`slhdsa.Shake.api_sign_spec,`slhdsa.Shake.api_sign_deterministic_spec,
    `slhdsa.Shake.api_verify_spec,`slhdsa.Shake.slh_keygen_internal_spec,`slhdsa.Shake.slh_sign_internal_spec,
    `slhdsa.Shake.slh_verify_internal_spec]
