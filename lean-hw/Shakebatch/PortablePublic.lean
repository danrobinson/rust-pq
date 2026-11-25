import Shakebatch.PortableApi
import Shakeopt.Segmented

/-! Replay the public wrappers with the segmented pure-mode implementation
selected by the production platform-sha2 feature. -/
open Aeneas Aeneas.Std Result slhdsa

namespace Shakeopt.Segmented

theorem sign_with_room {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (rnd : Array U8 N) (hk : sk.length = 4 * N.val) (_ : Room m.length (msgSlack N.val + 257)) :
    ShakeoptSeg.shake.slh.slh_sign p m ctx sk rnd ⦃ r =>
      r.map (fun v => bytes v.val) = Spec.slhSign (Shake.params p) (bytes m.val) (bytes ctx.val)
        (bytes sk.val) (bytes rnd.val) ⦄ := slh_sign_spec p hp m ctx sk rnd hk

theorem verify_with_room {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (hk : pk.length = 2 * N.val) (_ : Room m.length (msgSlack N.val + 257)) :
    ShakeoptSeg.shake.slh.slh_verify N p m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (Shake.params p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ :=
  slh_verify_spec p hp m sig ctx pk hk

theorem sign_with_context {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (rnd : Array U8 N) (hk : sk.length = 4 * N.val) (_ : Shake.ContextFits m ctx) :
    ShakeoptSeg.shake.slh.slh_sign p m ctx sk rnd ⦃ r =>
      r.map (fun v => bytes v.val) = Spec.slhSign (Shake.params p) (bytes m.val) (bytes ctx.val)
        (bytes sk.val) (bytes rnd.val) ⦄ := slh_sign_spec p hp m ctx sk rnd hk

theorem verify_with_context {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (hk : pk.length = 2 * N.val) (_ : Shake.ContextFits m ctx) :
    ShakeoptSeg.shake.slh.slh_verify N p m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (Shake.params p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ :=
  slh_verify_spec p hp m sig ctx pk hk

end Shakeopt.Segmented

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `SegmentedPublic [
    (`slhdsa.shake.slh.slh_sign, `ShakeoptSeg.shake.slh.slh_sign),
    (`slhdsa.Shake.slh_sign_spec, `Shakeopt.Segmented.sign_with_room),
    (`slhdsa.Shake.sign_full, `Shakeopt.Segmented.sign_with_context),
    (`slhdsa.Shake.verify_full, `Shakeopt.Segmented.verify_with_context),
    (`slhdsa.shake.slh.slh_verify, `ShakeoptSeg.shake.slh.slh_verify),
    (`slhdsa.Shake.slh_verify_spec, `Shakeopt.Segmented.verify_with_room)]
    (PlatformProof.shakeApiRoots ++ #[`slhdsa.Shake.api_sign_spec,
      `slhdsa.Shake.api_sign_deterministic_spec, `slhdsa.Shake.api_verify_spec])
