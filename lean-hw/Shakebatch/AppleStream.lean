import Kappleouter.Top
import Shakeabs.Api
import Shakebatch.ScalarStream
import Shakebatch.ForsDispatch
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.Apple
abbrev view (s : KappleouterRust.shake256.Sponge) := (Keccak.words s.lanes,s.pos.val)

theorem new_spec : KappleouterRust.shake256.Sponge.new ⦃ s => view s = Spec.Keccak.initial ∧ s.pos.val < 136 ⦄ := by
  simp [KappleouterRust.shake256.Sponge.new,view,Keccak.words,Spec.Keccak.initial,Array.repeat_val]
  rfl

theorem absorb_spec (s : KappleouterRust.shake256.Sponge) (data : Slice U8) (rate : s.pos.val < 136) :
    KappleouterRust.shake256.Sponge.absorb s data ⦃ out => view out=(bytes data.val).foldl Spec.Keccak.feed (view s) ∧
      out.pos.val < 136 ⦄ := by
  apply WP.spec_mono (PlatformShake.Apple.absorb s data rate)
  exact fun _ h => h.symm

theorem finish_spec (s : KappleouterRust.shake256.Sponge) (out : Slice U8) (rate : s.pos.val < 136) :
    KappleouterRust.shake256.Sponge.finish s out ⦃ r => bytes r.val =
      Spec.Keccak.squeeze (Spec.Keccak.finalize (view s)) 0 out.length ⦄ := by
  rw [PlatformShake.Apple.finishEq]
  exact PlatformShake.finish_spec (PlatformShake.Apple.portable s) out rate

end slhdsa.ShakeBatch.Apple

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `ShakeForestApple [
    (`slhdsa.shake256.Sponge, `KappleouterRust.shake256.Sponge),
    (`slhdsa.shake256.Sponge.pos, `KappleouterRust.shake256.Sponge.pos),
    (`slhdsa.shake256.Sponge.lanes, `KappleouterRust.shake256.Sponge.lanes),
    (`slhdsa.shake256.Sponge.new, `KappleouterRust.shake256.Sponge.new),
    (`slhdsa.shake256.Sponge.absorb, `KappleouterRust.shake256.Sponge.absorb),
    (`slhdsa.shake256.Sponge.finish, `KappleouterRust.shake256.Sponge.finish),
    (`slhdsa.Keccak.view, `slhdsa.ShakeBatch.Apple.view),
    (`slhdsa.Keccak.new_spec, `slhdsa.ShakeBatch.Apple.new_spec),
    (`slhdsa.Keccak.absorb_spec, `slhdsa.ShakeBatch.Apple.absorb_spec),
    (`slhdsa.Keccak.finish_spec, `slhdsa.ShakeBatch.Apple.finish_spec)]
    #[`slhdsa.ShakeBatch.scalarStreamCorrect,`slhdsa.ShakeBatch.sign_dispatched,`slhdsa.ShakeBatch.recover_dispatched]
