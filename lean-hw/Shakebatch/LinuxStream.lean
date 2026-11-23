import Kspongel.Top
import Shakeabs.Api
import Shakebatch.ScalarStream
import Shakebatch.ForsDispatch
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.Linux
abbrev view (s : KspongeLRust.shake256.Sponge) := (Keccak.words s.lanes,s.pos.val)

theorem new_spec : KspongeLRust.shake256.Sponge.new ⦃ s => view s = Spec.Keccak.initial ∧ s.pos.val < 136 ⦄ := by
  simp [KspongeLRust.shake256.Sponge.new,view,Keccak.words,Spec.Keccak.initial,Array.repeat_val]
  rfl

theorem absorb_spec (s : KspongeLRust.shake256.Sponge) (data : Slice U8) (rate : s.pos.val < 136) :
    KspongeLRust.shake256.Sponge.absorb s data ⦃ out => view out=(bytes data.val).foldl Spec.Keccak.feed (view s) ∧
      out.pos.val < 136 ⦄ := by
  apply WP.spec_mono (PlatformShake.Linux.absorb s data rate)
  exact fun _ h => h.symm

theorem finish_spec (s : KspongeLRust.shake256.Sponge) (out : Slice U8) (rate : s.pos.val < 136) :
    KspongeLRust.shake256.Sponge.finish s out ⦃ r => bytes r.val =
      Spec.Keccak.squeeze (Spec.Keccak.finalize (view s)) 0 out.length ⦄ := by
  rw [PlatformShake.Linux.finishEq]
  exact PlatformShake.finish_spec (PlatformShake.Linux.portable s) out rate

end slhdsa.ShakeBatch.Linux

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `ShakeForestLinux [
    (`slhdsa.shake256.Sponge, `KspongeLRust.shake256.Sponge),
    (`slhdsa.shake256.Sponge.pos, `KspongeLRust.shake256.Sponge.pos),
    (`slhdsa.shake256.Sponge.lanes, `KspongeLRust.shake256.Sponge.lanes),
    (`slhdsa.shake256.Sponge.new, `KspongeLRust.shake256.Sponge.new),
    (`slhdsa.shake256.Sponge.absorb, `KspongeLRust.shake256.Sponge.absorb),
    (`slhdsa.shake256.Sponge.finish, `KspongeLRust.shake256.Sponge.finish),
    (`slhdsa.Keccak.view, `slhdsa.ShakeBatch.Linux.view),
    (`slhdsa.Keccak.new_spec, `slhdsa.ShakeBatch.Linux.new_spec),
    (`slhdsa.Keccak.absorb_spec, `slhdsa.ShakeBatch.Linux.absorb_spec),
    (`slhdsa.Keccak.finish_spec, `slhdsa.ShakeBatch.Linux.finish_spec)]
    #[`slhdsa.ShakeBatch.scalarStreamCorrect,`slhdsa.ShakeBatch.sign_dispatched,`slhdsa.ShakeBatch.recover_dispatched]
