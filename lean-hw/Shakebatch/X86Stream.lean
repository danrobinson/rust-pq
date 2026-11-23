import Kxouter.Top
import Shakeabs.Api
import Shakebatch.ScalarStream
import Shakebatch.ForsDispatch
import Shakebatch.WotsDispatch
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.X86
abbrev view (s : KxouterRust.shake256.Sponge) := (Keccak.words s.lanes,s.pos.val)

theorem new_spec : KxouterRust.shake256.Sponge.new ⦃ s => view s = Spec.Keccak.initial ∧ s.pos.val < 136 ⦄ := by
  simp [KxouterRust.shake256.Sponge.new,view,Keccak.words,Spec.Keccak.initial,Array.repeat_val]
  rfl

theorem absorb_spec (s : KxouterRust.shake256.Sponge) (data : Slice U8) (rate : s.pos.val < 136) :
    KxouterRust.shake256.Sponge.absorb s data ⦃ out => view out=(bytes data.val).foldl Spec.Keccak.feed (view s) ∧
      out.pos.val < 136 ⦄ := by
  apply WP.spec_mono (PlatformShake.X86.absorb s data rate)
  exact fun _ h => h.symm

theorem finish_spec (s : KxouterRust.shake256.Sponge) (out : Slice U8) (rate : s.pos.val < 136) :
    KxouterRust.shake256.Sponge.finish s out ⦃ r => bytes r.val =
      Spec.Keccak.squeeze (Spec.Keccak.finalize (view s)) 0 out.length ⦄ := by
  rw [PlatformShake.X86.finishEq]
  exact PlatformShake.finish_spec (PlatformShake.X86.portable s) out rate

end slhdsa.ShakeBatch.X86

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `ShakeForestX86 [
    (`slhdsa.shake256.Sponge, `KxouterRust.shake256.Sponge),
    (`slhdsa.shake256.Sponge.pos, `KxouterRust.shake256.Sponge.pos),
    (`slhdsa.shake256.Sponge.lanes, `KxouterRust.shake256.Sponge.lanes),
    (`slhdsa.shake256.Sponge.new, `KxouterRust.shake256.Sponge.new),
    (`slhdsa.shake256.Sponge.absorb, `KxouterRust.shake256.Sponge.absorb),
    (`slhdsa.shake256.Sponge.finish, `KxouterRust.shake256.Sponge.finish),
    (`slhdsa.Keccak.view, `slhdsa.ShakeBatch.X86.view),
    (`slhdsa.Keccak.new_spec, `slhdsa.ShakeBatch.X86.new_spec),
    (`slhdsa.Keccak.absorb_spec, `slhdsa.ShakeBatch.X86.absorb_spec),
    (`slhdsa.Keccak.finish_spec, `slhdsa.ShakeBatch.X86.finish_spec)]
    #[`slhdsa.ShakeBatch.scalarStreamCorrect,`slhdsa.ShakeBatch.sign_dispatched,`slhdsa.ShakeBatch.recover_dispatched,
      `slhdsa.ShakeBatch.wots_pk_gen_spec,`slhdsa.ShakeBatch.wots_sign_spec,`slhdsa.ShakeBatch.wots_pk_from_sig_spec]
