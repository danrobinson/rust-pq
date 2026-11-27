import Kappleouter.Top
import Shakebatch.AppleStream
import Armplatform.Replay
open Aeneas Aeneas.Std Result
namespace CacheopsRust.NativeAppleSingle
open KapplebulkRust

/-- Apple Arm sequential permutation with SHA3 and duplicated vector lanes. The two loops
and lane initialization are shared verbatim with the extracted bulk absorber. -/
def sha3Single (state : Array U64 25#usize) : Result (Array U64 25#usize) := do
  let a ← core.array.Array.map shake256.parallel.sha3.blocks.closure.Insts.CoreOpsFunctionFnMutTupleU64uint64x2_t state ()
  let iter ← SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter shake256.RC
  let a1 ← shake256.parallel.sha3.blocks_loop0_loop0 iter a
  shake256.parallel.sha3.blocks_loop1 { start := 0#usize, «end» := 25#usize } state a1

def single (state : Array U64 25#usize) : Result (Array U64 25#usize) := do
  let b ← sha512.hw.arm.available
  massert b
  sha3Single state

theorem single_fips (s : Array U64 25#usize) :
    single s ⦃ out => slhdsa.Keccak.words out = Spec.Keccak.permute (slhdsa.Keccak.words s) ⦄ := by
  unfold single sha3Single
  simp only [sha512.hw.arm.available,massert,ite_true,bind_ok]
  step with slhdsa.Kapplebulk.duplicate s as ⟨a,dup⟩
  simp only [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  have inner : shake256.parallel.sha3.blocks_loop0_loop0 ⟨Slice.from shake256.RC.val (by scalar_tac),0⟩ a ⦃ r =>
      slhdsa.Ksha3.lane r 0 = Spec.Keccak.permute (slhdsa.Ksha3.lane a 0) ⦄ := by
    have constants : shake256.RC.val.map (·.bv) = Spec.Keccak.rc.toList := by unfold shake256.RC Spec.Keccak.rc; rfl
    apply WP.spec_mono (slhdsa.Kappleperm.rounds a (Slice.from shake256.RC.val (by scalar_tac)))
    intro r h
    specialize h 0
    simp only [Slice.from_val,constants] at h
    rw [h]
    rfl
  step with inner as ⟨r,rounds⟩
  step with slhdsa.Kapplebulk.first s r as ⟨out,read⟩
  rw [read,rounds,dup]

end CacheopsRust.NativeAppleSingle

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `AppleSingleStream [
    (`KappleoneRust.shake256.parallel.single, `CacheopsRust.NativeAppleSingle.single),
    (`slhdsa.Kappleone.single_fips, `CacheopsRust.NativeAppleSingle.single_fips)]
    #[`ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect, `slhdsa.ShakeBatch.Apple.new_spec,
      `slhdsa.ShakeBatch.Apple.absorb_spec, `slhdsa.ShakeBatch.Apple.finish_spec]
    [`Kappleouter]
