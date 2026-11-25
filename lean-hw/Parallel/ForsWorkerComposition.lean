import Parallel.ForsWorkerDriver
import Parallel.ForsNativeField
import Parallel.RawWorker
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelRawWorker
open WidthEight.Ticket ParallelRootWalk

noncomputable def inputsFrom (source : RawFors.ActionSource) (host : Host) (schedule : ∀ n, Schedule n) : ForestWorker :=
  assemble host (fun p md sk seed a => RawFors.run source host p md sk seed a schedule) schedule

theorem inputs_from_source (source : RawFors.ActionSource) (correct : RawFors.SourceCorrect source)
    (host : Host) (schedule : ∀ n, Schedule n) {N : Usize} (p : params.Params) (hp : PN p N) :
    ForestLaw (inputsFrom source host schedule) N p :=
  assemble_law host _ schedule p hp (fun md sk seed a len domain =>
    RawFors.run_spec source correct host p hp md sk seed a schedule len domain)

noncomputable def native (host : Host) (schedule : ∀ n, Schedule n) : ForestWorker :=
  inputsFrom (@RawFors.nativeAction) host schedule

theorem native_law (host : Host) (schedule : ∀ n, Schedule n) {N : Usize} (p : params.Params) (hp : PN p N) :
    ForestLaw (native host schedule) N p :=
  inputs_from_source (@RawFors.nativeAction) (fun mode d valid => RawFors.native_receipt mode d valid)
    host schedule p hp

end slhdsa.ParallelRawWorker
