import Shakebatch.WidthThreeRoundTrip
import Cachepath.NativeShakeWots.SignEntry
import Cachepath.NativeVerify.ActiveHashes
import Cachepath.NativeVerify.ForsFused
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthThree
open ShakeBatch NativeVerify
noncomputable section
local instance : Machine := Kldisp.machine
local instance : KeyCorrect linuxWots := linuxKey

/-- The actual Linux Arm WOTS and fused FORS procedures and their correctness laws. -/
def linuxSigning : SigningPrimitives where
  wots := ⟨linuxWots,⟨fun p hp m sk seed a domain =>
    @NativeShakeWots.sign_spec Kldisp.machine linuxDispatch _ p hp m sk seed a domain (by decide) NativeVerify.linux⟩⟩
  fors := ActiveHash.linuxWithLeaf (ForsFused.fused _) (ForsFused.leaf_correct _ NativeVerify.linux)

/-- The remaining parallel boundary describes the worker's published bytes.
The caller's serial continuation uses the same certified native procedures. -/
structure PublishedWorker where
  worker : ParallelCaller.Worker ParallelCaller.ShakeSeed
  published {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) :
    ParallelCaller.WorkerCorrect worker (N:=N) p (Shake.params p) (fun s => bytes s.val) (fun _ => True)

def linuxParallel (w : PublishedWorker) : ParallelPrimitives := ⟨linuxSigning,w.worker,@w.published⟩

/-- Generate, sign and verify a contextual message through Linux Arm production calls. -/
theorem linux_serial_roundtrip {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    generateSignVerify (WidthThreeLinuxSDK.WidthThreeSDK.ShakeoptSeg.shake.slh.slh_sign linuxSigning p) p
      secret prf publicSeed sk pk msg ctx rnd = ok true :=
  serial_roundtrip linuxSigning p hp secret prf publicSeed sk pk msg ctx rnd ks ps hc

theorem linux_worker_roundtrip (w : PublishedWorker) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    generateSignVerify (WidthThreeParallel.ShakeoptSeg.shake.slh.slh_sign (linuxParallel w) p) p
      secret prf publicSeed sk pk msg ctx rnd = ok true :=
  serial_keygen_parallel_sign_roundtrip (linuxParallel w) p hp secret prf publicSeed sk pk msg ctx rnd ks ps hc

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let install (source root : Name) : MetaM Unit := do
    let value := mkApp (mkConst source) (mkConst `slhdsa.WidthThree.linuxSigning)
    let type ← inferType value
    addDecl <| .thmDecl {«name» := root, levelParams := [], type, value}
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`slh_sign_internal,`sign,`sign_deterministic,`slh_sign] do
      let dest := `slhdsa.WidthThree.LinuxSerial ++ suite ++ op
      let source := if op == `slh_sign_internal then
        `WidthThreeLinuxSDK.WidthThreeSDK.slhdsa ++ suite ++ `slh_sign_internal_spec
        else `slhdsa.WidthThree.AllLengths ++ suite ++ op
      install source dest
      let claim := if op == `slh_sign_internal then `WidthThreeParallel.slhdsa ++ suite ++ `slh_sign_internal_spec
        else `slhdsa.WidthThree.ParallelAllLengths ++ suite ++ op
      withLocalDeclD `worker (mkConst `slhdsa.WidthThree.PublishedWorker) fun worker => do
        let w := mkApp (mkConst `slhdsa.WidthThree.linuxParallel) worker
        let value ← mkLambdaFVars #[worker] (mkApp (mkConst claim) w)
        let type ← inferType value
        addDecl <| .thmDecl {«name» := `slhdsa.WidthThree.LinuxWorker ++ suite ++ op, levelParams := [], type, value}
  for api in PlatformProof.shakeFacadeRoots do
    unless api.toString.startsWith "slh_dsa.multipart_" do
      install (`WidthThreeLinuxCompat.WidthThreeCompat ++ api) (`WidthThreeSignedFacade ++ api)

end
end slhdsa.WidthThree
