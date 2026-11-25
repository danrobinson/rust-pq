import Shakebatch.WidthThreeLinux
import Cachepath.NativeShakeWots.KeyEntry
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthThree
open ShakeBatch NativeVerify

@[instance_reducible] def linuxDispatch : NativeVerify.Wots.Dispatch Kldisp.machine :=
  ⟨fullActive Kldisp.machine KldispRust.shake256.parallel.available⟩

/-- Actual narrow-batch WOTS programs, instantiated at Linux Arm's selected kernel. -/
@[instance_reducible] noncomputable def linuxWots : Wots where
  keygen := @NativeShakeWots.keygen Kldisp.machine linuxDispatch ShakeForestLinux.slhdsa.ShakeBatch.scalarStream
  sign := @NativeShakeWots.sign Kldisp.machine linuxDispatch

theorem linuxKey : KeyCorrect linuxWots :=
  ⟨fun p hp sk seed a domain => @NativeShakeWots.keygen_spec Kldisp.machine linuxDispatch
    ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect _
    p hp sk seed a domain (by decide) NativeVerify.linux⟩

noncomputable abbrev linuxNode := @WidthThreeLinuxSDK.slhdsa.WidthThree.shake.xmss.xmss_node linuxWots
noncomputable abbrev linuxNodeSpec := @WidthThreeLinuxSDK.slhdsa.WidthThree.node_spec linuxWots linuxKey

open Lean Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let mut roots := #[`slhdsa.Shake.api_keygen_spec,`slhdsa.Shake.slh_keygen_internal_spec]
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`keygen_spec,`slh_keygen_internal_spec] do
      roots := roots.push (`slhdsa ++ setName ++ op)
    roots := roots.push (`slh_dsa ++ Name.mkSimple (setName.toString ++ "_new"))
  PlatformProof.replay `WidthThreeKeygenSDK [
    (`slhdsa.shake.xmss.xmss_node,`slhdsa.WidthThree.linuxNode),
    (`slhdsa.Shake.xmss_node_spec,`slhdsa.WidthThree.linuxNodeSpec)]
    roots

end slhdsa.WidthThree
