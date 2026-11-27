import Parallel.RootTable
import Cachepath.NativeVerify.Hosted

open Lean Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dst,bindings) in [
      (`RootTableApple,← Cachepath.NativeHashReplay.appleBindings),
      (`RootTableArm,Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux),
      (`RootTableX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    PlatformProof.replay dst bindings #[`slhdsa.Shake.hash2_spec] []
    unless (← getEnv).contains (dst ++ `slhdsa.shake.xmss.hash2) do
      throwError "missing native parent hash in {dst}"

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelRootWalk
open ParallelFused ParallelXmssTicket
inductive Host where
  | apple (sha3 : Bool)
  | linuxArm
  | x86

noncomputable def recovery : Host → CacheopsRust.NativeVerifier.Recovery
  | .apple sha3 => AppleNativeRecovery.slhdsa.NativeVerify.appleRecovery sha3
  | .linuxArm => LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery
  | .x86 => X86NativeRecovery.slhdsa.NativeVerify.x86Recovery

noncomputable def hosted (h : Host) : Engine where
  hash {N} := match h with
    | .apple _ => @RootTableApple.slhdsa.shake.xmss.hash2 N
    | .linuxArm => @RootTableArm.slhdsa.shake.xmss.hash2 N
    | .x86 => @RootTableX86.slhdsa.shake.xmss.hash2 N
  recover := @(recovery h).fors

theorem hosted_table {N : Usize} (host : Host) (p : params.Params) (hp : PN p N) (d width : Usize)
    (sig : alloc.vec.Vec U8) (md : Slice U8) (seed : Array U8 N) (a : address.Adrs)
    (layers : Layers) (leaves : alloc.vec.Vec (Option (Array U8 N))) (count : Usize)
    (auth : alloc.vec.Vec (Array U8 N)) (sk : Spec.Bytes) (tree leaf : Nat)
    (shape : width.val=p.hp.val) (num : count.val+1=p.d.val) (leafBound : leaf<2^p.hp.val)
    (layout : LayerTable p.hp.val tree leaf p.d.val layers)
    (live : PublishedLeaves (Shake.params p) sk (bytes seed.val) tree leaf count.val leaves)
    (siblings : PublishedAuth (Shake.params p) sk (bytes seed.val) tree leaf count.val auth)
    (size : sig.length=p.k.val*(1+p.a.val)*N.val) (digest : md.length=(p.k.val*p.a.val+7)/8)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    @all_roots (hosted host) N p d width sig md seed a layers leaves count auth ⦃ out => Roots
      (message (Shake.params p) (Spec.forsPkFromSig (Shake.params p) (bytes sig.val) (bytes md.val)
        (bytes seed.val) (adrsS a)) sk (bytes seed.val) tree leaf) p.d.val out ⦄ := by
  apply @table_spec (hosted host) N p hp d width sig md seed a layers leaves count auth sk tree leaf shape num leafBound layout live siblings
  · cases host with
    | apple sha3 => exact RootTableApple.slhdsa.Shake.hash2_spec p hp
    | linuxArm => exact RootTableArm.slhdsa.Shake.hash2_spec p hp
    | x86 => exact RootTableX86.slhdsa.Shake.hash2_spec p hp
  · have r := (recovery host).fors_spec p hp sig.deref md seed a (by simpa using size) digest domain
    change (recovery host).fors p sig.deref md seed a ⦃ row => bytes row.val =
      Spec.forsPkFromSig (Shake.params p) (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS a) ⦄
    simp only [vec_deref_val] at r
    exact r

end slhdsa.ParallelRootWalk
