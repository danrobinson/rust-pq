import Parallel.WorkerPayload

open Aeneas Aeneas.Std Result
namespace slhdsa.WorkerCrypto
set_option linter.concreteInstances false

/-- The native worker specializes the inner kernels to its parameter set and
the target's detected SHAKE implementation. -/
class Config where
  host : WorkerPayload.Host
  p : params.Params

def rootHost [cfg : Config] : ParallelRootWalk.Host :=
  match cfg.host with
  | .apple f => .apple f
  | .x86 => .x86
  | .linuxArm => .linuxArm

noncomputable def xmss [cfg : Config] {N : Usize} :=
  @ParallelLeafTable.nodeFor N rootHost cfg.p

noncomputable def node [cfg : Config] {N : Usize} :=
  match cfg.host with
  | .apple f => @ScalarTicketApple.slhdsa.ParallelScalarFors.node (ParallelScalarFors.wide (.apple f) cfg.p) N
  | .x86 => @ScalarTicketX86.slhdsa.ParallelScalarFors.node (ParallelScalarFors.wide .x86 cfg.p) N
  | .linuxArm => @ScalarTicketLinux.slhdsa.ParallelScalarFors.node ParallelScalarFors.narrow N

noncomputable def secret [cfg : Config] {N : Usize} :=
  match cfg.host with
  | .apple _ => @ScalarTicketApple.slhdsa.shake.fors.fors_sk_gen N
  | .x86 => @ScalarTicketX86.slhdsa.shake.fors.fors_sk_gen N
  | .linuxArm => @ScalarTicketLinux.slhdsa.shake.fors.fors_sk_gen N

noncomputable def wots [cfg : Config] {N : Usize} :=
  match cfg.host with
  | .apple f => @WidthEightOuterApple.slhdsa.Fused.Outer.shake.wots.wots_sign ((WidthEight.Platform.apple f).outer cfg.p) N
  | .x86 => @WidthEightOuterX86.slhdsa.Fused.Outer.shake.wots.wots_sign (WidthEight.Platform.x86.outer cfg.p) N
  | .linuxArm => @WidthThree.shake.wots.wots_sign WidthThree.linuxWots N

noncomputable def hash [Config] {N : Usize} :=
  @ParallelRootWalk.Engine.hash (ParallelRootWalk.hosted rootHost) N

noncomputable def recover [Config] {N : Usize} :=
  @ParallelRootWalk.Engine.recover (ParallelRootWalk.hosted rootHost) N

theorem ticket_eq [cfg : Config] {N : Usize} (layers : ParallelXmssTicket.Layers)
    (roots : alloc.vec.Vec (Array U8 N)) (j : Usize) (sk seed : Array U8 N) :
    (do let (a,k) ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) layers j
        let msg ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) roots j
        let tag ← address.Adrs.with_type a address.WOTS_HASH
        let addr ← address.Adrs.with_keypair tag k
        wots msg sk seed addr) =
      WorkerPayload.nativeTicket cfg.host cfg.p layers roots j sk seed := by
  cases cfg with
  | mk h p => cases h <;> rfl

end slhdsa.WorkerCrypto
