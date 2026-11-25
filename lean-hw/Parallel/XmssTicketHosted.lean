import Parallel.XmssTicket
import Shakebatch.WidthEightHostedKeys
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelXmssTicket
open WidthEight

noncomputable def hostedNode {N : Usize} (host : Platform) (p : params.Params) : Node N :=
  match host with
  | .apple sha3 => (WidthEightAppleKeys.slhdsa.WidthEight.sourceEngine (.apple sha3) p).node
  | .x86 => (WidthEightX86Keys.slhdsa.WidthEight.sourceEngine .x86 p).node

theorem hosted_law {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N) :
    NodeLaw p (hostedNode (N:=N) host p) 512 := by
  intro sk i z seed a room
  cases host with
  | apple sha3 => exact WidthEightAppleKeys.slhdsa.WidthEight.apple_worker_node sha3 p hp sk i z seed a room
  | x86 => exact WidthEightX86Keys.slhdsa.WidthEight.x86_worker_node p hp sk i z seed a room

abbrev hosted_subtree {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N) :=
  @subtree_spec N p _ _ (hosted_law host p hp)

abbrev hosted_leaf {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N) :=
  @leaf_spec N p _ _ (hosted_law host p hp)

end slhdsa.ParallelXmssTicket
