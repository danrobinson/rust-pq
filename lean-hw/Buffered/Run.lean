import Buffered.Indices
import Buffered.Leaves
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [kernel : Kernel]

abbrev Buffers (N : Usize) := Array (Row16 N) 17#usize

def runBlocks {N : Usize} (sk seed : Array U8 N) (a tree : address.Adrs)
    (z : Usize) (blocks first : U32) (buf : Buffers N) (len : Array Usize 17#usize)
    (next : Array U32 17#usize) (addresses : Array address.Adrs 8#usize) (left right : Rows8 N) := do
  let (buf',len',next',addresses',left',right') ← subtree_loop2 ⟨0#u32,blocks⟩ sk seed a tree z
    buf len next first addresses left right
  subtree_loop3 ⟨0#usize,z⟩ seed tree buf' len' next' addresses' left' right'

def ProcessAt {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (idx height : U32) : Prop :=
  ∀ (tree : address.Adrs) (z : Usize) (blocks first : U32) (buf : Buffers N) (len : Array Usize 17#usize)
    (next : Array U32 17#usize) (addresses : Array address.Adrs 8#usize) (left right : Rows8 N),
    adrsS tree=(adrsS a).setTypeAndClear Spec.TREE → z.val=height.val →
    blocks.val=2^(height.val-3) → first.val=idx.val*2^height.val →
    (∀ j≤z.val, len.val[j]!.val=0) →
    (∀ j≤z.val, next.val[j]!.val=idx.val*2^(z.val-j)) →
    runBlocks sk seed a tree z blocks first buf len next addresses left right ⦃ out =>
      bytes out.val[z.val]!.val[0]!.val=Spec.xmssNode (Shake.params p) (bytes sk.val) idx.val height.val (bytes seed.val) (adrsS a) ⦄

end slhdsa.Buffered
