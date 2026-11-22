import Ct.Hash

/-!
# Constant time: `hash::chain_blocks`, as built by default

The portable loops (`Ct.Hash.chain_blocks_portable`). See `Ct/CompressTop.lean`. The statement
is the same in the `hw-sha2` build (`lean-hw/Ct/ChainTop.lean`), whose hardware kernel is what
needs the precondition: the two runs' blocks have the same heads (`Ct/Heads.lean`).
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Hash

open slhdsa_leak

/-- `chain_blocks`: the state and the blocks are secret, except for the blocks' heads (the
first 16 bytes of their addresses), which must agree and are again equal afterwards; the chain
bounds are public. -/
@[ct_rel] theorem chain_blocks (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (start e : Slice U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks state blocks start e) (hash.chain_blocks state' blocks' start e)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks
  exact chain_blocks_portable state state' blocks blocks' start e h

end Ct.Hash
