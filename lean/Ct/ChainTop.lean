import Ct.Hash

/-!
# Constant time: `hash::chain_blocks`, portable build

The portable loops (`Ct.Hash.chain_blocks_portable`). The statement is the same in the
`hw-sha2` build (`../lean-hw/Ct/ChainTop.lean`), whose hardware kernel is what needs the
precondition: the two runs' blocks have the same heads (`Ct/Heads.lean`). As in the single-set tree
(git `26aa3d8`, `lean/Ct/ChainTop.lean`), this is the one build-specific file of the `hash.rs` layer.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Hash

open slhdsa_leak

/-- `chain_blocks` (the portable kernel in this build): the state and the blocks are secret,
except for the blocks' heads (the first 16 bytes of their addresses), which must agree and are
again equal afterwards; the chain bounds are public. -/
@[ct_rel] theorem chain_blocks (N : Usize) (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (start e : Slice U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks N state blocks start e) (hash.chain_blocks N state' blocks' start e)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks
  exact chain_blocks_portable N state state' blocks blocks' start e h

end Ct.Hash
