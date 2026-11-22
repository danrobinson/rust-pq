import Ct.Hw.Chain

/-!
# Constant time: `hash::chain_blocks`, as built with `hw-sha2`

`chain_blocks` first calls the hardware kernel `sha256::hw::chain_blocks` (`Ct/Hw/Chain.lean`),
which tests `available()` and the lengths of the step ranges and, if both are fine, runs
`chain_all`; if it returns `false` the portable loops run. The statement is the one of the
default build (`lean/Ct/ChainTop.lean`): the two runs' blocks must have the same heads, which is
what the kernel's first-round cache compares.
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
  ct_steps
  all_goals assumption

end Ct.Hash
