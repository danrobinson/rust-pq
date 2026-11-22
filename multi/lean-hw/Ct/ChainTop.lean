import Ct.Hw.Chain

/-!
# Constant time: `hash::chain_blocks`, as built with `hw-sha2`

`chain_blocks::<N>` first calls the hardware kernel `sha256::hw::chain_blocks::<N>`
(`Ct/Hw/Chain.lean`), which tests `N ∈ {16, 24, 32}`, `available()` and the lengths of the step
ranges and, if all are fine, runs `chain_all::<N>`; if it returns `false` the portable loops
run. The statement is the portable build's (`../lean/Ct/ChainTop.lean`), word for word: the two
runs' blocks must have the same heads (the first 16 bytes, for every `N`), which is what the
kernel's first-round cache compares. Adapted from the main tree's `../../lean-hw/Ct/ChainTop.lean`
(the hash length `N` is new).
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Hash

open slhdsa_leak

/-- `chain_blocks`: the state and the blocks are secret, except for the blocks' heads (the
first 16 bytes of their addresses), which must agree and are again equal afterwards; the hash
length `N` and the chain bounds are public. -/
@[ct_rel] theorem chain_blocks (N : Usize) (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (start e : Slice U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks N state blocks start e) (hash.chain_blocks N state' blocks' start e)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks
  ct_steps
  all_goals assumption

end Ct.Hash
