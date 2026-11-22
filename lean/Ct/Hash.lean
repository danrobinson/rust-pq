import Ct.Sha256

/-!
# Constant time: the `hash.rs` layer (started)

Only the first few functions, as a check that the SHA-256 lemmas and `ct_steps` compose at the
next layer. The rest of `hash.rs` (`chain_blocks`, `thash`, `thash_values`, `prf_msg`, `h_msg`,
…) is not done here.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Hash

open slhdsa_leak

@[ct_rel] theorem trunc (st st' : Array U32 8#usize) :
    Rel (hash.trunc st) (hash.trunc st') (fun _ _ => True) := by
  unfold hash.trunc
  ct_steps

/-- The address is public; the message is secret (only its length matters). -/
@[ct_rel] theorem short_block (adrs : slhdsa.address.Adrs) (m m' : Slice U8)
    (h : m.length = m'.length) :
    Rel (hash.short_block adrs m) (hash.short_block adrs m') (fun _ _ => True) := by
  unfold hash.short_block
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps

/-- The seed (midstate) may be secret too. -/
@[ct_rel] theorem thash_short (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs)
    (m m' : Slice U8) (h : m.length = m'.length) :
    Rel (hash.thash_short seed adrs m) (hash.thash_short seed' adrs m') (fun _ _ => True) := by
  unfold hash.thash_short
  ct_steps

/-- The inner loop body of `chain_blocks`: the chain bound `end[i]` and the position `t` are
public (they are WOTS digits / chain lengths, declassified through the signature), the blocks
are secret (equal length). -/
theorem chain_blocks_portable_loop0_loop0_body (state state' : Array U32 8#usize)
    (e : Slice U32) (i : Usize) (blocks blocks' : Slice (Array U8 64#usize)) (t : U32)
    (h : blocks.length = blocks'.length) :
    Rel (hash.chain_blocks_portable_loop0_loop0.body state e i blocks t)
      (hash.chain_blocks_portable_loop0_loop0.body state' e i blocks' t)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2)
        (fun p q => p.length = q.length)) := by
  unfold hash.chain_blocks_portable_loop0_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

end Ct.Hash
