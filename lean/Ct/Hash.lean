import Ct.Sha256
import Ct.Heads

/-!
# Constant time: the `hash.rs` layer (and `xmss::hash2`)

Every function of `hash.rs`: the trace depends only on the public arguments (addresses, chain
bounds) and on the lengths of the others. Secret arguments (seeds, SHA-256 states, blocks,
messages of a given length) appear as separate variables on the two sides.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Hash

open slhdsa_leak

@[ct_rel] theorem trunc (st st' : Array U32 8#usize) :
    Rel (hash.trunc st) (hash.trunc st') (fun _ _ => True) := by
  unfold hash.trunc
  ct_steps

/-- The address is public; the message is secret (only its length matters). The two blocks
have the same head (the first 16 bytes of the compressed address). -/
@[ct_rel] theorem short_block (adrs : slhdsa.address.Adrs) (m m' : Slice U8)
    (h : m.length = m'.length) :
    Rel (hash.short_block adrs m) (hash.short_block adrs m') (fun b b' => HeadEq b b') := by
  unfold hash.short_block
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  heads_tac

/-- The seed (midstate) may be secret too. -/
@[ct_rel] theorem thash_short (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs)
    (m m' : Slice U8) (h : m.length = m'.length) :
    Rel (hash.thash_short seed adrs m) (hash.thash_short seed' adrs m') (fun _ _ => True) := by
  unfold hash.thash_short
  ct_steps

/-- The inner loop body of `chain_blocks_portable`: the chain bound `end[i]` and the position
`t` are public (they are WOTS digits / chain lengths, declassified through the signature), the
blocks are secret except for their heads, which the loop does not change (it writes bytes
18..38). -/
theorem chain_blocks_portable_loop0_loop0_body (state state' : Array U32 8#usize)
    (e : Slice U32) (i : Usize) (blocks blocks' : Slice (Array U8 64#usize)) (t : U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable_loop0_loop0.body state e i blocks t)
      (hash.chain_blocks_portable_loop0_loop0.body state' e i blocks' t)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)
        (fun p q => HeadsEq p.val q.val)) := by
  have hl := Heads.slice_length_eq h
  unfold hash.chain_blocks_portable_loop0_loop0.body
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | skip
  · simp only [CFRel_cont_cont, and_true]
    heads_tac

@[ct_rel] theorem chain_blocks_portable_loop0_loop0 (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (e : Slice U32) (i : Usize) (t : U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable_loop0_loop0 state blocks e i t)
      (hash.chain_blocks_portable_loop0_loop0 state' blocks' e i t)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks_portable_loop0_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨b, t1⟩ ⟨b', t1'⟩ ⟨hb, (rfl : t1 = t1')⟩
  exact chain_blocks_portable_loop0_loop0_body state state' e i b b' t1 hb

theorem chain_blocks_portable_loop0_body (state state' : Array U32 8#usize)
    (start e : Slice U32) (blocks blocks' : Slice (Array U8 64#usize)) (i : Usize)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable_loop0.body state start e blocks i)
      (hash.chain_blocks_portable_loop0.body state' start e blocks' i)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)
        (fun p q => HeadsEq p.val q.val)) := by
  unfold hash.chain_blocks_portable_loop0.body
  simp only [(Ct.Facts.slice_len_congr (Heads.slice_length_eq h)).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem chain_blocks_portable_loop0 (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (start e : Slice U32) (i : Usize)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable_loop0 state blocks start e i)
      (hash.chain_blocks_portable_loop0 state' blocks' start e i)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks_portable_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨b, i1⟩ ⟨b', i1'⟩ ⟨hb, (rfl : i1 = i1')⟩
  exact chain_blocks_portable_loop0_body state state' start e b b' i1 hb

/-- `chain_blocks_portable`: the state and the blocks are secret, except for the blocks'
heads; the chain bounds are public. -/
@[ct_rel] theorem chain_blocks_portable (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (start e : Slice U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable state blocks start e)
      (hash.chain_blocks_portable state' blocks' start e)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks_portable
  exact chain_blocks_portable_loop0 state state' blocks blocks' start e 0#usize h

theorem thash_values_loop0_body (blocks blocks' : Array (Array U8 64#usize) 35#usize)
    (buf buf' : Array U8 640#usize) (i : Usize) :
    Rel (hash.thash_values_loop0.body blocks buf i) (hash.thash_values_loop0.body blocks' buf' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold hash.thash_values_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem thash_values_loop0 (blocks blocks' : Array (Array U8 64#usize) 35#usize)
    (buf buf' : Array U8 640#usize) (i : Usize) :
    Rel (hash.thash_values_loop0 blocks buf i) (hash.thash_values_loop0 blocks' buf' i)
      (fun _ _ => True) := by
  unfold hash.thash_values_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨b, i1⟩ ⟨b', i1'⟩ (rfl : i1 = i1')
  exact thash_values_loop0_body blocks blocks' b b' i1

theorem thash_values_loop1_body (buf buf' : Array U8 640#usize) (st st' : Array U32 8#usize)
    (off : Usize) :
    Rel (hash.thash_values_loop1.body buf st off) (hash.thash_values_loop1.body buf' st' off)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold hash.thash_values_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem thash_values_loop1 (buf buf' : Array U8 640#usize) (st st' : Array U32 8#usize)
    (off : Usize) :
    Rel (hash.thash_values_loop1 buf st off) (hash.thash_values_loop1 buf' st' off)
      (fun _ _ => True) := by
  unfold hash.thash_values_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨s, o⟩ ⟨s', o'⟩ (rfl : o = o')
  exact thash_values_loop1_body buf buf' s s' o

@[ct_rel] theorem thash_values (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs)
    (blocks blocks' : Array (Array U8 64#usize) 35#usize) :
    Rel (hash.thash_values seed adrs blocks) (hash.thash_values seed' adrs blocks')
      (fun _ _ => True) := by
  unfold hash.thash_values
  ct_steps

@[ct_rel] theorem thash (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs)
    (m m' : Slice U8) (h : m.length = m'.length) :
    Rel (hash.thash seed adrs m) (hash.thash seed' adrs m') (fun _ _ => True) := by
  unfold hash.thash
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem value (b b' : Array U8 64#usize) :
    Rel (hash.value b) (hash.value b') (fun _ _ => True) := by
  unfold hash.value
  ct_steps

@[ct_rel] theorem pair_block (adrs : slhdsa.address.Adrs) (l l' r r' : Array U8 16#usize) :
    Rel (hash.pair_block adrs l r) (hash.pair_block adrs l' r') (fun b b' => HeadEq b b') := by
  unfold hash.pair_block
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem hash2 (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs)
    (l l' r r' : Array U8 16#usize) :
    Rel (xmss.hash2 seed adrs l r) (xmss.hash2 seed' adrs l' r') (fun _ _ => True) := by
  unfold xmss.hash2
  ct_steps
  all_goals (ct_facts; simp_all)

/-- `seed_ctx`: even `PK.seed` only enters through its (fixed) length. -/
@[ct_rel] theorem seed_ctx (p p' : Array U8 16#usize) :
    Rel (hash.seed_ctx p) (hash.seed_ctx p') (fun _ _ => True) := by
  unfold hash.seed_ctx
  ct_steps

/-- `h_msg_inner`: only the length of the message matters. -/
@[ct_rel] theorem h_msg_inner (r r' ps ps' pr pr' : Array U8 16#usize) (m m' : Slice U8)
    (h : m.length = m'.length) :
    Rel (hash.h_msg_inner r ps pr m) (hash.h_msg_inner r' ps' pr' m') (fun _ _ => True) := by
  unfold hash.h_msg_inner
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem h_msg (r r' ps ps' pr pr' : Array U8 16#usize) (m m' : Slice U8)
    (h : m.length = m'.length) :
    Rel (hash.h_msg r ps pr m) (hash.h_msg r' ps' pr' m') (fun _ _ => True) := by
  unfold hash.h_msg
  ct_steps
  all_goals (ct_facts; simp_all)

theorem prf_msg_loop_body (k k' : Array U8 16#usize) (ip ip' op op' : Array U8 64#usize)
    (i : Usize) :
    Rel (hash.prf_msg_loop.body k ip op i) (hash.prf_msg_loop.body k' ip' op' i)
      (CFRel (fun p q => p.2.2 = q.2.2) (fun _ _ => True)) := by
  unfold hash.prf_msg_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem prf_msg_loop (k k' : Array U8 16#usize) (ip ip' op op' : Array U8 64#usize)
    (i : Usize) :
    Rel (hash.prf_msg_loop k ip op i) (hash.prf_msg_loop k' ip' op' i) (fun _ _ => True) := by
  unfold hash.prf_msg_loop
  refine Rel.loop (fun p q => p.2.2 = q.2.2) ?_ rfl
  rintro ⟨a, b, j⟩ ⟨a', b', j'⟩ (rfl : j = j')
  exact prf_msg_loop_body k k' a a' b b' j

/-- `PRF_msg`: `SK.prf` and `opt_rand` are secret; only the length of the message matters. -/
@[ct_rel] theorem prf_msg (k k' o o' : Array U8 16#usize) (m m' : Slice U8)
    (h : m.length = m'.length) :
    Rel (hash.prf_msg k o m) (hash.prf_msg k' o' m') (fun _ _ => True) := by
  unfold hash.prf_msg
  ct_steps
  all_goals (ct_facts; simp_all)

end Ct.Hash
