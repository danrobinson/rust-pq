import Ct.Sha512
import Ct.Heads

/-!
# Constant time: the `hash.rs` layer (and `xmss::hash2`)

Every function of `hash.rs`: the trace depends only on the public arguments (the hash length
`N`, the parameter set, addresses, chain bounds) and on the lengths of the others. Secret
arguments (seeds, SHA-256 and SHA-512 states, blocks, messages of a given length) appear as
separate variables on the two sides. The branches on `N = 16` (SHA-256 or SHA-512) have the
same outcome in both runs: `N` is shared.

As in the main tree, the blocks of `chain_blocks` are related by `HeadsEq` (same first 16
bytes); the portable kernel does not need it, but the statement is kept the same as the main
tree's (whose hardware kernel does). `hash::chain_blocks` itself is in `Ct/ChainTop.lean`, the
one file of this layer that depends on the build (`../lean-hw/Ct/ChainTop.lean` for
`hw-sha2`); this file is shared by both builds.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Hash

open slhdsa_leak

@[ct_rel] theorem trunc (N : Usize) (st st' : Array U32 8#usize) :
    Rel (hash.trunc N st) (hash.trunc N st') (fun _ _ => True) := by
  unfold hash.trunc
  ct_steps

@[ct_rel] theorem trunc512 (N : Usize) (st st' : Array U64 8#usize) :
    Rel (hash.trunc512 N st) (hash.trunc512 N st') (fun _ _ => True) := by
  unfold hash.trunc512
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
@[ct_rel] theorem thash_short {N : Usize} (seed seed' : slhdsa.hash.Seed N)
    (adrs : slhdsa.address.Adrs) (m m' : Slice U8) (h : m.length = m'.length) :
    Rel (hash.thash_short seed adrs m) (hash.thash_short seed' adrs m') (fun _ _ => True) := by
  unfold hash.thash_short
  ct_steps

set_option maxHeartbeats 1000000 in
/-- The inner loop body of `chain_blocks_portable`: the chain bound `end[i]` and the position
`t` are public (they are WOTS digits / chain lengths, declassified through the signature), the
blocks are secret except for their heads, which the loop does not change (it writes bytes
18..22 + N). -/
theorem chain_blocks_portable_loop0_loop0_body (N : Usize) (state state' : Array U32 8#usize)
    (e : Slice U32) (i : Usize) (blocks blocks' : Slice (Array U8 64#usize)) (t : U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable_loop0_loop0.body N state e i blocks t)
      (hash.chain_blocks_portable_loop0_loop0.body N state' e i blocks' t)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)
        (fun p q => HeadsEq p.val q.val)) := by
  have hl := Heads.slice_length_eq h
  unfold hash.chain_blocks_portable_loop0_loop0.body
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | skip
  · simp only [CFRel_cont_cont, and_true]
    heads_tac

@[ct_rel] theorem chain_blocks_portable_loop0_loop0 (N : Usize) (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (e : Slice U32) (i : Usize) (t : U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable_loop0_loop0 N state blocks e i t)
      (hash.chain_blocks_portable_loop0_loop0 N state' blocks' e i t)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks_portable_loop0_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨b, t1⟩ ⟨b', t1'⟩ ⟨hb, (rfl : t1 = t1')⟩
  exact chain_blocks_portable_loop0_loop0_body N state state' e i b b' t1 hb

theorem chain_blocks_portable_loop0_body (N : Usize) (state state' : Array U32 8#usize)
    (start e : Slice U32) (blocks blocks' : Slice (Array U8 64#usize)) (i : Usize)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable_loop0.body N state start e blocks i)
      (hash.chain_blocks_portable_loop0.body N state' start e blocks' i)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)
        (fun p q => HeadsEq p.val q.val)) := by
  unfold hash.chain_blocks_portable_loop0.body
  simp only [(Ct.Facts.slice_len_congr (Heads.slice_length_eq h)).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem chain_blocks_portable_loop0 (N : Usize) (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (start e : Slice U32) (i : Usize)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable_loop0 N state blocks start e i)
      (hash.chain_blocks_portable_loop0 N state' blocks' start e i)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks_portable_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨b, i1⟩ ⟨b', i1'⟩ ⟨hb, (rfl : i1 = i1')⟩
  exact chain_blocks_portable_loop0_body N state state' start e b b' i1 hb

/-- `chain_blocks_portable`: the state and the blocks are secret, except for the blocks'
heads; the chain bounds are public. -/
@[ct_rel] theorem chain_blocks_portable (N : Usize) (state state' : Array U32 8#usize)
    (blocks blocks' : Slice (Array U8 64#usize)) (start e : Slice U32)
    (h : HeadsEq blocks.val blocks'.val) :
    Rel (hash.chain_blocks_portable N state blocks start e)
      (hash.chain_blocks_portable N state' blocks' start e)
      (fun p q => HeadsEq p.val q.val) := by
  unfold hash.chain_blocks_portable
  exact chain_blocks_portable_loop0 N state state' blocks blocks' start e 0#usize h

theorem thash_values_loop0_body (N : Usize) (blocks blocks' : Slice (Array U8 64#usize))
    (buf buf' : Array U8 640#usize) (i : Usize) (h : blocks.length = blocks'.length) :
    Rel (hash.thash_values_loop0.body N blocks buf i) (hash.thash_values_loop0.body N blocks' buf' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold hash.thash_values_loop0.body
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem thash_values_loop0 (N : Usize) (blocks blocks' : Slice (Array U8 64#usize))
    (buf buf' : Array U8 640#usize) (i : Usize) (h : blocks.length = blocks'.length) :
    Rel (hash.thash_values_loop0 N blocks buf i) (hash.thash_values_loop0 N blocks' buf' i)
      (fun _ _ => True) := by
  unfold hash.thash_values_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨b, i1⟩ ⟨b', i1'⟩ (rfl : i1 = i1')
  exact thash_values_loop0_body N blocks blocks' b b' i1 h

theorem thash_values_loop1_body (buf buf' : Array U8 640#usize) (total : Usize)
    (st st' : Array U32 8#usize) (off : Usize) :
    Rel (hash.thash_values_loop1.body buf total st off)
      (hash.thash_values_loop1.body buf' total st' off)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold hash.thash_values_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem thash_values_loop1 (buf buf' : Array U8 640#usize) (total : Usize)
    (st st' : Array U32 8#usize) (off : Usize) :
    Rel (hash.thash_values_loop1 buf total st off) (hash.thash_values_loop1 buf' total st' off)
      (fun _ _ => True) := by
  unfold hash.thash_values_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨s, o⟩ ⟨s', o'⟩ (rfl : o = o')
  exact thash_values_loop1_body buf buf' total s s' o

theorem thash_values_loop2_body (N : Usize) (blocks blocks' : Slice (Array U8 64#usize))
    (buf buf' : Array U8 2304#usize) (i : Usize) (h : blocks.length = blocks'.length) :
    Rel (hash.thash_values_loop2.body N blocks buf i) (hash.thash_values_loop2.body N blocks' buf' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold hash.thash_values_loop2.body
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem thash_values_loop2 (N : Usize) (blocks blocks' : Slice (Array U8 64#usize))
    (buf buf' : Array U8 2304#usize) (i : Usize) (h : blocks.length = blocks'.length) :
    Rel (hash.thash_values_loop2 N blocks buf i) (hash.thash_values_loop2 N blocks' buf' i)
      (fun _ _ => True) := by
  unfold hash.thash_values_loop2
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨b, i1⟩ ⟨b', i1'⟩ (rfl : i1 = i1')
  exact thash_values_loop2_body N blocks blocks' b b' i1 h

theorem thash_values_loop3_body (buf buf' : Array U8 2304#usize) (total : Usize)
    (st st' : Array U64 8#usize) (off : Usize) :
    Rel (hash.thash_values_loop3.body buf total st off)
      (hash.thash_values_loop3.body buf' total st' off)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold hash.thash_values_loop3.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem thash_values_loop3 (buf buf' : Array U8 2304#usize) (total : Usize)
    (st st' : Array U64 8#usize) (off : Usize) :
    Rel (hash.thash_values_loop3 buf total st off) (hash.thash_values_loop3 buf' total st' off)
      (fun _ _ => True) := by
  unfold hash.thash_values_loop3
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨s, o⟩ ⟨s', o'⟩ (rfl : o = o')
  exact thash_values_loop3_body buf buf' total s s' o

@[ct_rel] theorem thash_values {N : Usize} (seed seed' : slhdsa.hash.Seed N)
    (adrs : slhdsa.address.Adrs) (blocks blocks' : Slice (Array U8 64#usize))
    (h : blocks.length = blocks'.length) :
    Rel (hash.thash_values seed adrs blocks) (hash.thash_values seed' adrs blocks')
      (fun _ _ => True) := by
  unfold hash.thash_values
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps

@[ct_rel] theorem thash {N : Usize} (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs)
    (m m' : Slice U8) (h : m.length = m'.length) :
    Rel (hash.thash seed adrs m) (hash.thash seed' adrs m') (fun _ _ => True) := by
  unfold hash.thash
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem value (N : Usize) (b b' : Array U8 64#usize) :
    Rel (hash.value N b) (hash.value N b') (fun _ _ => True) := by
  unfold hash.value
  ct_steps

@[ct_rel] theorem pair_block {N : Usize} (adrs : slhdsa.address.Adrs) (l l' r r' : Array U8 N) :
    Rel (hash.pair_block adrs l r) (hash.pair_block adrs l' r') (fun b b' => HeadEq b b') := by
  unfold hash.pair_block
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | heads_tac

@[ct_rel] theorem thash_pair {N : Usize} (seed seed' : slhdsa.hash.Seed N)
    (adrs : slhdsa.address.Adrs) (l l' r r' : Array U8 N) :
    Rel (hash.thash_pair seed adrs l r) (hash.thash_pair seed' adrs l' r') (fun _ _ => True) := by
  unfold hash.thash_pair
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem hash2 {N : Usize} (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs)
    (l l' r r' : Array U8 N) :
    Rel (xmss.hash2 seed adrs l r) (xmss.hash2 seed' adrs l' r') (fun _ _ => True) := by
  unfold xmss.hash2
  ct_steps

/-- `seed_ctx`: even `PK.seed` only enters through its (fixed) length. -/
@[ct_rel] theorem seed_ctx {N : Usize} (p p' : Array U8 N) :
    Rel (hash.seed_ctx p) (hash.seed_ctx p') (fun _ _ => True) := by
  unfold hash.seed_ctx
  ct_steps

theorem mgf1_sha256_loop_body (seed seed' : Slice U8) (len : Usize) (t t' : alloc.vec.Vec U8)
    (c : U32) (hs : seed.length = seed'.length) (ht : t.length = t'.length) :
    Rel (hash.mgf1_sha256_loop.body seed len t c) (hash.mgf1_sha256_loop.body seed' len t' c)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2)
        (fun p q => p.length = q.length)) := by
  unfold hash.mgf1_sha256_loop.body
  simp only [(Ct.Facts.vec_len_congr ht).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem mgf1_sha256_loop (seed seed' : Slice U8) (len : Usize) (t t' : alloc.vec.Vec U8)
    (c : U32) (hs : seed.length = seed'.length) (ht : t.length = t'.length) :
    Rel (hash.mgf1_sha256_loop seed len t c) (hash.mgf1_sha256_loop seed' len t' c)
      (fun p q => p.length = q.length) := by
  unfold hash.mgf1_sha256_loop
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨ht, rfl⟩
  rintro ⟨a, j⟩ ⟨a', j'⟩ ⟨ha, (rfl : j = j')⟩
  exact mgf1_sha256_loop_body seed seed' len a a' j hs ha

@[ct_rel] theorem mgf1_sha256 (seed seed' : Slice U8) (len : Usize)
    (hs : seed.length = seed'.length) :
    Rel (hash.mgf1_sha256 seed len) (hash.mgf1_sha256 seed' len)
      (fun p q => p.length = q.length) := by
  unfold hash.mgf1_sha256
  ct_steps
  all_goals (ct_facts; simp_all)

theorem mgf1_sha512_loop_body (seed seed' : Slice U8) (len : Usize) (t t' : alloc.vec.Vec U8)
    (c : U32) (hs : seed.length = seed'.length) (ht : t.length = t'.length) :
    Rel (hash.mgf1_sha512_loop.body seed len t c) (hash.mgf1_sha512_loop.body seed' len t' c)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2)
        (fun p q => p.length = q.length)) := by
  unfold hash.mgf1_sha512_loop.body
  simp only [(Ct.Facts.vec_len_congr ht).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem mgf1_sha512_loop (seed seed' : Slice U8) (len : Usize) (t t' : alloc.vec.Vec U8)
    (c : U32) (hs : seed.length = seed'.length) (ht : t.length = t'.length) :
    Rel (hash.mgf1_sha512_loop seed len t c) (hash.mgf1_sha512_loop seed' len t' c)
      (fun p q => p.length = q.length) := by
  unfold hash.mgf1_sha512_loop
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨ht, rfl⟩
  rintro ⟨a, j⟩ ⟨a', j'⟩ ⟨ha, (rfl : j = j')⟩
  exact mgf1_sha512_loop_body seed seed' len a a' j hs ha

@[ct_rel] theorem mgf1_sha512 (seed seed' : Slice U8) (len : Usize)
    (hs : seed.length = seed'.length) :
    Rel (hash.mgf1_sha512 seed len) (hash.mgf1_sha512 seed' len)
      (fun p q => p.length = q.length) := by
  unfold hash.mgf1_sha512
  ct_steps
  all_goals (ct_facts; simp_all)

/-- `h_msg_inner256`: only the length of the message matters. -/
@[ct_rel] theorem h_msg_inner256 {N : Usize} (r r' ps ps' pr pr' : Array U8 N) (m m' : Slice U8)
    (h : m.length = m'.length) :
    Rel (hash.h_msg_inner256 r ps pr m) (hash.h_msg_inner256 r' ps' pr' m') (fun _ _ => True) := by
  unfold hash.h_msg_inner256
  rw [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem h_msg_inner512 {N : Usize} (r r' ps ps' pr pr' : Array U8 N) (m m' : Slice U8)
    (h : m.length = m'.length) :
    Rel (hash.h_msg_inner512 r ps pr m) (hash.h_msg_inner512 r' ps' pr' m') (fun _ _ => True) := by
  unfold hash.h_msg_inner512
  rw [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem h_msg {N : Usize} (p : slhdsa.params.Params) (r r' ps ps' pr pr' : Array U8 N)
    (m m' : Slice U8) (h : m.length = m'.length) :
    Rel (hash.h_msg p r ps pr m) (hash.h_msg p r' ps' pr' m') (fun a b => a.length = b.length) := by
  unfold hash.h_msg
  ct_steps
  all_goals (ct_facts; simp_all)

theorem prf_msg_loop0_body {N : Usize} (k k' : Array U8 N) (ip ip' op op' : Array U8 64#usize)
    (i : Usize) :
    Rel (hash.prf_msg_loop0.body k ip op i) (hash.prf_msg_loop0.body k' ip' op' i)
      (CFRel (fun p q => p.2.2 = q.2.2) (fun _ _ => True)) := by
  unfold hash.prf_msg_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem prf_msg_loop0 {N : Usize} (k k' : Array U8 N) (ip ip' op op' : Array U8 64#usize)
    (i : Usize) :
    Rel (hash.prf_msg_loop0 k ip op i) (hash.prf_msg_loop0 k' ip' op' i) (fun _ _ => True) := by
  unfold hash.prf_msg_loop0
  refine Rel.loop (fun p q => p.2.2 = q.2.2) ?_ rfl
  rintro ⟨a, b, j⟩ ⟨a', b', j'⟩ (rfl : j = j')
  exact prf_msg_loop0_body k k' a a' b b' j

theorem prf_msg_loop1_body {N : Usize} (k k' : Array U8 N) (ip ip' op op' : Array U8 128#usize)
    (i : Usize) :
    Rel (hash.prf_msg_loop1.body k ip op i) (hash.prf_msg_loop1.body k' ip' op' i)
      (CFRel (fun p q => p.2.2 = q.2.2) (fun _ _ => True)) := by
  unfold hash.prf_msg_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem prf_msg_loop1 {N : Usize} (k k' : Array U8 N)
    (ip ip' op op' : Array U8 128#usize) (i : Usize) :
    Rel (hash.prf_msg_loop1 k ip op i) (hash.prf_msg_loop1 k' ip' op' i) (fun _ _ => True) := by
  unfold hash.prf_msg_loop1
  refine Rel.loop (fun p q => p.2.2 = q.2.2) ?_ rfl
  rintro ⟨a, b, j⟩ ⟨a', b', j'⟩ (rfl : j = j')
  exact prf_msg_loop1_body k k' a a' b b' j

/-- `PRF_msg`: `SK.prf` and `opt_rand` are secret; only the length of the message matters. -/
@[ct_rel] theorem prf_msg {N : Usize} (k k' o o' : Array U8 N) (m m' : Slice U8)
    (h : m.length = m'.length) :
    Rel (hash.prf_msg k o m) (hash.prf_msg k' o' m') (fun _ _ => True) := by
  unfold hash.prf_msg
  ct_steps
  all_goals (ct_facts; simp_all)

end Ct.Hash
