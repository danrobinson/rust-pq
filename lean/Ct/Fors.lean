import Ct.Xmss

/-!
# Constant time: `fors.rs`

The message digest (hence the FORS indices) and the address are public; the secret seed, the
seed state and every value derived from them (blocks, node values, signature bytes) only enter
the trace through their lengths. The tree indices that `fors_batch` and `fors_pk_from_sig` keep
in their `start`/`end`/`idx` arrays are public and are the same in the two runs.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Fors

open slhdsa_leak

abbrev Blocks := Array (Array U8 64#usize) 128#usize
abbrev Vals := Array (Array U8 16#usize) 128#usize
abbrev Idx := Array U32 128#usize

theorem fors_batch_loop0_body (sk sk' : Array U8 16#usize) (i z : U32) (n : Usize)
    (a : slhdsa.address.Adrs) (b b' : Blocks) (s e : Idx) (j : Usize) :
    Rel (fors.fors_batch_loop0.body sk i z n a b s e j)
      (fors.fors_batch_loop0.body sk' i z n a b' s e j)
      (CFRel (fun p q => p.2 = q.2) (fun p q => p.2 = q.2)) := by
  unfold fors.fors_batch_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_batch_loop0 (sk sk' : Array U8 16#usize) (i z : U32) (n : Usize)
    (a : slhdsa.address.Adrs) (b b' : Blocks) (s e : Idx) (j : Usize) :
    Rel (fors.fors_batch_loop0 sk i z n a b s e j) (fors.fors_batch_loop0 sk' i z n a b' s e j)
      (fun p q => p.2 = q.2) := by
  unfold fors.fors_batch_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, s1, e1, j1⟩ ⟨x', s1', e1', j1'⟩ hI
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ j1 = j1' := by simpa using hI
  exact fors_batch_loop0_body sk sk' i z n a x x' s1 e1 j1

theorem fors_batch_loop1_body (t : U32) (n : Usize) (b b' : Blocks) (j : Usize) :
    Rel (fors.fors_batch_loop1.body t n b j) (fors.fors_batch_loop1.body t n b' j)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_batch_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_batch_loop1 (t : U32) (n : Usize) (b b' : Blocks) (j : Usize) :
    Rel (fors.fors_batch_loop1 t n b j) (fors.fors_batch_loop1 t n b' j) (fun _ _ => True) := by
  unfold fors.fors_batch_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_batch_loop1_body t n x x' j1

theorem fors_batch_loop2_body (n : Usize) (b b' : Blocks) (v v' : Vals) (j : Usize) :
    Rel (fors.fors_batch_loop2.body n b v j) (fors.fors_batch_loop2.body n b' v' j)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_batch_loop2.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_batch_loop2 (n : Usize) (b b' : Blocks) (v v' : Vals) (j : Usize) :
    Rel (fors.fors_batch_loop2 n b v j) (fors.fors_batch_loop2 n b' v' j) (fun _ _ => True) := by
  unfold fors.fors_batch_loop2
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_batch_loop2_body n b b' x x' j1

theorem fors_batch_loop3_loop0_body (i z i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (v v' : Vals) (lvl : U32) (cnt : Usize) (b b' : Blocks) (s e : Idx) (j : Usize) :
    Rel (fors.fors_batch_loop3_loop0.body i z i1 i2 i3 i4 i5 i6 v lvl cnt b s e j)
      (fors.fors_batch_loop3_loop0.body i z i1 i2 i3 i4 i5 i6 v' lvl cnt b' s e j)
      (CFRel (fun p q => p.2 = q.2) (fun p q => p.2 = q.2)) := by
  unfold fors.fors_batch_loop3_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_batch_loop3_loop0 (i z i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (b b' : Blocks) (s e : Idx) (v v' : Vals) (lvl : U32) (cnt : Usize) (j : Usize) :
    Rel (fors.fors_batch_loop3_loop0 i z i1 i2 i3 i4 i5 i6 b s e v lvl cnt j)
      (fors.fors_batch_loop3_loop0 i z i1 i2 i3 i4 i5 i6 b' s e v' lvl cnt j)
      (fun p q => p.2 = q.2) := by
  unfold fors.fors_batch_loop3_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, s1, e1, j1⟩ ⟨x', s1', e1', j1'⟩ hI
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ j1 = j1' := by simpa using hI
  exact fors_batch_loop3_loop0_body i z i1 i2 i3 i4 i5 i6 v v' lvl cnt x x' s1 e1 j1

theorem fors_batch_loop3_loop1_body (b b' : Blocks) (cnt : Usize) (v v' : Vals) (j : Usize) :
    Rel (fors.fors_batch_loop3_loop1.body b cnt v j) (fors.fors_batch_loop3_loop1.body b' cnt v' j)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_batch_loop3_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_batch_loop3_loop1 (b b' : Blocks) (v v' : Vals) (cnt : Usize) (j : Usize) :
    Rel (fors.fors_batch_loop3_loop1 b v cnt j) (fors.fors_batch_loop3_loop1 b' v' cnt j)
      (fun _ _ => True) := by
  unfold fors.fors_batch_loop3_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_batch_loop3_loop1_body b b' cnt x x' j1

theorem fors_batch_loop3_body (i z : U32) (a a' : Array U32 8#usize) (i1 : U32) (i2 : U64)
    (i3 i4 i5 i6 : U32) (b b' : Blocks) (s e : Idx) (v v' : Vals) (lvl : U32) (cnt : Usize) :
    Rel (fors.fors_batch_loop3.body i z a i1 i2 i3 i4 i5 i6 b s e v lvl cnt)
      (fors.fors_batch_loop3.body i z a' i1 i2 i3 i4 i5 i6 b' s e v' lvl cnt)
      (CFRel (fun p q => p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2.2 = q.2.2.2.2)
        (fun _ _ => True)) := by
  unfold fors.fors_batch_loop3.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_batch_loop3 (i z : U32) (a a' : Array U32 8#usize) (i1 : U32) (i2 : U64)
    (i3 i4 i5 i6 : U32) (b b' : Blocks) (s e : Idx) (v v' : Vals) (lvl : U32) (cnt : Usize) :
    Rel (fors.fors_batch_loop3 i z a i1 i2 i3 i4 i5 i6 b s e v lvl cnt)
      (fors.fors_batch_loop3 i z a' i1 i2 i3 i4 i5 i6 b' s e v' lvl cnt) (fun _ _ => True) := by
  unfold fors.fors_batch_loop3
  refine Rel.loop (fun p q => p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2.2 = q.2.2.2.2) ?_
    ⟨rfl, rfl, rfl⟩
  rintro ⟨x, s1, e1, v1, l1, c1⟩ ⟨x', s1', e1', v1', l1', c1'⟩ hI
  obtain ⟨rfl, rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ l1 = l1' ∧ c1 = c1' := by simpa using hI
  exact fors_batch_loop3_body i z a a' i1 i2 i3 i4 i5 i6 x x' s1 e1 v1 v1' l1 c1

@[ct_rel] theorem fors_batch (sk sk' : Array U8 16#usize) (i z : U32)
    (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs) :
    Rel (fors.fors_batch sk i z seed adrs) (fors.fors_batch sk' i z seed' adrs)
      (fun _ _ => True) := by
  unfold fors.fors_batch
  ct_steps
  all_goals (ct_facts; simp_all)

/-- `fors_node`, by strong induction on the height. -/
@[ct_rel] theorem fors_node (sk sk' : Array U8 16#usize) (i z : U32)
    (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs) :
    Rel (fors.fors_node sk i z seed adrs) (fors.fors_node sk' i z seed' adrs)
      (fun _ _ => True) := by
  induction hz : z.val using Nat.strong_induction_on generalizing i z with
  | _ n ih =>
    rw [fors.fors_node, fors.fors_node]
    ct_steps
    all_goals first
      | (simp only [Ct.Facts.erase_liftM] at *
         ct_facts
         refine ih _ ?_ _ _ rfl
         simp_all; omega)
      | (ct_facts; simp_all)

theorem fors_pk_gen_loop_body (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) (r r' : alloc.vec.Vec U8) (i : U32) (h : r.length = r'.length) :
    Rel (fors.fors_pk_gen_loop.body sk seed adrs r i) (fors.fors_pk_gen_loop.body sk' seed' adrs r' i)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold fors.fors_pk_gen_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_pk_gen_loop (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) (r r' : alloc.vec.Vec U8) (i : U32) (h : r.length = r'.length) :
    Rel (fors.fors_pk_gen_loop sk seed adrs r i) (fors.fors_pk_gen_loop sk' seed' adrs r' i)
      (fun p q => p.length = q.length) := by
  unfold fors.fors_pk_gen_loop
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact fors_pk_gen_loop_body sk sk' seed seed' adrs x x' k hx

/-- `fors_pk_gen` (new: the second route to the FORS public key): nothing secret reaches the
trace. -/
@[ct_rel] theorem fors_pk_gen (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) :
    Rel (fors.fors_pk_gen sk seed adrs) (fors.fors_pk_gen sk' seed' adrs) (fun _ _ => True) := by
  unfold fors.fors_pk_gen
  ct_steps
  all_goals (ct_facts; simp_all)

abbrev KBlocks := Array (Array U8 64#usize) 14#usize
abbrev KVals := Array (Array U8 16#usize) 14#usize
abbrev KIdx := Array U32 14#usize

theorem fors_pk_from_sig_loop0_body (sig sig' : Slice U8) (adrs : slhdsa.address.Adrs)
    (ind : alloc.vec.Vec U32) (b b' : KBlocks) (idx e : KIdx) (i : Usize)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig_loop0.body sig adrs ind b idx e i)
      (fors.fors_pk_from_sig_loop0.body sig' adrs ind b' idx e i)
      (CFRel (fun p q => p.2 = q.2) (fun p q => p.2 = q.2)) := by
  unfold fors.fors_pk_from_sig_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_pk_from_sig_loop0 (sig sig' : Slice U8) (adrs : slhdsa.address.Adrs)
    (ind : alloc.vec.Vec U32) (b b' : KBlocks) (idx e : KIdx) (i : Usize)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig_loop0 sig adrs ind b idx e i)
      (fors.fors_pk_from_sig_loop0 sig' adrs ind b' idx e i) (fun p q => p.2 = q.2) := by
  unfold fors.fors_pk_from_sig_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, s1, e1, j1⟩ ⟨x', s1', e1', j1'⟩ hI
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ j1 = j1' := by simpa using hI
  exact fors_pk_from_sig_loop0_body sig sig' adrs ind x x' s1 e1 j1 h

theorem fors_pk_from_sig_loop1_body (b b' : KBlocks) (v v' : KVals) (i : Usize) :
    Rel (fors.fors_pk_from_sig_loop1.body b v i) (fors.fors_pk_from_sig_loop1.body b' v' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_pk_from_sig_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_pk_from_sig_loop1 (b b' : KBlocks) (v v' : KVals) (i : Usize) :
    Rel (fors.fors_pk_from_sig_loop1 b v i) (fors.fors_pk_from_sig_loop1 b' v' i)
      (fun _ _ => True) := by
  unfold fors.fors_pk_from_sig_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_pk_from_sig_loop1_body b b' x x' j1

theorem fors_pk_from_sig_loop2_loop0_body (sig sig' : Slice U8) (adrs : slhdsa.address.Adrs)
    (v v' : KVals) (k : U32) (b b' : KBlocks) (idx e : KIdx) (i : Usize)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig_loop2_loop0.body sig adrs v k b idx e i)
      (fors.fors_pk_from_sig_loop2_loop0.body sig' adrs v' k b' idx e i)
      (CFRel (fun p q => p.2 = q.2) (fun p q => p.2 = q.2)) := by
  unfold fors.fors_pk_from_sig_loop2_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_pk_from_sig_loop2_loop0 (sig sig' : Slice U8) (adrs : slhdsa.address.Adrs)
    (b b' : KBlocks) (idx e : KIdx) (v v' : KVals) (k : U32) (i : Usize)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig_loop2_loop0 sig adrs b idx e v k i)
      (fors.fors_pk_from_sig_loop2_loop0 sig' adrs b' idx e v' k i) (fun p q => p.2 = q.2) := by
  unfold fors.fors_pk_from_sig_loop2_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, s1, e1, j1⟩ ⟨x', s1', e1', j1'⟩ hI
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ j1 = j1' := by simpa using hI
  exact fors_pk_from_sig_loop2_loop0_body sig sig' adrs v v' k x x' s1 e1 j1 h

theorem fors_pk_from_sig_loop2_loop1_body (b b' : KBlocks) (v v' : KVals) (i : Usize) :
    Rel (fors.fors_pk_from_sig_loop2_loop1.body b v i)
      (fors.fors_pk_from_sig_loop2_loop1.body b' v' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_pk_from_sig_loop2_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_pk_from_sig_loop2_loop1 (b b' : KBlocks) (v v' : KVals) (i : Usize) :
    Rel (fors.fors_pk_from_sig_loop2_loop1 b v i) (fors.fors_pk_from_sig_loop2_loop1 b' v' i)
      (fun _ _ => True) := by
  unfold fors.fors_pk_from_sig_loop2_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_pk_from_sig_loop2_loop1_body b b' x x' j1

theorem fors_pk_from_sig_loop2_body (sig sig' : Slice U8) (a a' : Array U32 8#usize)
    (adrs : slhdsa.address.Adrs) (b b' : KBlocks) (idx e : KIdx) (v v' : KVals) (k : U32)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig_loop2.body sig a adrs b idx e v k)
      (fors.fors_pk_from_sig_loop2.body sig' a' adrs b' idx e v' k)
      (CFRel (fun p q => p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2.2 = q.2.2.2.2)
        (fun _ _ => True)) := by
  unfold fors.fors_pk_from_sig_loop2.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_pk_from_sig_loop2 (sig sig' : Slice U8) (a a' : Array U32 8#usize)
    (adrs : slhdsa.address.Adrs) (b b' : KBlocks) (idx e : KIdx) (v v' : KVals) (k : U32)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig_loop2 sig a adrs b idx e v k)
      (fors.fors_pk_from_sig_loop2 sig' a' adrs b' idx e v' k) (fun _ _ => True) := by
  unfold fors.fors_pk_from_sig_loop2
  refine Rel.loop (fun p q => p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2.2 = q.2.2.2.2) ?_
    ⟨rfl, rfl, rfl⟩
  rintro ⟨x, s1, e1, v1, k1⟩ ⟨x', s1', e1', v1', k1'⟩ hI
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ k1 = k1' := by simpa using hI
  exact fors_pk_from_sig_loop2_body sig sig' a a' adrs x x' s1 e1 v1 v1' k1 h

theorem fors_pk_from_sig_loop3_body (v v' : KVals) (r r' : alloc.vec.Vec U8) (i : Usize)
    (h : r.length = r'.length) :
    Rel (fors.fors_pk_from_sig_loop3.body v r i) (fors.fors_pk_from_sig_loop3.body v' r' i)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold fors.fors_pk_from_sig_loop3.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_pk_from_sig_loop3 (v v' : KVals) (r r' : alloc.vec.Vec U8) (i : Usize)
    (h : r.length = r'.length) :
    Rel (fors.fors_pk_from_sig_loop3 v r i) (fors.fors_pk_from_sig_loop3 v' r' i)
      (fun p q => p.length = q.length) := by
  unfold fors.fors_pk_from_sig_loop3
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact fors_pk_from_sig_loop3_body v v' x x' k hx

/-- `fors_pkFromSig`: the digest (indices) is public; the signature is secret (length only). -/
@[ct_rel] theorem fors_pk_from_sig (sig sig' : Slice U8) (md : Slice U8)
    (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs) (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig sig md seed adrs) (fors.fors_pk_from_sig sig' md seed' adrs)
      (fun _ _ => True) := by
  unfold fors.fors_pk_from_sig
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_sk_gen (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) (idx : U32) :
    Rel (fors.fors_sk_gen sk seed adrs idx) (fors.fors_sk_gen sk' seed' adrs idx)
      (fun _ _ => True) := by
  unfold fors.fors_sk_gen
  ct_steps

theorem fors_sign_loop0_loop0_body (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) (i idx : U32) (sig sig' : alloc.vec.Vec U8) (j : U32)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_sign_loop0_loop0.body sk seed adrs i idx sig j)
      (fors.fors_sign_loop0_loop0.body sk' seed' adrs i idx sig' j)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold fors.fors_sign_loop0_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_sign_loop0_loop0 (sk sk' : Array U8 16#usize)
    (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs) (sig sig' : alloc.vec.Vec U8)
    (i idx j : U32) (h : sig.length = sig'.length) :
    Rel (fors.fors_sign_loop0_loop0 sk seed adrs sig i idx j)
      (fors.fors_sign_loop0_loop0 sk' seed' adrs sig' i idx j) (fun p q => p.length = q.length) := by
  unfold fors.fors_sign_loop0_loop0
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact fors_sign_loop0_loop0_body sk sk' seed seed' adrs i idx x x' k hx

theorem fors_sign_loop0_body (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) (ind : alloc.vec.Vec U32) (sig sig' : alloc.vec.Vec U8) (i : U32)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_sign_loop0.body sk seed adrs ind sig i)
      (fors.fors_sign_loop0.body sk' seed' adrs ind sig' i)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold fors.fors_sign_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_sign_loop0 (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) (ind : alloc.vec.Vec U32) (sig sig' : alloc.vec.Vec U8) (i : U32)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_sign_loop0 sk seed adrs ind sig i) (fors.fors_sign_loop0 sk' seed' adrs ind sig' i)
      (fun p q => p.length = q.length) := by
  unfold fors.fors_sign_loop0
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact fors_sign_loop0_body sk sk' seed seed' adrs ind x x' k hx

/-- `fors_sign`: the digest is public (its indices select the revealed leaves and the
authentication paths). -/
@[ct_rel] theorem fors_sign (md : Slice U8) (sk sk' : Array U8 16#usize)
    (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs) :
    Rel (fors.fors_sign md sk seed adrs) (fors.fors_sign md sk' seed' adrs)
      (fun p q => p.length = q.length) := by
  unfold fors.fors_sign
  ct_steps

end Ct.Fors
