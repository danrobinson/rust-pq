import Ct.Xmss

/-!
# Constant time: `fors.rs`

(Adapted from the single-set tree's `lean/Ct/Fors.lean` to the hash length `N`, the parameter set
`p`, the arrays sized for the largest set (`K_MAX = 35` trees; batches of `BATCH = 128`
leaves) and the `N > 16` paths, which hash the tree levels node by node with `thash_pair`.)

The message digest (hence the FORS indices), the parameter set and the address are public; the
secret seed, the seed state and every value derived from them (blocks, node values, signature
bytes) only enter the trace through their lengths. The tree indices that `fors_batch` and
`fors_pk_from_sig` keep in their `start`/`end`/`idx` arrays are public and are the same in the
two runs. The seed's three components, which the loops receive separately, are secret.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Fors

open slhdsa_leak

abbrev Blocks := Array (Array U8 64#usize) 128#usize
abbrev Vals (N : Usize) := Array (Array U8 N) 128#usize
abbrev Idx := Array U32 128#usize

theorem fors_batch_loop0_body {N : Usize} (sk sk' : Array U8 N) (i z : U32) (n : Usize)
    (a : slhdsa.address.Adrs) (b b' : Blocks) (s e : Idx) (j : Usize) (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_batch_loop0.body sk i z n a b s e j)
      (fors.fors_batch_loop0.body sk' i z n a b' s e j)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)
        (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)) := by
  unfold fors.fors_batch_loop0.body
  ct_steps
  all_goals first
    | (simp only [CFRel_cont_cont, CFRel_done_done, and_true]; heads_tac)
    | (simp only [CFRel_cont_cont, CFRel_done_done]; exact ⟨hb, rfl⟩)
    | simp_all

@[ct_rel] theorem fors_batch_loop0 {N : Usize} (sk sk' : Array U8 N) (i z : U32) (n : Usize)
    (a : slhdsa.address.Adrs) (b b' : Blocks) (s e : Idx) (j : Usize) (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_batch_loop0 sk i z n a b s e j) (fors.fors_batch_loop0 sk' i z n a b' s e j)
      (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) := by
  unfold fors.fors_batch_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨hb, rfl⟩
  rintro ⟨x, s1, e1, j1⟩ ⟨x', s1', e1', j1'⟩ ⟨hx, hI⟩
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ j1 = j1' := by simpa using hI
  exact fors_batch_loop0_body sk sk' i z n a x x' s1 e1 j1 hx

theorem fors_batch_loop1_body (t : U32) (n : Usize) (b b' : Blocks) (j : Usize)
    (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_batch_loop1.body t n b j) (fors.fors_batch_loop1.body t n b' j)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) (fun p q => HeadsEq p.val q.val)) := by
  unfold fors.fors_batch_loop1.body
  ct_steps
  all_goals first | (simp only [CFRel_cont_cont, CFRel_done_done, and_true]; heads_tac) | simp_all

@[ct_rel] theorem fors_batch_loop1 (t : U32) (n : Usize) (b b' : Blocks) (j : Usize)
    (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_batch_loop1 t n b j) (fors.fors_batch_loop1 t n b' j)
      (fun p q => HeadsEq p.val q.val) := by
  unfold fors.fors_batch_loop1
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨hb, rfl⟩
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ ⟨hx, (rfl : j1 = j1')⟩
  exact fors_batch_loop1_body t n x x' j1 hx

theorem fors_batch_loop2_body {N : Usize} (n : Usize) (b b' : Blocks) (v v' : Vals N) (j : Usize) :
    Rel (fors.fors_batch_loop2.body n b v j) (fors.fors_batch_loop2.body n b' v' j)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_batch_loop2.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_batch_loop2 {N : Usize} (n : Usize) (b b' : Blocks) (v v' : Vals N)
    (j : Usize) :
    Rel (fors.fors_batch_loop2 n b v j) (fors.fors_batch_loop2 n b' v' j) (fun _ _ => True) := by
  unfold fors.fors_batch_loop2
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_batch_loop2_body n b b' x x' j1

theorem fors_batch_loop3_loop0_body {N : Usize} (i z i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (v v' : Vals N) (lvl : U32) (cnt : Usize) (b b' : Blocks) (s e : Idx) (j : Usize)
    (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_batch_loop3_loop0.body i z i1 i2 i3 i4 i5 i6 v lvl cnt b s e j)
      (fors.fors_batch_loop3_loop0.body i z i1 i2 i3 i4 i5 i6 v' lvl cnt b' s e j)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)
        (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)) := by
  unfold fors.fors_batch_loop3_loop0.body
  ct_steps
  all_goals first
    | (simp only [CFRel_cont_cont, CFRel_done_done, and_true]; heads_tac)
    | (simp only [CFRel_cont_cont, CFRel_done_done]; exact ⟨hb, rfl⟩)
    | simp_all

@[ct_rel] theorem fors_batch_loop3_loop0 {N : Usize} (i z i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (b b' : Blocks) (s e : Idx) (v v' : Vals N) (lvl : U32) (cnt : Usize) (j : Usize)
    (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_batch_loop3_loop0 i z i1 i2 i3 i4 i5 i6 b s e v lvl cnt j)
      (fors.fors_batch_loop3_loop0 i z i1 i2 i3 i4 i5 i6 b' s e v' lvl cnt j)
      (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) := by
  unfold fors.fors_batch_loop3_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨hb, rfl⟩
  rintro ⟨x, s1, e1, j1⟩ ⟨x', s1', e1', j1'⟩ ⟨hx, hI⟩
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ j1 = j1' := by simpa using hI
  exact fors_batch_loop3_loop0_body i z i1 i2 i3 i4 i5 i6 v v' lvl cnt x x' s1 e1 j1 hx

theorem fors_batch_loop3_loop1_body {N : Usize} (b b' : Blocks) (cnt : Usize) (v v' : Vals N)
    (j : Usize) :
    Rel (fors.fors_batch_loop3_loop1.body b cnt v j) (fors.fors_batch_loop3_loop1.body b' cnt v' j)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_batch_loop3_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_batch_loop3_loop1 {N : Usize} (b b' : Blocks) (v v' : Vals N) (cnt : Usize)
    (j : Usize) :
    Rel (fors.fors_batch_loop3_loop1 b v cnt j) (fors.fors_batch_loop3_loop1 b' v' cnt j)
      (fun _ _ => True) := by
  unfold fors.fors_batch_loop3_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_batch_loop3_loop1_body b b' cnt x x' j1

theorem fors_batch_loop3_loop2_body {N : Usize} (i z : U32) (a a' : Array U8 N)
    (a1 a1' : Array U32 8#usize) (a2 a2' : Array U64 8#usize) (i1 : U32) (i2 : U64)
    (i3 i4 i5 i6 : U32) (lvl : U32) (cnt : Usize) (v v' : Vals N) (j : Usize) :
    Rel (fors.fors_batch_loop3_loop2.body i z a a1 a2 i1 i2 i3 i4 i5 i6 lvl cnt v j)
      (fors.fors_batch_loop3_loop2.body i z a' a1' a2' i1 i2 i3 i4 i5 i6 lvl cnt v' j)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_batch_loop3_loop2.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_batch_loop3_loop2 {N : Usize} (i z : U32) (a a' : Array U8 N)
    (a1 a1' : Array U32 8#usize) (a2 a2' : Array U64 8#usize) (i1 : U32) (i2 : U64)
    (i3 i4 i5 i6 : U32) (v v' : Vals N) (lvl : U32) (cnt : Usize) (j : Usize) :
    Rel (fors.fors_batch_loop3_loop2 i z a a1 a2 i1 i2 i3 i4 i5 i6 v lvl cnt j)
      (fors.fors_batch_loop3_loop2 i z a' a1' a2' i1 i2 i3 i4 i5 i6 v' lvl cnt j)
      (fun _ _ => True) := by
  unfold fors.fors_batch_loop3_loop2
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_batch_loop3_loop2_body i z a a' a1 a1' a2 a2' i1 i2 i3 i4 i5 i6 lvl cnt x x' j1

theorem fors_batch_loop3_body {N : Usize} (i z : U32) (a a' : Array U8 N)
    (a1 a1' : Array U32 8#usize) (a2 a2' : Array U64 8#usize) (i1 : U32) (i2 : U64)
    (i3 i4 i5 i6 : U32) (b b' : Blocks) (s e : Idx) (v v' : Vals N) (lvl : U32) (cnt : Usize)
    (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_batch_loop3.body i z a a1 a2 i1 i2 i3 i4 i5 i6 b s e v lvl cnt)
      (fors.fors_batch_loop3.body i z a' a1' a2' i1 i2 i3 i4 i5 i6 b' s e v' lvl cnt)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧
          p.2.2.2.2 = q.2.2.2.2)
        (fun _ _ => True)) := by
  unfold fors.fors_batch_loop3.body
  ct_steps
  all_goals first
    | (ct_facts; simp_all; done)
    | heads_tac
    | (simp only [CFRel_cont_cont]; refine ⟨by heads_tac, ?_⟩; ct_facts; simp_all)

@[ct_rel] theorem fors_batch_loop3 {N : Usize} (i z : U32) (a a' : Array U8 N)
    (a1 a1' : Array U32 8#usize) (a2 a2' : Array U64 8#usize) (i1 : U32) (i2 : U64)
    (i3 i4 i5 i6 : U32) (b b' : Blocks) (s e : Idx) (v v' : Vals N) (lvl : U32) (cnt : Usize)
    (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_batch_loop3 i z a a1 a2 i1 i2 i3 i4 i5 i6 b s e v lvl cnt)
      (fors.fors_batch_loop3 i z a' a1' a2' i1 i2 i3 i4 i5 i6 b' s e v' lvl cnt)
      (fun _ _ => True) := by
  unfold fors.fors_batch_loop3
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧
    p.2.2.2.2 = q.2.2.2.2) ?_ ⟨hb, rfl, rfl, rfl⟩
  rintro ⟨x, s1, e1, v1, l1, c1⟩ ⟨x', s1', e1', v1', l1', c1'⟩ ⟨hx, hI⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ l1 = l1' ∧ c1 = c1' := by simpa using hI
  exact fors_batch_loop3_body i z a a' a1 a1' a2 a2' i1 i2 i3 i4 i5 i6 x x' s1 e1 v1 v1' l1 c1 hx

@[ct_rel] theorem fors_batch {N : Usize} (sk sk' : Array U8 N) (i z : U32)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) :
    Rel (fors.fors_batch sk i z seed adrs) (fors.fors_batch sk' i z seed' adrs)
      (fun _ _ => True) := by
  unfold fors.fors_batch
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | heads_tac

/-- `fors_node`, by strong induction on the height. -/
@[ct_rel] theorem fors_node {N : Usize} (sk sk' : Array U8 N) (i z : U32)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) :
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

abbrev KBlocks := Array (Array U8 64#usize) 35#usize
abbrev KVals (N : Usize) := Array (Array U8 N) 35#usize
abbrev KIdx := Array U32 35#usize

theorem fors_pk_from_sig_loop0_body (N : Usize) (sig sig' : Slice U8) (adrs : slhdsa.address.Adrs)
    (a : U32) (k : Usize) (ind : alloc.vec.Vec U32) (b b' : KBlocks) (idx e : KIdx) (i : Usize)
    (h : sig.length = sig'.length) (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_pk_from_sig_loop0.body N sig adrs a k ind b idx e i)
      (fors.fors_pk_from_sig_loop0.body N sig' adrs a k ind b' idx e i)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)
        (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)) := by
  unfold fors.fors_pk_from_sig_loop0.body
  ct_steps
  all_goals first
    | (simp only [CFRel_cont_cont, CFRel_done_done, and_true]; heads_tac)
    | (simp only [CFRel_cont_cont, CFRel_done_done]; exact ⟨hb, rfl⟩)
    | simp_all

@[ct_rel] theorem fors_pk_from_sig_loop0 (N : Usize) (sig sig' : Slice U8)
    (adrs : slhdsa.address.Adrs) (a : U32) (k : Usize) (ind : alloc.vec.Vec U32) (b b' : KBlocks)
    (idx e : KIdx) (i : Usize) (h : sig.length = sig'.length) (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_pk_from_sig_loop0 N sig adrs a k ind b idx e i)
      (fors.fors_pk_from_sig_loop0 N sig' adrs a k ind b' idx e i)
      (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) := by
  unfold fors.fors_pk_from_sig_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨hb, rfl⟩
  rintro ⟨x, s1, e1, j1⟩ ⟨x', s1', e1', j1'⟩ ⟨hx, hI⟩
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ j1 = j1' := by simpa using hI
  exact fors_pk_from_sig_loop0_body N sig sig' adrs a k ind x x' s1 e1 j1 h hx

theorem fors_pk_from_sig_loop1_body {N : Usize} (k : Usize) (b b' : KBlocks) (v v' : KVals N)
    (i : Usize) :
    Rel (fors.fors_pk_from_sig_loop1.body k b v i) (fors.fors_pk_from_sig_loop1.body k b' v' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_pk_from_sig_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_pk_from_sig_loop1 {N : Usize} (k : Usize) (b b' : KBlocks) (v v' : KVals N)
    (i : Usize) :
    Rel (fors.fors_pk_from_sig_loop1 k b v i) (fors.fors_pk_from_sig_loop1 k b' v' i)
      (fun _ _ => True) := by
  unfold fors.fors_pk_from_sig_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_pk_from_sig_loop1_body k b b' x x' j1

theorem fors_pk_from_sig_loop2_loop0_body {N : Usize} (sig sig' : Slice U8)
    (adrs : slhdsa.address.Adrs) (a : U32) (k : Usize) (v v' : KVals N) (hh : U32)
    (b b' : KBlocks) (idx e : KIdx) (i : Usize)
    (h : sig.length = sig'.length) (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_pk_from_sig_loop2_loop0.body sig adrs a k v hh b idx e i)
      (fors.fors_pk_from_sig_loop2_loop0.body sig' adrs a k v' hh b' idx e i)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)
        (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2)) := by
  unfold fors.fors_pk_from_sig_loop2_loop0.body
  ct_steps_h
  all_goals first
    | (simp only [CFRel_cont_cont, CFRel_done_done, and_true]; heads_tac)
    | (simp only [CFRel_cont_cont, CFRel_done_done]; exact ⟨hb, rfl⟩)
    | heads_tac
    | simp_all

@[ct_rel] theorem fors_pk_from_sig_loop2_loop0 {N : Usize} (sig sig' : Slice U8)
    (adrs : slhdsa.address.Adrs) (a : U32) (k : Usize) (b b' : KBlocks) (idx e : KIdx)
    (v v' : KVals N) (hh : U32) (i : Usize)
    (h : sig.length = sig'.length) (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_pk_from_sig_loop2_loop0 sig adrs a k b idx e v hh i)
      (fors.fors_pk_from_sig_loop2_loop0 sig' adrs a k b' idx e v' hh i)
      (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) := by
  unfold fors.fors_pk_from_sig_loop2_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨hb, rfl⟩
  rintro ⟨x, s1, e1, j1⟩ ⟨x', s1', e1', j1'⟩ ⟨hx, hI⟩
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ j1 = j1' := by simpa using hI
  exact fors_pk_from_sig_loop2_loop0_body sig sig' adrs a k v v' hh x x' s1 e1 j1 h hx

theorem fors_pk_from_sig_loop2_loop1_body {N : Usize} (k : Usize) (b b' : KBlocks)
    (v v' : KVals N) (i : Usize) :
    Rel (fors.fors_pk_from_sig_loop2_loop1.body k b v i)
      (fors.fors_pk_from_sig_loop2_loop1.body k b' v' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold fors.fors_pk_from_sig_loop2_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_pk_from_sig_loop2_loop1 {N : Usize} (k : Usize) (b b' : KBlocks)
    (v v' : KVals N) (i : Usize) :
    Rel (fors.fors_pk_from_sig_loop2_loop1 k b v i) (fors.fors_pk_from_sig_loop2_loop1 k b' v' i)
      (fun _ _ => True) := by
  unfold fors.fors_pk_from_sig_loop2_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j1⟩ ⟨x', j1'⟩ (rfl : j1 = j1')
  exact fors_pk_from_sig_loop2_loop1_body k b b' x x' j1

theorem fors_pk_from_sig_loop2_loop2_body {N : Usize} (sig sig' : Slice U8) (a a' : Array U8 N)
    (a1 a1' : Array U32 8#usize) (a2 a2' : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
    (a3 : U32) (k : Usize) (hh : U32) (idx : KIdx) (v v' : KVals N) (i : Usize)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig_loop2_loop2.body sig a a1 a2 adrs a3 k hh idx v i)
      (fors.fors_pk_from_sig_loop2_loop2.body sig' a' a1' a2' adrs a3 k hh idx v' i)
      (CFRel (fun p q => p.1 = q.1 ∧ p.2.2 = q.2.2) (fun p q => p.1 = q.1)) := by
  unfold fors.fors_pk_from_sig_loop2_loop2.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem fors_pk_from_sig_loop2_loop2 {N : Usize} (sig sig' : Slice U8)
    (a a' : Array U8 N) (a1 a1' : Array U32 8#usize) (a2 a2' : Array U64 8#usize)
    (adrs : slhdsa.address.Adrs) (a3 : U32) (k : Usize) (idx : KIdx) (v v' : KVals N) (hh : U32)
    (i : Usize) (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig_loop2_loop2 sig a a1 a2 adrs a3 k idx v hh i)
      (fors.fors_pk_from_sig_loop2_loop2 sig' a' a1' a2' adrs a3 k idx v' hh i)
      (fun p q => p.1 = q.1) := by
  unfold fors.fors_pk_from_sig_loop2_loop2
  refine Rel.loop (fun p q => p.1 = q.1 ∧ p.2.2 = q.2.2) ?_ ⟨rfl, rfl⟩
  rintro ⟨x, v1, j1⟩ ⟨x', v1', j1'⟩ ⟨(rfl : x = x'), (rfl : j1 = j1')⟩
  exact fors_pk_from_sig_loop2_loop2_body sig sig' a a' a1 a1' a2 a2' adrs a3 k hh x v1 v1' j1 h

theorem fors_pk_from_sig_loop2_body {N : Usize} (sig sig' : Slice U8) (a a' : Array U8 N)
    (a1 a1' : Array U32 8#usize) (a2 a2' : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
    (a3 : U32) (k : Usize) (b b' : KBlocks) (idx e : KIdx) (v v' : KVals N) (hh : U32)
    (h : sig.length = sig'.length) (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_pk_from_sig_loop2.body sig a a1 a2 adrs a3 k b idx e v hh)
      (fors.fors_pk_from_sig_loop2.body sig' a' a1' a2' adrs a3 k b' idx e v' hh)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧
          p.2.2.2.2 = q.2.2.2.2)
        (fun _ _ => True)) := by
  unfold fors.fors_pk_from_sig_loop2.body
  ct_steps
  all_goals first
    | (ct_facts; simp_all; done)
    | heads_tac
    | (simp only [CFRel_cont_cont]; refine ⟨by heads_tac, ?_⟩; ct_facts; simp_all)

@[ct_rel] theorem fors_pk_from_sig_loop2 {N : Usize} (sig sig' : Slice U8) (a a' : Array U8 N)
    (a1 a1' : Array U32 8#usize) (a2 a2' : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
    (a3 : U32) (k : Usize) (b b' : KBlocks) (idx e : KIdx) (v v' : KVals N) (hh : U32)
    (h : sig.length = sig'.length) (hb : HeadsEq b.val b'.val) :
    Rel (fors.fors_pk_from_sig_loop2 sig a a1 a2 adrs a3 k b idx e v hh)
      (fors.fors_pk_from_sig_loop2 sig' a' a1' a2' adrs a3 k b' idx e v' hh) (fun _ _ => True) := by
  unfold fors.fors_pk_from_sig_loop2
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧
    p.2.2.2.2 = q.2.2.2.2) ?_ ⟨hb, rfl, rfl, rfl⟩
  rintro ⟨x, s1, e1, v1, k1⟩ ⟨x', s1', e1', v1', k1'⟩ ⟨hx, hI⟩
  obtain ⟨rfl, rfl, rfl⟩ : s1 = s1' ∧ e1 = e1' ∧ k1 = k1' := by simpa using hI
  exact fors_pk_from_sig_loop2_body sig sig' a a' a1 a1' a2 a2' adrs a3 k x x' s1 e1 v1 v1' k1 h hx

theorem fors_pk_from_sig_loop3_body {N : Usize} (k : Usize) (v v' : KVals N)
    (r r' : alloc.vec.Vec U8) (i : Usize) (h : r.length = r'.length) :
    Rel (fors.fors_pk_from_sig_loop3.body k v r i) (fors.fors_pk_from_sig_loop3.body k v' r' i)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold fors.fors_pk_from_sig_loop3.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_pk_from_sig_loop3 {N : Usize} (k : Usize) (v v' : KVals N)
    (r r' : alloc.vec.Vec U8) (i : Usize) (h : r.length = r'.length) :
    Rel (fors.fors_pk_from_sig_loop3 k v r i) (fors.fors_pk_from_sig_loop3 k v' r' i)
      (fun p q => p.length = q.length) := by
  unfold fors.fors_pk_from_sig_loop3
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, j⟩ ⟨x', j'⟩ ⟨hx, (rfl : j = j')⟩
  exact fors_pk_from_sig_loop3_body k v v' x x' j hx

/-- `fors_pkFromSig`: the digest (indices) is public; the signature is secret (length only). -/
@[ct_rel] theorem fors_pk_from_sig {N : Usize} (p : slhdsa.params.Params) (sig sig' : Slice U8)
    (md : Slice U8) (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_pk_from_sig p sig md seed adrs) (fors.fors_pk_from_sig p sig' md seed' adrs)
      (fun _ _ => True) := by
  unfold fors.fors_pk_from_sig
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | heads_tac

@[ct_rel] theorem fors_sk_gen {N : Usize} (sk sk' : Array U8 N) (seed seed' : slhdsa.hash.Seed N)
    (adrs : slhdsa.address.Adrs) (idx : U32) :
    Rel (fors.fors_sk_gen sk seed adrs idx) (fors.fors_sk_gen sk' seed' adrs idx)
      (fun _ _ => True) := by
  unfold fors.fors_sk_gen
  ct_steps

theorem fors_sign_loop0_loop0_body {N : Usize} (sk sk' : Array U8 N)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) (a i idx : U32)
    (sig sig' : alloc.vec.Vec U8) (j : U32) (h : sig.length = sig'.length) :
    Rel (fors.fors_sign_loop0_loop0.body sk seed adrs a i idx sig j)
      (fors.fors_sign_loop0_loop0.body sk' seed' adrs a i idx sig' j)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold fors.fors_sign_loop0_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_sign_loop0_loop0 {N : Usize} (sk sk' : Array U8 N)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) (a : U32)
    (sig sig' : alloc.vec.Vec U8) (i idx j : U32) (h : sig.length = sig'.length) :
    Rel (fors.fors_sign_loop0_loop0 sk seed adrs a sig i idx j)
      (fors.fors_sign_loop0_loop0 sk' seed' adrs a sig' i idx j)
      (fun p q => p.length = q.length) := by
  unfold fors.fors_sign_loop0_loop0
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact fors_sign_loop0_loop0_body sk sk' seed seed' adrs a i idx x x' k hx

theorem fors_sign_loop0_body {N : Usize} (i : U32) (sk sk' : Array U8 N)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) (a : U32)
    (ind : alloc.vec.Vec U32) (sig sig' : alloc.vec.Vec U8) (i1 : U32)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_sign_loop0.body i sk seed adrs a ind sig i1)
      (fors.fors_sign_loop0.body i sk' seed' adrs a ind sig' i1)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold fors.fors_sign_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_sign_loop0 {N : Usize} (i : U32) (sk sk' : Array U8 N)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) (a : U32)
    (ind : alloc.vec.Vec U32) (sig sig' : alloc.vec.Vec U8) (i1 : U32)
    (h : sig.length = sig'.length) :
    Rel (fors.fors_sign_loop0 i sk seed adrs a ind sig i1)
      (fors.fors_sign_loop0 i sk' seed' adrs a ind sig' i1)
      (fun p q => p.length = q.length) := by
  unfold fors.fors_sign_loop0
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact fors_sign_loop0_body i sk sk' seed seed' adrs a ind x x' k hx

/-- `fors_sign`: the digest is public (its indices select the revealed leaves and the
authentication paths). -/
@[ct_rel] theorem fors_sign {N : Usize} (p : slhdsa.params.Params) (md : Slice U8)
    (sk sk' : Array U8 N) (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) :
    Rel (fors.fors_sign p md sk seed adrs) (fors.fors_sign p md sk' seed' adrs)
      (fun p q => p.length = q.length) := by
  unfold fors.fors_sign
  ct_steps

end Ct.Fors
