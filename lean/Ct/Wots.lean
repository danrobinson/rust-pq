import Ct.ChainTop

/-!
# Constant time: `util.rs` and `wots.rs`

The WOTS+ message (the value signed, hence its base-`w` digits, which decide the chain lengths)
is public; the secret seed, the seed state and the blocks are secret.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Wots

open slhdsa_leak

/-! ## `util.rs` -/

@[ct_rel] theorem block (s s' : Slice U8) (i : Usize) (h : s.length = s'.length) :
    Rel (util.block s i) (util.block s' i) (fun _ _ => True) := by
  unfold util.block
  ct_steps
  all_goals (ct_facts; simp_all)

theorem to_int_loop_body (x x' : Slice U8) (t t' : U64) (i : Usize)
    (h : x.length = x'.length) :
    Rel (util.to_int_loop.body x t i) (util.to_int_loop.body x' t' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold util.to_int_loop.body
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals simp_all

@[ct_rel] theorem to_int_loop (x x' : Slice U8) (t t' : U64) (i : Usize)
    (h : x.length = x'.length) :
    Rel (util.to_int_loop x t i) (util.to_int_loop x' t' i) (fun _ _ => True) := by
  unfold util.to_int_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨a, j⟩ ⟨a', j'⟩ (rfl : j = j')
  exact to_int_loop_body x x' a a' j h

@[ct_rel] theorem to_int (x x' : Slice U8) (h : x.length = x'.length) :
    Rel (util.to_int x) (util.to_int x') (fun _ _ => True) := by
  unfold util.to_int
  exact to_int_loop x x' _ _ _ h

theorem base_2b_loop0_loop0_body (x x' : Slice U8) (b : U32) (input : Usize) (bits : U32)
    (t t' : U32) (h : x.length = x'.length) :
    Rel (util.base_2b_loop0_loop0.body x b input bits t)
      (util.base_2b_loop0_loop0.body x' b input bits t')
      (CFRel (fun p q => p.1 = q.1 ∧ p.2.1 = q.2.1) (fun p q => p.1 = q.1 ∧ p.2.1 = q.2.1)) := by
  unfold util.base_2b_loop0_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem base_2b_loop0_loop0 (x x' : Slice U8) (b : U32) (input : Usize) (bits : U32)
    (t t' : U32) (h : x.length = x'.length) :
    Rel (util.base_2b_loop0_loop0 x b input bits t) (util.base_2b_loop0_loop0 x' b input bits t')
      (fun p q => p.1 = q.1 ∧ p.2.1 = q.2.1) := by
  unfold util.base_2b_loop0_loop0
  refine Rel.loop (fun p q => p.1 = q.1 ∧ p.2.1 = q.2.1) ?_ ⟨rfl, rfl⟩
  rintro ⟨a, c, d⟩ ⟨a', c', d'⟩ ⟨(rfl : a = a'), (rfl : c = c')⟩
  exact base_2b_loop0_loop0_body x x' b a c d d' h

theorem base_2b_loop0_body (x x' : Slice U8) (b : U32) (n : Usize) (input : Usize) (bits : U32)
    (t t' : U32) (out out' : alloc.vec.Vec U32) (i : Usize) (h : x.length = x'.length)
    (ho : out.length = out'.length) :
    Rel (util.base_2b_loop0.body x b n input bits t out i)
      (util.base_2b_loop0.body x' b n input bits t' out' i)
      (CFRel (fun p q => p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.2.1.length = q.2.2.2.1.length ∧
          p.2.2.2.2 = q.2.2.2.2)
        (fun p q => p.length = q.length)) := by
  unfold util.base_2b_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem base_2b_loop0 (x x' : Slice U8) (b : U32) (n : Usize) (input : Usize)
    (bits : U32) (t t' : U32) (out out' : alloc.vec.Vec U32) (i : Usize)
    (h : x.length = x'.length) (ho : out.length = out'.length) :
    Rel (util.base_2b_loop0 x b n input bits t out i) (util.base_2b_loop0 x' b n input bits t' out' i)
      (fun p q => p.length = q.length) := by
  unfold util.base_2b_loop0
  refine Rel.loop (fun p q => p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.2.1.length = q.2.2.2.1.length ∧
          p.2.2.2.2 = q.2.2.2.2) ?_ ⟨rfl, rfl, ho, rfl⟩
  rintro ⟨a, c, d, o, j⟩ ⟨a', c', d', o', j'⟩ ⟨(rfl : a = a'), (rfl : c = c'), hoo, (rfl : j = j')⟩
  exact base_2b_loop0_body x x' b n a c d d' o o' j h hoo

/-- `base_2b`: the trace depends on the length of the input only (the values decide the digits,
not the accesses). -/
@[ct_rel] theorem base_2b (x x' : Slice U8) (b : U32) (n : Usize) (h : x.length = x'.length) :
    Rel (util.base_2b x b n) (util.base_2b x' b n) (fun p q => p.length = q.length) := by
  unfold util.base_2b
  exact base_2b_loop0 x x' b n _ _ _ _ _ _ _ h rfl

/-! ## `wots.rs` -/

theorem wots_digits_loop_body (msg msg' : alloc.vec.Vec U32) (c c' : U32) (i : Usize)
    (h : msg.length = msg'.length) :
    Rel (wots.wots_digits_loop.body msg c i) (wots.wots_digits_loop.body msg' c' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold wots.wots_digits_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem wots_digits_loop (msg msg' : alloc.vec.Vec U32) (c c' : U32) (i : Usize)
    (h : msg.length = msg'.length) :
    Rel (wots.wots_digits_loop msg c i) (wots.wots_digits_loop msg' c' i) (fun _ _ => True) := by
  unfold wots.wots_digits_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨a, j⟩ ⟨a', j'⟩ (rfl : j = j')
  exact wots_digits_loop_body msg msg' a a' j h

/-- The digits' trace does not depend on the message. -/
@[ct_rel] theorem wots_digits (m m' : Array U8 16#usize) :
    Rel (wots.wots_digits m) (wots.wots_digits m') (fun p q => p.length = q.length) := by
  unfold wots.wots_digits
  ct_steps
  all_goals (ct_facts; simp_all)

/-! The block arrays below are secret except for their heads (`Ct/Heads.lean`), which are
built from the public address and are the same in the two runs: the precondition of
`chain_blocks`. -/

theorem sk_blocks_loop0_body (sk sk' : Array U8 16#usize) (a : slhdsa.address.Adrs)
    (b b' : Array (Array U8 64#usize) 35#usize) (i : Usize) (h : HeadsEq b.val b'.val) :
    Rel (wots.sk_blocks_loop0.body sk a b i) (wots.sk_blocks_loop0.body sk' a b' i)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) (fun p q => HeadsEq p.val q.val)) := by
  unfold wots.sk_blocks_loop0.body
  ct_steps
  all_goals first | (simp only [CFRel_cont_cont, CFRel_done_done, and_true]; heads_tac) | simp_all

@[ct_rel] theorem sk_blocks_loop0 (sk sk' : Array U8 16#usize) (a : slhdsa.address.Adrs)
    (b b' : Array (Array U8 64#usize) 35#usize) (i : Usize) (h : HeadsEq b.val b'.val) :
    Rel (wots.sk_blocks_loop0 sk a b i) (wots.sk_blocks_loop0 sk' a b' i)
      (fun p q => HeadsEq p.val q.val) := by
  unfold wots.sk_blocks_loop0
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, j⟩ ⟨x', j'⟩ ⟨hx, (rfl : j = j')⟩
  exact sk_blocks_loop0_body sk sk' a x x' j hx

theorem sk_blocks_loop1_body (t : U32) (b b' : Array (Array U8 64#usize) 35#usize) (i : Usize)
    (h : HeadsEq b.val b'.val) :
    Rel (wots.sk_blocks_loop1.body t b i) (wots.sk_blocks_loop1.body t b' i)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) (fun p q => HeadsEq p.val q.val)) := by
  unfold wots.sk_blocks_loop1.body
  ct_steps
  all_goals first | (simp only [CFRel_cont_cont, CFRel_done_done, and_true]; heads_tac) | simp_all

@[ct_rel] theorem sk_blocks_loop1 (t : U32) (b b' : Array (Array U8 64#usize) 35#usize)
    (i : Usize) (h : HeadsEq b.val b'.val) :
    Rel (wots.sk_blocks_loop1 t b i) (wots.sk_blocks_loop1 t b' i)
      (fun p q => HeadsEq p.val q.val) := by
  unfold wots.sk_blocks_loop1
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, j⟩ ⟨x', j'⟩ ⟨hx, (rfl : j = j')⟩
  exact sk_blocks_loop1_body t x x' j hx

@[ct_rel] theorem sk_blocks (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) :
    Rel (wots.sk_blocks sk seed adrs) (wots.sk_blocks sk' seed' adrs)
      (fun p q => HeadsEq p.val q.val) := by
  unfold wots.sk_blocks
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | heads_tac

/-- `wots_pkGen`: nothing secret (seed, `PK.seed` state) reaches the trace. -/
@[ct_rel] theorem wots_pk_gen (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (adrs : slhdsa.address.Adrs) :
    Rel (wots.wots_pk_gen sk seed adrs) (wots.wots_pk_gen sk' seed' adrs) (fun _ _ => True) := by
  unfold wots.wots_pk_gen
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | heads_tac

theorem wots_pk_from_sig_loop_body (sig sig' : Slice U8) (a : slhdsa.address.Adrs)
    (b b' : Array (Array U8 64#usize) 35#usize) (i : Usize) (h : sig.length = sig'.length)
    (hb : HeadsEq b.val b'.val) :
    Rel (wots.wots_pk_from_sig_loop.body sig a b i) (wots.wots_pk_from_sig_loop.body sig' a b' i)
      (CFRel (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) (fun p q => HeadsEq p.val q.val)) := by
  unfold wots.wots_pk_from_sig_loop.body
  ct_steps
  all_goals first | (simp only [CFRel_cont_cont, CFRel_done_done, and_true]; heads_tac) | simp_all

@[ct_rel] theorem wots_pk_from_sig_loop (sig sig' : Slice U8) (a : slhdsa.address.Adrs)
    (b b' : Array (Array U8 64#usize) 35#usize) (i : Usize) (h : sig.length = sig'.length)
    (hb : HeadsEq b.val b'.val) :
    Rel (wots.wots_pk_from_sig_loop sig a b i) (wots.wots_pk_from_sig_loop sig' a b' i)
      (fun p q => HeadsEq p.val q.val) := by
  unfold wots.wots_pk_from_sig_loop
  refine Rel.loop (fun p q => HeadsEq p.1.val q.1.val ∧ p.2 = q.2) ?_ ⟨hb, rfl⟩
  rintro ⟨x, j⟩ ⟨x', j'⟩ ⟨hx, (rfl : j = j')⟩
  exact wots_pk_from_sig_loop_body sig sig' a x x' j h hx

/-- `wots_pkFromSig`: the message (its digits start the chains) is public; the signature
values only matter through their length. -/
@[ct_rel] theorem wots_pk_from_sig (sig sig' : Slice U8) (m : Array U8 16#usize)
    (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs) (h : sig.length = sig'.length) :
    Rel (wots.wots_pk_from_sig sig m seed adrs) (wots.wots_pk_from_sig sig' m seed' adrs)
      (fun _ _ => True) := by
  unfold wots.wots_pk_from_sig
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | heads_tac

theorem wots_sign_loop_body (b b' : Array (Array U8 64#usize) 35#usize)
    (sig sig' : alloc.vec.Vec U8) (i : Usize) (h : sig.length = sig'.length) :
    Rel (wots.wots_sign_loop.body b sig i) (wots.wots_sign_loop.body b' sig' i)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold wots.wots_sign_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem wots_sign_loop (b b' : Array (Array U8 64#usize) 35#usize)
    (sig sig' : alloc.vec.Vec U8) (i : Usize) (h : sig.length = sig'.length) :
    Rel (wots.wots_sign_loop b sig i) (wots.wots_sign_loop b' sig' i)
      (fun p q => p.length = q.length) := by
  unfold wots.wots_sign_loop
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, j⟩ ⟨x', j'⟩ ⟨hx, (rfl : j = j')⟩
  exact wots_sign_loop_body b b' x x' j hx

/-- `wots_sign`: the message is public (its digits are the chain lengths). -/
@[ct_rel] theorem wots_sign (m : Array U8 16#usize) (sk sk' : Array U8 16#usize)
    (seed seed' : slhdsa.hash.Seed) (adrs : slhdsa.address.Adrs) :
    Rel (wots.wots_sign m sk seed adrs) (wots.wots_sign m sk' seed' adrs)
      (fun p q => p.length = q.length) := by
  unfold wots.wots_sign
  ct_steps
  all_goals first | (ct_facts; simp_all; done) | heads_tac

end Ct.Wots
