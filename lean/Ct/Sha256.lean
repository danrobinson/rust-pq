import Ct.CompressTop

/-!
# Constant time: the SHA-256 layer

For every function of `rust/src/sha256.rs` (as translated), two runs on data of the same
lengths, with the same offsets and other public arguments, have the same trace; their results
are again of equal length (arrays: by their type; vectors: stated). Secret buffers enter only
through their lengths: a caller needs nothing but length equality for them.

The schedule and the portable compression are in `Ct/Sha256Core.lean`, `sha256::compress`
(which depends on the build) in `Ct/CompressTop.lean`.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Sha256

open slhdsa_leak

theorem digest_loop_body (state state' : Array U32 8#usize) (out out' : Array U8 32#usize)
    (i : Usize) :
    Rel (sha256.digest_loop.body state out i) (sha256.digest_loop.body state' out' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold sha256.digest_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem digest_loop (state state' : Array U32 8#usize) (out out' : Array U8 32#usize)
    (i : Usize) :
    Rel (sha256.digest_loop state out i) (sha256.digest_loop state' out' i) (fun _ _ => True) := by
  unfold sha256.digest_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨o, i⟩ ⟨o', i'⟩ (rfl : i = i')
  exact digest_loop_body state state' o o' i

@[ct_rel] theorem digest (state state' : Array U32 8#usize) :
    Rel (sha256.digest state) (sha256.digest state') (fun _ _ => True) := by
  unfold sha256.digest
  ct_steps

theorem pad_loop_body (p p' : alloc.vec.Vec U8) (h : p.length = p'.length) :
    Rel (sha256.pad_loop.body p) (sha256.pad_loop.body p')
      (CFRel (fun q q' => q.length = q'.length) (fun q q' => q.length = q'.length)) := by
  unfold sha256.pad_loop.body
  simp only [(Facts.vec_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem pad_loop (p p' : alloc.vec.Vec U8) (h : p.length = p'.length) :
    Rel (sha256.pad_loop p) (sha256.pad_loop p') (fun q q' => q.length = q'.length) := by
  unfold sha256.pad_loop
  exact Rel.loop (fun q q' => q.length = q'.length) (fun q q' hq => pad_loop_body q q' hq) h

@[ct_rel] theorem pad (msg msg' : Slice U8) (pre : Usize) (h : msg.length = msg'.length) :
    Rel (sha256.pad msg pre) (sha256.pad msg' pre) (fun q q' => q.length = q'.length) := by
  unfold sha256.pad
  simp only [(Facts.slice_len_congr h).symm]
  ct_steps
  ct_facts; simp_all

theorem sha256_from_loop0_body (msg msg' : Slice U8) (st st' : Array U32 8#usize) (off : Usize)
    (h : msg.length = msg'.length) :
    Rel (sha256.sha256_from_loop0.body msg st off) (sha256.sha256_from_loop0.body msg' st' off)
      (CFRel (fun p q => p.2 = q.2) (fun p q => p.2 = q.2)) := by
  unfold sha256.sha256_from_loop0.body
  simp only [(Facts.slice_len_congr h).symm]
  ct_steps
  all_goals simp_all

@[ct_rel] theorem sha256_from_loop0 (msg msg' : Slice U8) (st st' : Array U32 8#usize)
    (off : Usize) (h : msg.length = msg'.length) :
    Rel (sha256.sha256_from_loop0 msg st off) (sha256.sha256_from_loop0 msg' st' off)
      (fun p q => p.2 = q.2) := by
  unfold sha256.sha256_from_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨s, o⟩ ⟨s', o'⟩ (rfl : o = o')
  exact sha256_from_loop0_body msg msg' s s' o h

theorem sha256_from_loop1_body (p p' : alloc.vec.Vec U8) (st st' : Array U32 8#usize)
    (o : Usize) (h : p.length = p'.length) :
    Rel (sha256.sha256_from_loop1.body p st o) (sha256.sha256_from_loop1.body p' st' o)
      (CFRel (fun a b => a.2 = b.2) (fun _ _ => True)) := by
  unfold sha256.sha256_from_loop1.body
  simp only [(Facts.vec_len_congr h).symm]
  ct_steps
  all_goals simp_all

@[ct_rel] theorem sha256_from_loop1 (st st' : Array U32 8#usize) (p p' : alloc.vec.Vec U8)
    (o : Usize) (h : p.length = p'.length) :
    Rel (sha256.sha256_from_loop1 st p o) (sha256.sha256_from_loop1 st' p' o)
      (fun _ _ => True) := by
  unfold sha256.sha256_from_loop1
  refine Rel.loop (fun a b => a.2 = b.2) ?_ rfl
  rintro ⟨s, o⟩ ⟨s', o'⟩ (rfl : o = o')
  exact sha256_from_loop1_body p p' s s' o h

@[ct_rel] theorem sha256_from (state state' : Array U32 8#usize) (pre : Usize)
    (msg msg' : Slice U8) (h : msg.length = msg'.length) :
    Rel (sha256.sha256_from state pre msg) (sha256.sha256_from state' pre msg')
      (fun _ _ => True) := by
  unfold sha256.sha256_from
  simp only [(Facts.slice_len_congr h).symm]
  ct_steps

@[ct_rel] theorem sha256 (msg msg' : Slice U8) (h : msg.length = msg'.length) :
    Rel (sha256.sha256 msg) (sha256.sha256 msg') (fun _ _ => True) := by
  unfold sha256.sha256
  ct_steps

theorem hmac_sha256_loop_body (key key' : Slice U8) (inner inner' outer outer' : alloc.vec.Vec U8)
    (i : Usize) (hk : key.length = key'.length) (hi : inner.length = inner'.length)
    (ho : outer.length = outer'.length) :
    Rel (sha256.hmac_sha256_loop.body key inner outer i)
      (sha256.hmac_sha256_loop.body key' inner' outer' i)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2.1.length = q.2.1.length ∧ p.2.2 = q.2.2)
        (fun p q => p.1.length = q.1.length ∧ p.2.length = q.2.length)) := by
  unfold sha256.hmac_sha256_loop.body
  simp only [(Facts.slice_len_congr hk).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem hmac_sha256_loop (key key' : Slice U8) (inner inner' outer outer' : alloc.vec.Vec U8)
    (i : Usize) (hk : key.length = key'.length) (hi : inner.length = inner'.length)
    (ho : outer.length = outer'.length) :
    Rel (sha256.hmac_sha256_loop key inner outer i) (sha256.hmac_sha256_loop key' inner' outer' i)
      (fun p q => p.1.length = q.1.length ∧ p.2.length = q.2.length) := by
  unfold sha256.hmac_sha256_loop
  refine Rel.loop
    (fun p q => p.1.length = q.1.length ∧ p.2.1.length = q.2.1.length ∧ p.2.2 = q.2.2)
    ?_ ⟨hi, ho, rfl⟩
  rintro ⟨a, b, j⟩ ⟨a', b', j'⟩ ⟨ha, hb, (rfl : j = j')⟩
  exact hmac_sha256_loop_body key key' a a' b b' j hk ha hb

@[ct_rel] theorem hmac_sha256 (key key' msg msg' : Slice U8) (hk : key.length = key'.length)
    (hm : msg.length = msg'.length) :
    Rel (sha256.hmac_sha256 key msg) (sha256.hmac_sha256 key' msg') (fun _ _ => True) := by
  unfold sha256.hmac_sha256
  ct_steps

end Ct.Sha256
