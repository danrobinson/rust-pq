import Ct.Sha256

/-!
# Constant time: the SHA-512 layer

`sha512.rs` is SHA-256's code on 64-bit words, 80 rounds, 128-byte blocks and a 128-bit length
field; the lemmas are those of `Ct/Sha256Core.lean` and `Ct/Sha256.lean`. For every function, two
runs on data of the same lengths, with the same offsets and other public arguments, have the
same trace; vectors keep equal lengths. Secret buffers enter only through their lengths.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Sha512

open slhdsa_leak

@[ct_rel] theorem load_be64 (data data' : Slice U8) (off : Usize)
    (h : data.length = data'.length) :
    Rel (sha512.load_be64 data off) (sha512.load_be64 data' off) (fun _ _ => True) := by
  unfold sha512.load_be64
  ct_steps

theorem schedule_loop0_body (data data' : Slice U8) (off : Usize) (w w' : Array U64 80#usize)
    (i : Usize) (h : data.length = data'.length) :
    Rel (sha512.schedule_loop0.body data off w i) (sha512.schedule_loop0.body data' off w' i)
      (CFRel (fun p q => p.2 = q.2) (fun p q => p.2 = q.2)) := by
  unfold sha512.schedule_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem schedule_loop0 (data data' : Slice U8) (off : Usize)
    (w w' : Array U64 80#usize) (i : Usize) (h : data.length = data'.length) :
    Rel (sha512.schedule_loop0 data off w i) (sha512.schedule_loop0 data' off w' i)
      (fun p q => p.2 = q.2) := by
  unfold sha512.schedule_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨w1, i1⟩ ⟨w1', i1'⟩ (rfl : i1 = i1')
  exact schedule_loop0_body data data' off w1 w1' i1 h

theorem schedule_loop1_body (w w' : Array U64 80#usize) (i : Usize) :
    Rel (sha512.schedule_loop1.body w i) (sha512.schedule_loop1.body w' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold sha512.schedule_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem schedule_loop1 (w w' : Array U64 80#usize) (i : Usize) :
    Rel (sha512.schedule_loop1 w i) (sha512.schedule_loop1 w' i) (fun _ _ => True) := by
  unfold sha512.schedule_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨w1, i1⟩ ⟨w1', i1'⟩ (rfl : i1 = i1')
  exact schedule_loop1_body w1 w1' i1

@[ct_rel] theorem schedule (data data' : Slice U8) (off : Usize)
    (h : data.length = data'.length) :
    Rel (sha512.schedule data off) (sha512.schedule data' off) (fun _ _ => True) := by
  unfold sha512.schedule
  ct_steps

theorem compress_portable_loop_body (w w' : Array U64 80#usize)
    (a b c d e f g h a' b' c' d' e' f' g' h' : U64) (i : Usize) :
    Rel (sha512.compress_portable_loop.body w a b c d e f g h i)
      (sha512.compress_portable_loop.body w' a' b' c' d' e' f' g' h' i)
      (CFRel (fun p q => p.2.2.2.2.2.2.2.2 = q.2.2.2.2.2.2.2.2) (fun _ _ => True)) := by
  unfold sha512.compress_portable_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem compress_portable_loop (w w' : Array U64 80#usize)
    (a b c d e f g h a' b' c' d' e' f' g' h' : U64) (i : Usize) :
    Rel (sha512.compress_portable_loop w a b c d e f g h i)
      (sha512.compress_portable_loop w' a' b' c' d' e' f' g' h' i) (fun _ _ => True) := by
  unfold sha512.compress_portable_loop
  refine Rel.loop (fun p q => p.2.2.2.2.2.2.2.2 = q.2.2.2.2.2.2.2.2) ?_ rfl
  rintro ⟨a, b, c, d, e, f, g, h, i⟩ ⟨a', b', c', d', e', f', g', h', i'⟩ (rfl : i = i')
  exact compress_portable_loop_body w w' a b c d e f g h a' b' c' d' e' f' g' h' i

@[ct_rel] theorem compress_portable (state state' : Array U64 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha512.compress_portable state data off) (sha512.compress_portable state' data' off)
      (fun _ _ => True) := by
  unfold sha512.compress_portable
  ct_steps

@[ct_rel] theorem compress (state state' : Array U64 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha512.compress state data off) (sha512.compress state' data' off)
      (fun _ _ => True) := by
  unfold sha512.compress
  exact compress_portable state state' data data' off h

theorem digest_loop_body (state state' : Array U64 8#usize) (out out' : Array U8 64#usize)
    (i : Usize) :
    Rel (sha512.digest_loop.body state out i) (sha512.digest_loop.body state' out' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold sha512.digest_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem digest_loop (state state' : Array U64 8#usize) (out out' : Array U8 64#usize)
    (i : Usize) :
    Rel (sha512.digest_loop state out i) (sha512.digest_loop state' out' i) (fun _ _ => True) := by
  unfold sha512.digest_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨o, i⟩ ⟨o', i'⟩ (rfl : i = i')
  exact digest_loop_body state state' o o' i

@[ct_rel] theorem digest (state state' : Array U64 8#usize) :
    Rel (sha512.digest state) (sha512.digest state') (fun _ _ => True) := by
  unfold sha512.digest
  ct_steps

theorem pad_loop0_body (p p' : alloc.vec.Vec U8) (h : p.length = p'.length) :
    Rel (sha512.pad_loop0.body p) (sha512.pad_loop0.body p')
      (CFRel (fun q q' => q.length = q'.length) (fun q q' => q.length = q'.length)) := by
  unfold sha512.pad_loop0.body
  simp only [(Facts.vec_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem pad_loop0 (p p' : alloc.vec.Vec U8) (h : p.length = p'.length) :
    Rel (sha512.pad_loop0 p) (sha512.pad_loop0 p') (fun q q' => q.length = q'.length) := by
  unfold sha512.pad_loop0
  exact Rel.loop (fun q q' => q.length = q'.length) (fun q q' hq => pad_loop0_body q q' hq) h

theorem pad_loop1_body (bitlen : U128) (p p' : alloc.vec.Vec U8) (i : U32)
    (h : p.length = p'.length) :
    Rel (sha512.pad_loop1.body bitlen p i) (sha512.pad_loop1.body bitlen p' i)
      (CFRel (fun q q' => q.1.length = q'.1.length ∧ q.2 = q'.2)
        (fun q q' => q.length = q'.length)) := by
  unfold sha512.pad_loop1.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem pad_loop1 (p p' : alloc.vec.Vec U8) (bitlen : U128) (i : U32)
    (h : p.length = p'.length) :
    Rel (sha512.pad_loop1 p bitlen i) (sha512.pad_loop1 p' bitlen i)
      (fun q q' => q.length = q'.length) := by
  unfold sha512.pad_loop1
  refine Rel.loop (fun q q' => q.1.length = q'.1.length ∧ q.2 = q'.2) ?_ ⟨h, rfl⟩
  rintro ⟨a, j⟩ ⟨a', j'⟩ ⟨ha, (rfl : j = j')⟩
  exact pad_loop1_body bitlen a a' j ha

@[ct_rel] theorem pad (msg msg' : Slice U8) (pre : Usize) (h : msg.length = msg'.length) :
    Rel (sha512.pad msg pre) (sha512.pad msg' pre) (fun q q' => q.length = q'.length) := by
  unfold sha512.pad
  simp only [(Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

theorem sha512_from_loop0_body (msg msg' : Slice U8) (st st' : Array U64 8#usize) (off : Usize)
    (h : msg.length = msg'.length) :
    Rel (sha512.sha512_from_loop0.body msg st off) (sha512.sha512_from_loop0.body msg' st' off)
      (CFRel (fun p q => p.2 = q.2) (fun p q => p.2 = q.2)) := by
  unfold sha512.sha512_from_loop0.body
  simp only [(Facts.slice_len_congr h).symm]
  ct_steps
  all_goals simp_all

@[ct_rel] theorem sha512_from_loop0 (msg msg' : Slice U8) (st st' : Array U64 8#usize)
    (off : Usize) (h : msg.length = msg'.length) :
    Rel (sha512.sha512_from_loop0 msg st off) (sha512.sha512_from_loop0 msg' st' off)
      (fun p q => p.2 = q.2) := by
  unfold sha512.sha512_from_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨s, o⟩ ⟨s', o'⟩ (rfl : o = o')
  exact sha512_from_loop0_body msg msg' s s' o h

theorem sha512_from_loop1_body (p p' : alloc.vec.Vec U8) (st st' : Array U64 8#usize)
    (o : Usize) (h : p.length = p'.length) :
    Rel (sha512.sha512_from_loop1.body p st o) (sha512.sha512_from_loop1.body p' st' o)
      (CFRel (fun a b => a.2 = b.2) (fun _ _ => True)) := by
  unfold sha512.sha512_from_loop1.body
  simp only [(Facts.vec_len_congr h).symm]
  ct_steps
  all_goals simp_all

@[ct_rel] theorem sha512_from_loop1 (st st' : Array U64 8#usize) (p p' : alloc.vec.Vec U8)
    (o : Usize) (h : p.length = p'.length) :
    Rel (sha512.sha512_from_loop1 st p o) (sha512.sha512_from_loop1 st' p' o)
      (fun _ _ => True) := by
  unfold sha512.sha512_from_loop1
  refine Rel.loop (fun a b => a.2 = b.2) ?_ rfl
  rintro ⟨s, o⟩ ⟨s', o'⟩ (rfl : o = o')
  exact sha512_from_loop1_body p p' s s' o h

@[ct_rel] theorem sha512_from (state state' : Array U64 8#usize) (pre : Usize)
    (msg msg' : Slice U8) (h : msg.length = msg'.length) :
    Rel (sha512.sha512_from state pre msg) (sha512.sha512_from state' pre msg')
      (fun _ _ => True) := by
  unfold sha512.sha512_from
  simp only [(Facts.slice_len_congr h).symm]
  ct_steps

@[ct_rel] theorem sha512 (msg msg' : Slice U8) (h : msg.length = msg'.length) :
    Rel (sha512.sha512 msg) (sha512.sha512 msg') (fun _ _ => True) := by
  unfold sha512.sha512
  ct_steps

theorem hmac_sha512_loop_body (key key' : Slice U8) (inner inner' outer outer' : alloc.vec.Vec U8)
    (i : Usize) (hk : key.length = key'.length) (hi : inner.length = inner'.length)
    (ho : outer.length = outer'.length) :
    Rel (sha512.hmac_sha512_loop.body key inner outer i)
      (sha512.hmac_sha512_loop.body key' inner' outer' i)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2.1.length = q.2.1.length ∧ p.2.2 = q.2.2)
        (fun p q => p.1.length = q.1.length ∧ p.2.length = q.2.length)) := by
  unfold sha512.hmac_sha512_loop.body
  simp only [(Facts.slice_len_congr hk).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem hmac_sha512_loop (key key' : Slice U8) (inner inner' outer outer' : alloc.vec.Vec U8)
    (i : Usize) (hk : key.length = key'.length) (hi : inner.length = inner'.length)
    (ho : outer.length = outer'.length) :
    Rel (sha512.hmac_sha512_loop key inner outer i) (sha512.hmac_sha512_loop key' inner' outer' i)
      (fun p q => p.1.length = q.1.length ∧ p.2.length = q.2.length) := by
  unfold sha512.hmac_sha512_loop
  refine Rel.loop
    (fun p q => p.1.length = q.1.length ∧ p.2.1.length = q.2.1.length ∧ p.2.2 = q.2.2)
    ?_ ⟨hi, ho, rfl⟩
  rintro ⟨a, b, j⟩ ⟨a', b', j'⟩ ⟨ha, hb, (rfl : j = j')⟩
  exact hmac_sha512_loop_body key key' a a' b b' j hk ha hb

@[ct_rel] theorem hmac_sha512 (key key' msg msg' : Slice U8) (hk : key.length = key'.length)
    (hm : msg.length = msg'.length) :
    Rel (sha512.hmac_sha512 key msg) (sha512.hmac_sha512 key' msg') (fun _ _ => True) := by
  unfold sha512.hmac_sha512
  ct_steps

end Ct.Sha512
