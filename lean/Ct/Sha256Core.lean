import Ct.Funs
import Ct.Tactic
import Ct.Facts
import Ct.Erase

/-!
# Constant time: the SHA-256 layer, portable compression

The part of `sha256.rs` that does not depend on the build: the message schedule and the
portable compression function. `sha256::compress` itself is in `Ct/CompressTop.lean` (one per
build), the rest of the module in `Ct/Sha256.lean`.

For every function of `rust/src/sha256.rs` (as translated), two runs on data of the same
lengths, with the same offsets and other public arguments, have the same trace; their results
are again of equal length (arrays: by their type; vectors: stated). Secret buffers enter only
through their lengths: a caller needs nothing but length equality for them.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Sha256

open slhdsa_leak

@[ct_rel] theorem load_be32 (data data' : Slice U8) (off : Usize)
    (h : data.length = data'.length) :
    Rel (sha256.load_be32 data off) (sha256.load_be32 data' off) (fun _ _ => True) := by
  unfold sha256.load_be32
  ct_steps

theorem schedule_loop0_body (data data' : Slice U8) (off : Usize) (w w' : Array U32 64#usize)
    (i : Usize) (h : data.length = data'.length) :
    Rel (sha256.schedule_loop0.body data off w i) (sha256.schedule_loop0.body data' off w' i)
      (CFRel (fun p q => p.2 = q.2) (fun p q => p.2 = q.2)) := by
  unfold sha256.schedule_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem schedule_loop0 (data data' : Slice U8) (off : Usize)
    (w w' : Array U32 64#usize) (i : Usize) (h : data.length = data'.length) :
    Rel (sha256.schedule_loop0 data off w i) (sha256.schedule_loop0 data' off w' i)
      (fun p q => p.2 = q.2) := by
  unfold sha256.schedule_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨w1, i1⟩ ⟨w1', i1'⟩ (rfl : i1 = i1')
  exact schedule_loop0_body data data' off w1 w1' i1 h

theorem schedule_loop1_body (w w' : Array U32 64#usize) (i : Usize) :
    Rel (sha256.schedule_loop1.body w i) (sha256.schedule_loop1.body w' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold sha256.schedule_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem schedule_loop1 (w w' : Array U32 64#usize) (i : Usize) :
    Rel (sha256.schedule_loop1 w i) (sha256.schedule_loop1 w' i) (fun _ _ => True) := by
  unfold sha256.schedule_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨w1, i1⟩ ⟨w1', i1'⟩ (rfl : i1 = i1')
  exact schedule_loop1_body w1 w1' i1

@[ct_rel] theorem schedule (data data' : Slice U8) (off : Usize)
    (h : data.length = data'.length) :
    Rel (sha256.schedule data off) (sha256.schedule data' off) (fun _ _ => True) := by
  unfold sha256.schedule
  ct_steps

theorem compress_portable_loop_body (w w' : Array U32 64#usize)
    (a b c d e f g h a' b' c' d' e' f' g' h' : U32) (i : Usize) :
    Rel (sha256.compress_portable_loop.body w a b c d e f g h i)
      (sha256.compress_portable_loop.body w' a' b' c' d' e' f' g' h' i)
      (CFRel (fun p q => p.2.2.2.2.2.2.2.2 = q.2.2.2.2.2.2.2.2) (fun _ _ => True)) := by
  unfold sha256.compress_portable_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem compress_portable_loop (w w' : Array U32 64#usize)
    (a b c d e f g h a' b' c' d' e' f' g' h' : U32) (i : Usize) :
    Rel (sha256.compress_portable_loop w a b c d e f g h i)
      (sha256.compress_portable_loop w' a' b' c' d' e' f' g' h' i) (fun _ _ => True) := by
  unfold sha256.compress_portable_loop
  refine Rel.loop (fun p q => p.2.2.2.2.2.2.2.2 = q.2.2.2.2.2.2.2.2) ?_ rfl
  rintro ⟨a, b, c, d, e, f, g, h, i⟩ ⟨a', b', c', d', e', f', g', h', i'⟩ (rfl : i = i')
  exact compress_portable_loop_body w w' a b c d e f g h a' b' c' d' e' f' g' h' i

@[ct_rel] theorem compress_portable (state state' : Array U32 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha256.compress_portable state data off) (sha256.compress_portable state' data' off)
      (fun _ _ => True) := by
  unfold sha256.compress_portable
  ct_steps


end Ct.Sha256
