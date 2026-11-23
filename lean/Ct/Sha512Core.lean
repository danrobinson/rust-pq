import Ct.Sha256

/-!
# Constant time: the SHA-512 layer, up to the portable compression function

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

end Ct.Sha512
