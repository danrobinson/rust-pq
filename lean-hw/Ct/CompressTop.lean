import Ct.Sha256Core

/-!
# Constant time: `sha256::compress`, as built with `hw-sha2`

`sha256::compress` first calls the hardware kernel `sha256::hw::compress`, which tests
`available()` and, if the processor has the instructions, copies the block and runs
`compress_block`; on `None` it falls back to the portable code. The statement is the one of the
default build (`lean/Ct/CompressTop.lean`).

The kernel's trace: the test (a branch on `Arm.haveSha2`, the same in both runs), the copy of
the block (its range `[off, off + 64)` and lengths), and in `compress_block` the loads at fixed
positions and the round loop, bounded by 16, whose indices are the loop counter. The values
(state, block, message schedule, round state) are in vector registers and only pass through the
register-only wrappers, which emit nothing (the assumption of `Ct/ModelBuild.lean`).
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Sha256

open slhdsa_leak

abbrev Vec := core.core_arch.arm_shared.neon.uint32x4_t

theorem hw_compress_block_loop_body (abcd abcd' efgh efgh' : Vec) (m m' : Array Vec 4#usize)
    (i : Usize) :
    Rel (sha256.hw.compress_block_loop.body abcd efgh m i)
      (sha256.hw.compress_block_loop.body abcd' efgh' m' i)
      (CFRel (fun p q => p.2.2.2 = q.2.2.2) (fun _ _ => True)) := by
  unfold sha256.hw.compress_block_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem hw_compress_block_loop (abcd abcd' efgh efgh' : Vec) (m m' : Array Vec 4#usize)
    (i : Usize) :
    Rel (sha256.hw.compress_block_loop abcd efgh m i)
      (sha256.hw.compress_block_loop abcd' efgh' m' i) (fun _ _ => True) := by
  unfold sha256.hw.compress_block_loop
  refine Rel.loop (fun p q => p.2.2.2 = q.2.2.2) ?_ rfl
  rintro ⟨a, e, x, j⟩ ⟨a', e', x', j'⟩ (rfl : j = j')
  exact hw_compress_block_loop_body a a' e e' x x' j

@[ct_rel] theorem hw_compress_block (state state' : Array U32 8#usize)
    (block block' : Array U8 64#usize) :
    Rel (sha256.hw.compress_block state block) (sha256.hw.compress_block state' block')
      (fun _ _ => True) := by
  unfold sha256.hw.compress_block
  ct_steps

/-- The kernel: both runs take the hardware path or both do not (the test is on
`Arm.haveSha2`). -/
@[ct_rel] theorem hw_compress (state state' : Array U32 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha256.hw.compress state data off) (sha256.hw.compress state' data' off)
      (fun o o' => o.isSome = o'.isSome) := by
  unfold sha256.hw.compress
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem compress (state state' : Array U32 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha256.compress state data off) (sha256.compress state' data' off)
      (fun _ _ => True) := by
  unfold sha256.compress
  refine Rel.bind (hw_compress state state' data data' off h) fun o o' ho => ?_
  refine Rel.matchOpt ho (fun _ _ => compress_portable state state' data data' off h)
    (fun _ _ _ _ => Rel.pure trivial)

end Ct.Sha256
