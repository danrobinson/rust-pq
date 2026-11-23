import Ct.Sha512Core

/-!
# Constant time: `sha512::compress`, as built with `hw-sha2`

`sha512::compress` first calls the hardware kernel `sha512::hw::compress`, which tests
`available()` and, if the processor has the SHA-512 instructions, copies the block and runs
`compress_block`; on `None` it falls back to the portable code. The statement is the one of the
default build (`lean/Ct/Compress512Top.lean`).

The kernel's trace: the test (a branch on `Arm.haveSha512`, the same in both runs), the copy of
the block (its range `[off, off + 128)` and lengths), and in `compress_block` the loads at fixed
positions and the loop of forty steps, whose indices are the loop counter. The values (state,
block, message schedule, working variables) are in vector registers and only pass through the
register-only wrappers, which emit nothing (the assumption of `Ct/ModelBuild.lean`).
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Sha512

open slhdsa_leak

abbrev Vec2 := core.core_arch.arm_shared.neon.uint64x2_t

theorem hw_compress_block_loop_body (m m' : Array Vec2 8#usize) (ab ab' cd cd' ef ef' gh gh' : Vec2)
    (i : Usize) :
    Rel (sha512.hw.compress_block_loop.body m ab cd ef gh i)
      (sha512.hw.compress_block_loop.body m' ab' cd' ef' gh' i)
      (CFRel (fun p q => p.2.2.2.2.2 = q.2.2.2.2.2) (fun _ _ => True)) := by
  unfold sha512.hw.compress_block_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem hw_compress_block_loop (m m' : Array Vec2 8#usize) (ab ab' cd cd' ef ef' gh gh' : Vec2)
    (i : Usize) :
    Rel (sha512.hw.compress_block_loop m ab cd ef gh i)
      (sha512.hw.compress_block_loop m' ab' cd' ef' gh' i) (fun _ _ => True) := by
  unfold sha512.hw.compress_block_loop
  refine Rel.loop (fun p q => p.2.2.2.2.2 = q.2.2.2.2.2) ?_ rfl
  rintro ⟨x, a, c, e, g, j⟩ ⟨x', a', c', e', g', j'⟩ (rfl : j = j')
  exact hw_compress_block_loop_body x x' a a' c c' e e' g g' j

@[ct_rel] theorem hw_compress_block (state state' : Array U64 8#usize)
    (block block' : Array U8 128#usize) :
    Rel (sha512.hw.compress_block state block) (sha512.hw.compress_block state' block')
      (fun _ _ => True) := by
  unfold sha512.hw.compress_block
  ct_steps

/-- The kernel: both runs take the hardware path or both do not (the test is on
`Arm.haveSha512`). -/
@[ct_rel] theorem hw_compress (state state' : Array U64 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha512.hw.compress state data off) (sha512.hw.compress state' data' off)
      (fun o o' => o.isSome = o'.isSome) := by
  unfold sha512.hw.compress
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem compress (state state' : Array U64 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha512.compress state data off) (sha512.compress state' data' off)
      (fun _ _ => True) := by
  unfold sha512.compress
  refine Rel.bind (hw_compress state state' data data' off h) fun o o' ho => ?_
  refine Rel.matchOpt ho (fun _ _ => compress_portable state state' data data' off h)
    (fun _ _ _ _ => Rel.pure trivial)

end Ct.Sha512
