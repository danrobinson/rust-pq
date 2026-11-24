import Kneon.Rows
import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result
namespace slhdsa.Kneon
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
private theorem idx {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize) (h : i.val < n.val) :
    a.index_usize i = ok a.val[i.val]! := by
  have hi : i.val < a.val.length := by simpa using h
  simp [Array.index_usize, Array.getElem?_Usize_eq, getElem?_pos a.val i.val hi, getElem!_pos a.val i.val hi]

private theorem upd {α : Type} {n : Usize} (a : Array α n) (i : Usize) (v : α) (h : i.val < n.val) :
    a.update i v = ok (a.set i v) := by
  obtain ⟨out,eq,post⟩ := spec_imp_exists (Array.update_spec a i v (by simpa using h))
  simpa [post] using eq

private theorem literalAdd (a b : Usize) (h : a.val+b.val ≤ 80) :
    a+b = ok (UScalar.ofNat (a.val+b.val) (by change _ ≤ 4294967295; omega) : Usize) := by
  obtain ⟨v,eq,val⟩ := spec_imp_exists (Usize.add_spec (x := a) (y := b) (by scalar_tac))
  rw [eq]; congr 1; exact UScalar.eq_of_val_eq val

theorem round_plain (a : Array KneonRust.core.core_arch.arm_shared.neon.uint64x2_t 25#usize) (rc : U64) :
    KneonRust.shake256.parallel.neon.round a rc = ok (pureRound a rc) := by
  unfold KneonRust.shake256.parallel.neon.round
  simp (config := {maxSteps := 2000000}) (disch := decide) only [bind_ok,
    show 0#usize + 1#usize = ok 1#usize from literalAdd _ _ (by decide),
    show 0#usize + 2#usize = ok 2#usize from literalAdd _ _ (by decide),
    show 0#usize + 3#usize = ok 3#usize from literalAdd _ _ (by decide),
    show 0#usize + 4#usize = ok 4#usize from literalAdd _ _ (by decide),
    show 10#usize + 1#usize = ok 11#usize from literalAdd _ _ (by decide),
    show 10#usize + 2#usize = ok 12#usize from literalAdd _ _ (by decide),
    show 10#usize + 3#usize = ok 13#usize from literalAdd _ _ (by decide),
    show 10#usize + 4#usize = ok 14#usize from literalAdd _ _ (by decide),
    show 15#usize + 1#usize = ok 16#usize from literalAdd _ _ (by decide),
    show 15#usize + 2#usize = ok 17#usize from literalAdd _ _ (by decide),
    show 15#usize + 3#usize = ok 18#usize from literalAdd _ _ (by decide),
    show 15#usize + 4#usize = ok 19#usize from literalAdd _ _ (by decide),
    show 20#usize + 1#usize = ok 21#usize from literalAdd _ _ (by decide),
    show 20#usize + 2#usize = ok 22#usize from literalAdd _ _ (by decide),
    show 20#usize + 3#usize = ok 23#usize from literalAdd _ _ (by decide),
    show 20#usize + 4#usize = ok 24#usize from literalAdd _ _ (by decide),
    show 5#usize + 1#usize = ok 6#usize from literalAdd _ _ (by decide),
    show 5#usize + 2#usize = ok 7#usize from literalAdd _ _ (by decide),
    show 5#usize + 3#usize = ok 8#usize from literalAdd _ _ (by decide),
    show 5#usize + 4#usize = ok 9#usize from literalAdd _ _ (by decide)]
  simp (config := {maxSteps := 2000000}) (disch := decide) only [idx,upd,Array.make_val,
    show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl, show (2#usize).val = 2 from rfl, show (3#usize).val = 3 from rfl, show (4#usize).val = 4 from rfl, show (5#usize).val = 5 from rfl, show (6#usize).val = 6 from rfl, show (7#usize).val = 7 from rfl, show (8#usize).val = 8 from rfl, show (9#usize).val = 9 from rfl, show (10#usize).val = 10 from rfl, show (11#usize).val = 11 from rfl, show (12#usize).val = 12 from rfl, show (13#usize).val = 13 from rfl, show (14#usize).val = 14 from rfl, show (15#usize).val = 15 from rfl, show (16#usize).val = 16 from rfl, show (17#usize).val = 17 from rfl, show (18#usize).val = 18 from rfl, show (19#usize).val = 19 from rfl, show (20#usize).val = 20 from rfl, show (21#usize).val = 21 from rfl, show (22#usize).val = 22 from rfl, show (23#usize).val = 23 from rfl, show (24#usize).val = 24 from rfl,
    List.getElem!_cons_zero,List.getElem!_cons_succ]
  simp (config := {maxSteps := 2000000}) only [lift,bind_ok,
    KneonRust.core.core_arch.arm_shared.neon.generated.veorq_u64,
    KneonRust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64,
    KneonRust.core.core_arch.arm_shared.neon.generated.vbicq_u64,
    KneonRust.core.core_arch.arm_shared.neon.generated.vshlq_n_u64,
    KneonRust.core.core_arch.aarch64.neon.generated.vsriq_n_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.veorq_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64]
  rfl
end slhdsa.Kneon
