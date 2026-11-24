import Kgridbulk.Funs
import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result
namespace slhdsa.Kgridbulk
open KgridbulkRust
abbrev wordAt := GatherRust.core.core_arch.x86.littleWord

private theorem lowFive (i : Fin 8) : (31#u8).bv.getLsbD i.val = decide (i.val < 5) := by
  fin_cases i <;> rfl
private theorem lowTwo (i : Fin 8) : (3#u8).bv.getLsbD i.val = decide (i.val < 2) := by
  fin_cases i <;> rfl

theorem maskedLoad (mask : U8) (count : Nat) (p : KgridbulkRust.ConstRawPtr I64)
    (bits : ∀ i : Fin 8, mask.bv.getLsbD i.val = decide (i.val < count))
    (bound : p.offset + 8*count ≤ p.allocation.length) :
    core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64 mask p =
      ok (fun i => if i.val < count then wordAt p.allocation (p.offset + 8*i.val) else 0) := by
  unfold core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64
  simp only [bits,decide_eq_true_eq]
  rw [if_pos (by intro i hi; omega)]

theorem loadFive (p : KgridbulkRust.ConstRawPtr I64) (bound : p.offset + 40 ≤ p.allocation.length) :
    core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64 31#u8 p =
      ok (fun i => if i.val < 5 then wordAt p.allocation (p.offset + 8*i.val) else 0) :=
  maskedLoad 31#u8 5 p lowFive bound

theorem loadTwo (p : KgridbulkRust.ConstRawPtr I64) (bound : p.offset + 16 ≤ p.allocation.length) :
    core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64 3#u8 p =
      ok (fun i => if i.val < 2 then wordAt p.allocation (p.offset + 8*i.val) else 0) :=
  maskedLoad 3#u8 2 p lowTwo bound
end slhdsa.Kgridbulk
