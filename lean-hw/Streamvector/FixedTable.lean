import Streamvector.Table
import Streamvector.Lanes
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000

private theorem literalAdd (a b : Usize) (h : a.val+b.val ≤ 80) :
    a+b = ok (UScalar.ofNat (a.val+b.val) (by change _ ≤ 4294967295; omega) : Usize) := by
  obtain ⟨v,eq,val⟩ := spec_imp_exists (Usize.add_spec (x := a) (y := b) (by scalar_tac))
  rw [eq]; congr 1; exact UScalar.eq_of_val_eq val

theorem fixedTable512 (w : Array Reg 16#usize) (blocks : Array (Array U8 128#usize) 8#usize)
    (window : vectorWindow512 w blocks 0) :
    StreamVectorRust.sha512.stream.schedule_table w ⦃ out => ordered512 out blocks 80 ⦄ := by
  have rows : ordered512 (Array.repeat 80#usize (Array.repeat 8#usize 0#u64)) blocks 0 :=
    fun i h => False.elim (Nat.not_lt_zero i h)
  unfold StreamVectorRust.sha512.stream.schedule_table
  simp (config := {maxSteps := 500000}) (disch := decide) only [literalAdd,bind_ok]
  iterate 79
    apply WP.spec_bind (scheduleWord512 _ _ blocks (by decide) (by assumption))
    rintro ⟨row,win⟩ ⟨window,h⟩
    apply WP.spec_bind (Array.update_spec _ _ _ (by simp <;> decide))
    intro table write
    have rows' := write_ordered512 _ blocks _ row (by decide) (by assumption) h
    rw [← write] at rows'
  apply WP.spec_bind (scheduleWord512 79#usize _ blocks (by decide) (by assumption))
  rintro ⟨row,win⟩ ⟨_,h⟩
  apply WP.spec_mono (Array.update_spec _ 79#usize row (by simp))
  intro table write
  rw [write]
  exact write_ordered512 _ blocks 79#usize row (by decide) (by assumption) h
end slhdsa.X86.Stream
