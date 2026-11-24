import S512schedule.Funs
import Streamvector.FixedTable
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream.Eight512
private theorem word_eq : S512scheduleRust.sha512.stream.schedule_word =
    StreamVectorRust.sha512.stream.schedule_word := by
  unfold S512scheduleRust.sha512.stream.schedule_word StreamVectorRust.sha512.stream.schedule_word
    S512scheduleRust.sha512.K StreamVectorRust.sha512.K
  rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
theorem schedule (w : Array Reg 16#usize) (blocks : Array (Array U8 128#usize) 8#usize)
    (window : vectorWindow512 w blocks 0) :
    S512scheduleRust.sha512.stream.schedule_table w ⦃ out => ordered512 out blocks 80 ⦄ := by
  have eq : S512scheduleRust.sha512.stream.schedule_table = StreamVectorRust.sha512.stream.schedule_table := by
    unfold S512scheduleRust.sha512.stream.schedule_table StreamVectorRust.sha512.stream.schedule_table
    simp (config := {maxSteps := 500000}) only [word_eq]
  rw [eq]
  exact fixedTable512 w blocks window
end slhdsa.X86.Stream.Eight512
