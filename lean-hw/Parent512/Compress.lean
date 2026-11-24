import Parent512.Load
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Parents
open ParentsRust.sha512.x86
private theorem same_step (i : Usize) (s : Array Reg 8#usize) (w : Array Reg 16#usize) :
    compression_step i s w = PlatformRust.sha512.x86.compression_step i s w := by
  have h : ParentsRust.sha512.K = PlatformRust.sha512.K := by
    unfold ParentsRust.sha512.K PlatformRust.sha512.K; rfl
  simp only [compression_step, PlatformRust.sha512.x86.compression_step, h]

set_option maxRecDepth 8000 in
theorem compress_eq (s : Array Reg 8#usize) (w : Array Reg 16#usize) :
    compress s w = PlatformRust.sha512.x86.compress s w := by
  simp only [compress, PlatformRust.sha512.x86.compress, same_step]

/-- All eight native chaining states match the caller's input before the first round. -/
theorem initial_words (a : Array Reg 8#usize) (st : Array U64 8#usize)
    (ha : ∀ i, i < 8 → ∀ j : Fin 8, word64 a.val[i]! j = st.val[i]!.bv) (j : Fin 8) :
    stateWords (laneState a j) = st.val.map (·.bv) := by
  simp (disch := decide) only [laneState, stateWords, ha]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi8 : i < 8 := by simpa using hj
    rw [List.getElem_map]
    interval_cases i <;> simp [getElem!_pos]

#print axioms compress_eq
end slhdsa.X86.S512.Parents
