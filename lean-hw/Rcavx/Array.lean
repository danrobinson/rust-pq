import Aeneas
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
theorem at0 {α : Type} (a b c d e f g h : α) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 0#usize = ok a := by rfl
theorem put0 {α : Type} (a b c d e f g h z : α) : Array.update (Array.make 8#usize [a,b,c,d,e,f,g,h]) 0#usize z = ok (Array.make 8#usize [z,b,c,d,e,f,g,h]) := by rfl
theorem at1 {α : Type} (a b c d e f g h : α) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 1#usize = ok b := by rfl
theorem put1 {α : Type} (a b c d e f g h z : α) : Array.update (Array.make 8#usize [a,b,c,d,e,f,g,h]) 1#usize z = ok (Array.make 8#usize [a,z,c,d,e,f,g,h]) := by rfl
theorem at2 {α : Type} (a b c d e f g h : α) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 2#usize = ok c := by rfl
theorem put2 {α : Type} (a b c d e f g h z : α) : Array.update (Array.make 8#usize [a,b,c,d,e,f,g,h]) 2#usize z = ok (Array.make 8#usize [a,b,z,d,e,f,g,h]) := by rfl
theorem at3 {α : Type} (a b c d e f g h : α) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 3#usize = ok d := by rfl
theorem put3 {α : Type} (a b c d e f g h z : α) : Array.update (Array.make 8#usize [a,b,c,d,e,f,g,h]) 3#usize z = ok (Array.make 8#usize [a,b,c,z,e,f,g,h]) := by rfl
theorem at4 {α : Type} (a b c d e f g h : α) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 4#usize = ok e := by rfl
theorem put4 {α : Type} (a b c d e f g h z : α) : Array.update (Array.make 8#usize [a,b,c,d,e,f,g,h]) 4#usize z = ok (Array.make 8#usize [a,b,c,d,z,f,g,h]) := by rfl
theorem at5 {α : Type} (a b c d e f g h : α) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 5#usize = ok f := by rfl
theorem put5 {α : Type} (a b c d e f g h z : α) : Array.update (Array.make 8#usize [a,b,c,d,e,f,g,h]) 5#usize z = ok (Array.make 8#usize [a,b,c,d,e,z,g,h]) := by rfl
theorem at6 {α : Type} (a b c d e f g h : α) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 6#usize = ok g := by rfl
theorem put6 {α : Type} (a b c d e f g h z : α) : Array.update (Array.make 8#usize [a,b,c,d,e,f,g,h]) 6#usize z = ok (Array.make 8#usize [a,b,c,d,e,f,z,h]) := by rfl
theorem at7 {α : Type} (a b c d e f g h : α) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 7#usize = ok h := by rfl
theorem put7 {α : Type} (a b c d e f g h z : α) : Array.update (Array.make 8#usize [a,b,c,d,e,f,g,h]) 7#usize z = ok (Array.make 8#usize [a,b,c,d,e,f,g,z]) := by rfl
theorem materialize {α : Type} [Inhabited α] (x : Array α 8#usize) :
  x = Array.make 8#usize [x.val[0]!,x.val[1]!,x.val[2]!,x.val[3]!,x.val[4]!,x.val[5]!,x.val[6]!,x.val[7]!] := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp [Array.make]
  · intro k h _
    have bound : k<8 := by simpa using h
    interval_cases k <;> simp [Array.make]
end slhdsa.X86.RustCrypto512
