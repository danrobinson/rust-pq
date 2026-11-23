import Parent256.Batch
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Parent
abbrev Rows := Slice (Array U8 16#usize)

def Processed (expected : Nat → Spec.Bytes) (before after : Rows) (done : Nat) :=
  after.length = before.length ∧ ∀ i, i < before.length →
    if i < done then bytes after.val[i]!.val = expected i else after.val[i]! = before.val[i]!

theorem children_intact (expected : Nat → Spec.Bytes) (before buf : Rows) (done i : Nat)
    (h : Processed expected before buf done) (hi : done ≤ i)
    (bound : 2*i+1 < before.length) : children buf i = children before i := by
  have left := h.2 (2*i) (by omega)
  have right := h.2 (2*i+1) bound
  simp only [if_neg (show ¬2*i < done by omega)] at left
  simp only [if_neg (show ¬2*i+1 < done by omega)] at right
  simp only [children,left,right]

theorem advance (expected : Nat → Spec.Bytes) (before buf batch after : Rows)
    (start : Nat) (h : Processed expected before buf start)
    (fits : start+batch.length ≤ before.length)
    (back : after.val = buf.val.setSlice! start batch.val)
    (produced : ∀ j, j < batch.length → bytes batch.val[j]!.val = expected (start+j)) :
    Processed expected before after (start+batch.length) := by
  have len := h.1
  refine ⟨?_,fun k hk => ?_⟩
  · change after.val.length = before.length
    rw [back,List.length_setSlice!]
    exact len
  by_cases early : k < start
  · simp only [if_pos (show k < start+batch.length by omega),back,List.getElem!_setSlice!_prefix _ _ _ _ early]
    simpa only [if_pos early] using h.2 k hk
  · by_cases active : k < start+batch.length
    · simp only [if_pos active,back]
      rw [List.getElem!_setSlice!_middle _ _ _ _ (by change start ≤ k ∧ k-start < batch.length ∧ k < buf.length; omega)]
      simpa only [show start+(k-start)=k by omega] using produced (k-start) (by omega)
    · simp only [if_neg active,back,List.getElem!_setSlice!_suffix _ _ _ _ (by change start+batch.length ≤ k; omega)]
      simpa only [if_neg early] using h.2 k hk

end slhdsa.X86.Parent
