import Std

namespace MetalBindings

/-- The encoder's setBuffer loop overwrites successive slots, starting at
`base`. Slots outside the loop retain their previous bindings. -/
def writeBuffers (previous : Nat → α) (base : Nat) : List α → Nat → α
  | [] => previous
  | x :: xs => writeBuffers (fun i => if i = base then x else previous i) (base + 1) xs

private theorem before (xs : List α) (previous : Nat → α) (base i : Nat) (h : i < base) :
    writeBuffers previous base xs i = previous i := by
  induction xs generalizing previous base with
  | nil => rfl
  | cons x xs ih =>
    rw [writeBuffers, ih _ _ (by omega)]
    simp [Nat.ne_of_lt h]

theorem buffer_at (xs : List α) (previous : Nat → α) (base j : Nat) (h : j < xs.length) :
    writeBuffers previous base xs (base + j) = xs[j] := by
  induction xs generalizing previous base j with
  | nil => simp at h
  | cons x xs ih =>
    cases j with
    | zero => simp [writeBuffers, before]
    | succ j =>
      rw [writeBuffers]
      have shift : base + (j+1) = (base+1)+j := by omega
      rw [shift, ih _ _ _ (by simpa using h)]
      rfl

/-- The subsequent setBytes call uses its explicit slot. For any previous
encoder state and any resource values, every shader input resolves to the
intended buffer and the parameter slot resolves to the inline value. -/
theorem dispatch (host shader : List String) (inlineSlot : Nat)
    (same : host = shader) (slot : inlineSlot = host.length)
    (resource : String → α) (previous : Nat → α) (params : α) :
    let encoded := fun i => if i = inlineSlot then params
      else writeBuffers previous 0 (host.map resource) i
    encoded shader.length = params ∧
      ∀ i (inside : i < shader.length), encoded i = resource shader[i] := by
  subst shader
  subst inlineSlot
  refine ⟨by simp, ?_⟩
  intro i inside
  simp only [ite_eq_right (Nat.ne_of_lt inside)]
  have h := buffer_at (host.map resource) previous 0 i (by simpa using inside)
  rw [Nat.zero_add, List.getElem_map] at h
  exact h

/-- Every flattened index stays in its allocation and fits in the shader's
32-bit address arithmetic when the host's division guard admits the batch.
This also covers multi-word values ending at the last word of the last item. -/
theorem flat_index {count stride guard item offset : Nat}
    (positive : 0 < guard) (checked : count ≤ (2^32 - 1) / guard)
    (covers : stride ≤ guard) (hi : item < count) (ho : offset < stride) :
    item * stride + offset < count * stride ∧ count * stride ≤ 2^32 - 1 := by
  have h := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at h
  exact ⟨by omega, Nat.le_trans (Nat.mul_le_mul_left count covers)
    ((Nat.le_div_iff_mul_le positive).mp checked)⟩

end MetalBindings
