import Wots.Funs
import Store256.Proof
import Chainni.Words
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots

theorem flat_length {N : Usize} (rows : List (Array U8 N)) :
    (rows.flatMap (·.val)).length = N.val * rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem flat_byte {N : Usize} (rows : List (Array U8 N)) (i k : Nat)
    (hi : i < rows.length) (hk : k < N.val) :
    (rows.flatMap (·.val))[N.val*i+k]! = rows[i]!.val[k]! := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    cases i with
    | zero => simp (disch := simpa using hk) only [Nat.mul_zero,Nat.zero_add,List.flatMap_cons,
        List.getElem!_append_left,List.getElem!_cons_zero]
    | succ i =>
      simp only [List.flatMap_cons,List.getElem!_cons_succ,Nat.mul_succ]
      rw [List.getElem!_append_right _ _ _ (by simp; omega)]
      rw [show row.val.length = N.val by simp]
      rw [show N.val*i + N.val + k - N.val = N.val*i+k by omega]
      exact ih i (by simpa using hi)

theorem flatten_spec {N : Usize} (rows : Slice (Array U8 N)) (bound : N.val * rows.length ≤ Usize.max) :
    WotsRust.core.slice.SliceArray.as_flattened rows ⦃ flat =>
      flat.length = N.val * rows.length ∧ ∀ i < rows.length, ∀ k < N.val,
        flat.val[N.val*i+k]! = rows.val[i]!.val[k]! ⦄ := by
  have fits : (rows.val.flatMap (·.val)).length ≤ Usize.max := (flat_length rows.val) ▸ bound
  simp only [WotsRust.core.slice.SliceArray.as_flattened,dif_pos fits,step_simps]
  constructor
  · simpa [Slice.length,Slice.from_val] using flat_length rows.val
  · intro i hi k hk
    simpa [Slice.from_val] using flat_byte rows.val i k hi hk

/-- The range mutation and contiguous byte copy used on both sides of a keypair boundary. -/
def copyRows {N L : Usize} (out : Slice (Array U8 L)) (key pos stop : Usize)
    (rows : Slice (Array U8 N)) := do
  let (a,back) ← Slice.index_mut_usize out key
  let (dst,restore) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) a
    (⟨pos,stop⟩ : core.ops.range.Range Usize)
  let flat ← WotsRust.core.slice.SliceArray.as_flattened rows
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dst flat
  ok (back (restore copied))

theorem copy_rows_spec {N L : Usize} (out : Slice (Array U8 L)) (key pos stop : Usize)
    (rows : Slice (Array U8 N)) (hkey : key.val < out.length)
    (hlen : stop.val = pos.val + N.val * rows.length) (hstop : stop.val ≤ L.val) :
    copyRows out key pos stop rows ⦃ r => r.length = out.length ∧
      (∀ j, j ≠ key.val → r.val[j]! = out.val[j]!) ∧
      r.val[key.val]!.val = out.val[key.val]!.val.take pos.val ++
        rows.val.flatMap (·.val) ++ out.val[key.val]!.val.drop stop.val ⦄ := by
  unfold copyRows
  have fits : (rows.val.flatMap (·.val)).length ≤ Usize.max := by
    rw [flat_length]; change N.val * rows.length ≤ Usize.max
    exact Nat.le_trans (by omega : N.val * rows.length ≤ stop.val) (by scalar_tac)
  step as ⟨ab,ha,hback⟩
  obtain ⟨a,back⟩ := ab
  step as ⟨sb,hsub,hslen,hba⟩
  obtain ⟨s,restore⟩ := sb
  simp only at ha hback hsub hslen hba
  simp only [WotsRust.core.slice.SliceArray.as_flattened,dif_pos fits]
  step as ⟨copied,hc⟩
  · rw [hslen]; simp only [Slice.length,Slice.from_val,flat_length]; change stop.val-pos.val = N.val*rows.length; omega
  simp only [step_simps,hback,Slice.set_val_eq]
  refine ⟨by simp,fun j hj => Avx2.setOther _ _ _ _ (Ne.symm hj),?_⟩
  rw [Avx2.setSame _ _ _ hkey,hc,hba]
  · have room : N.val*rows.val.length ≤ out.val[key.val]!.val.length-pos.val := by
      rw [show out.val[key.val]!.val.length = L.val by simp]
      change N.val*rows.length ≤ L.val-pos.val
      omega
    simp only [List.setSlice!,ha,← getElem!_pos,Slice.from_val,flat_length,Nat.min_eq_left room]
    rw [← flat_length rows.val,List.take_length,flat_length]
    change _ ++ List.drop (pos.val+N.val*rows.length) _ = _
    rw [← hlen]

def stage {N : Usize} (hash : Array Store.Reg512 8#usize) (used : Usize) := do
  let values := Array.repeat 16#usize (Array.repeat N 0#u8)
  let (s,back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) values
    (⟨used⟩ : core.ops.range.RangeTo Usize)
  let written ← WotsRust.sha256.x86.avx512.write_words hash s
  ok (back written)

theorem stage_spec {N : Usize} (hash : Array Store.Reg512 8#usize) (used : Usize)
    (hn : N.val = 16 ∨ N.val = 24 ∨ N.val = 32) (hu : used.val ≤ 16) :
    stage (N := N) hash used ⦃ a => ∀ j : Fin 16, j.val < used.val → ∀ k < N.val,
      (a.val[j.val]!.val[k]!).bv = Store.digestByte hash j k ⦄ := by
  unfold stage
  step as ⟨pair,hsub,hlen,hback⟩
  obtain ⟨s,back⟩ := pair
  simp only at hsub hlen hback
  step with Store.write_words_spec hash s hn (by omega) as ⟨w,hwlen,hw⟩
  intro j hj k hk
  rw [hback,List.getElem!_setSlice!_middle _ _ _ _ (by simp; change j.val < w.length; omega)]
  exact hw j (by omega) k hk

end slhdsa.X86.Wots
