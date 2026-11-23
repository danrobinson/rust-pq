import Chainavx2.Groups
import Chainni.Residual
open Aeneas Aeneas.Std Result
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust

theorem flat_size (xs : List Batch) : (xs.flatMap (·.val)).length = 8*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih,Nat.mul_add,Nat.add_comm]

theorem flat_lane (xs : List Batch) (g : Nat) (j : Fin 8) (hg : g < xs.length) :
    (xs.flatMap (·.val))[8*g+j.val]! = xs[g]!.val[j.val]! := by
  induction xs generalizing g with
  | nil => simp at hg
  | cons a xs ih =>
    cases g with
    | zero => simp (disch := simp [j.isLt]) only [Nat.mul_zero,Nat.zero_add,List.flatMap_cons,
        List.getElem!_append_left,List.getElem!_cons_zero]
    | succ g =>
      simp only [List.flatMap_cons,List.getElem!_cons_succ]
      have hlen : a.val.length ≤ 8*(g+1)+j.val := by simp; omega
      rw [List.getElem!_append_right _ _ _ hlen]
      rw [show 8*(g+1)+j.val-a.val.length = 8*g+j.val by simp; omega]
      exact ih g (by simpa using hg)

theorem group_size (blocks : Intel.Chain.Rows) :
    (fullChunks 8#usize blocks).length = blocks.length/8 := by
  simp [fullChunks,Slice.length,Slice.from_val]

theorem group_lane (blocks : Intel.Chain.Rows) (g : Nat) (j : Fin 8) (hg : g < blocks.length/8) :
    (fullChunks 8#usize blocks).val[g]!.val[j.val]! = blocks.val[8*g+j.val]! := by
  simp (disch := simpa using hg) only [fullChunks,Slice.from_val,getElem!_pos,List.length_ofFn,
    List.getElem_ofFn,Array.from_val]
  exact getElem!_take_drop _ _ _ _ j.isLt


theorem reassemble (N : Usize) (state : Array U32 8#usize) (iv : EightRegs)
    (blocks tail : Intel.Chain.Rows) (groups : Groups) (starts ends : Slice U32)
    (initial : ∀ j, X86.stateWords (laneState iv j) = wv state.val)
    (groupOK : GroupPrefix N iv starts ends (fullChunks 8#usize blocks) groups (blocks.length/8))
    (tailSize : tail.length = blocks.length - 8*(blocks.length/8))
    (tailOK : ∀ k < tail.length, bytes tail.val[k]!.val = runBlock N.val (wv state.val)
      (bytes blocks.val[8*(blocks.length/8)+k]!.val) starts.val[8*(blocks.length/8)+k]!.val
      ends.val[8*(blocks.length/8)+k]!.val) :
    Intel.Chain.Ended N state blocks (joinChunks blocks (groups,tail)) starts ends := by
  obtain ⟨glen,rows⟩ := groupOK
  rw [group_size] at glen
  have flatLen : (groups.val.flatMap (·.val)).length = 8*(blocks.length/8) := (flat_size groups.val).trans (by rw [← glen])
  have total : (groups.val.flatMap (·.val) ++ tail.val).length = blocks.length := by
    rw [List.length_append,flatLen,show tail.val.length = _ from tailSize]; omega
  have joined : (joinChunks blocks (groups,tail)).val = groups.val.flatMap (·.val) ++ tail.val := by
    simp only [joinChunks,total,dif_pos,Slice.from_val]
  refine ⟨by change (joinChunks blocks (groups,tail)).val.length = _; rw [joined,total],fun k hk => ?_⟩
  rw [joined]
  by_cases full : k < 8*(blocks.length/8)
  · let j : Fin 8 := ⟨k%8,by omega⟩
    have split : 8*(k/8)+j.val = k := by dsimp [j]; omega
    have hg : k/8 < blocks.length/8 := by omega
    have row := rows (k/8) (by rw [group_size]; exact hg) j
    rw [if_pos hg,initial,group_lane blocks _ j hg,split] at row
    rw [List.getElem!_append_left _ _ _ (flatLen ▸ full),← split,flat_lane _ (k/8) j (by change k/8 < groups.length; omega)]
    simpa only [split] using row
  · have le : 8*(blocks.length/8) ≤ k := by omega
    rw [List.getElem!_append_right _ _ _ (flatLen ▸ le),flatLen]
    simpa only [Nat.add_sub_of_le le] using tailOK (k-8*(blocks.length/8)) (by omega)
end slhdsa.Avx2.Chain
