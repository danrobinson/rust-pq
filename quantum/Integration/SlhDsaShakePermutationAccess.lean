import Integration.SlhDsaShakePermutationCompletion

namespace Reduction.ShakePermutation.Completion
open MLink SLHDSA ShakeXof Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
variable (S : Sha2Set) {N T : ℕ} (cap : blockCap N ≤ T)

noncomputable def row (xs : List Rate) : Option (ShakeApi.Input N) :=
  if h : xs.length ≤ T then locate (address cap) (BList.ofList xs h) else none

private theorem long_row (xs : List Rate) (long : blockCap N < xs.length) : row cap xs = none := by
  unfold row
  split
  · rename_i short
    cases hr : locate (address cap) (BList.ofList xs short) with
    | none => rfl
    | some x =>
      have eq := congrArg (fun t : Fix.Domain T => t.1.val) (located _ hr)
      change (messageBlocks (sp (List.ofFn x.2))).length = xs.length at eq
      simp only [messageBlocks_length,sp,List.length_map,List.length_ofFn] at eq
      have small := Nat.div_le_div_right (c:=136) (Nat.le_of_lt_succ x.1.isLt)
      unfold blockCap at long
      omega
  · rfl

noncomputable def access (g : Private T) : Fix.Access (ShakeApi.Input N) (Bytes S.vp.params.m) where
  addr xs := (row cap xs).getD (BList.ofList [] (by simp))
  decode xs y := if h : xs.length ≤ T then
    let v := g (BList.ofList xs h)
    equiv.symm ((row cap xs).elim v (fun _ => replaceHead v y)) else 0
  privateValue := Fix.extend (fun x => equiv.symm (g x))

/-- The simulator's external XOF is needed only on a valid padded byte input.
All unused output bytes and non-message paths come from the fixed private table. -/
theorem value_access (g : Private T) (H : ShakeApi.RawTable S N) :
    (access S cap g).value (blockCap N) H = Fix.extend (complete S cap g H) := by
  funext xs
  by_cases short : xs.length ≤ T
  · by_cases hit : xs.length ≤ blockCap N
    · simp only [Fix.Access.value,ite_eq_left hit,access,dite_eq_left short,Fix.extend,complete,write]
      simp only [row,dite_eq_left short]
      generalize locate (address cap) (BList.ofList xs short) = opt
      cases opt <;> simp only [Option.elim_none,Option.elim_some,Option.getD_some]
    · have hr := long_row cap xs (by omega)
      simp only [row,dite_eq_left short] at hr
      simp [Fix.Access.value,hit,access,Fix.extend,short,complete,write,hr]
  · have long : ¬xs.length ≤ blockCap N := fun h => short (h.trans cap)
    simp [Fix.Access.value,long,access,Fix.extend,short]

end Reduction.ShakePermutation.Completion
#print axioms Reduction.ShakePermutation.Completion.value_access
