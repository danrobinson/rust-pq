import Integration.SlhDsaShakePermutationMsgTrajectory

namespace Reduction.ShakePermutation.MsgTrajectory
open MLink SLHDSA SLHDSA.Security ShakeXof Classical ENNReal
set_option maxRecDepth 8192
variable (S : Sha2Set)

private def restBytes (rand : S.Node) (m : List SLHDSA.Byte) : Spec.Bytes :=
  nd rand ++ sp m ++ Reduction.ShakePermutation.suffix ((2*S.vp.params.n+m.length)%136)

private theorem layout (k rand : S.Node) (m : List SLHDSA.Byte) :
    padded (sp (raw S k rand m)) = nd k ++ restBytes S rand m := by
  simp only [padded,raw,List.map_append,Nat.add_assoc,restBytes,nd,sp,List.length_map,List.length_append,
    Vector.length_toList,List.append_assoc,two_mul]

def firstBlock (k rand : S.Node) (m : List SLHDSA.Byte) : Rate :=
  rateBlock (padded (sp (raw S k rand m))) 0

def laterBlocks (rand : S.Node) (m : List SLHDSA.Byte) : List Rate :=
  List.ofFn (fun i : Fin ((2*S.vp.params.n+m.length)/136) =>
    rateBlock (padded (sp (raw S (0 : S.Node) rand m))) (i.val+1))

/-- Key bytes occur only in the first rate block, including at padding
boundaries. The suffix is a function of public inputs alone. -/
theorem split_blocks (k rand : S.Node) (m : List SLHDSA.Byte) :
    messageBlocks (sp (raw S k rand m)) = firstBlock S k rand m :: laterBlocks S rand m := by
  have len : (sp (raw S k rand m)).length = 2*S.vp.params.n+m.length := by simp [sp,raw,two_mul,Nat.add_assoc]
  simp only [messageBlocks,len,List.ofFn_succ,firstBlock,laterBlocks,Fin.val_cast,Fin.val_zero,List.cons.injEq,true_and]
  apply congrArg List.ofFn
  funext i j
  simp only [layout,rateBlock,Fin.val_succ]
  congr 1
  funext z
  have n : S.vp.params.n ≤ 136 := by cases S <;> decide
  have idx : S.vp.params.n ≤ 136*(i.val+1)+8*j.val+z.val := by omega
  have skip (k' : S.Node) : (nd k').length ≤ 136*(i.val+1)+8*j.val+z.val := by simpa [nd,sp] using idx
  rw [List.getElem?_append_right (skip k),List.getElem?_append_right (skip 0)]
  simp [nd,sp]

theorem first_key (k rand : S.Node) (m : List SLHDSA.Byte) :
    (SkFormat.split S (join (firstBlock S k rand m) 0)).1 = k := by
  rw [SkFormat.split_fst,rate_join]
  apply Vector.ext
  intro i hi
  simp only [head,Completion.bytes,Vector.getElem_ofFn,firstBlock,blockByte_rateBlock,layout,
    Nat.mul_zero,Nat.zero_add]
  rw [List.getElem?_append_left (by simpa [nd,sp] using hi)]
  simp [nd,sp,hi]

theorem random_image {A : Type} [Fintype A] [DecidableEq A] (x : A) (f : A → ℝ≥0∞) :
    SetOracle.uniformMean (fun π : Equiv.Perm A => f (π x)) = SetOracle.uniformMean f := by
  let _ : Nonempty A := ⟨x⟩
  have same (v : A) : SetOracle.uniformMean (fun π : Equiv.Perm A => f (π x)) =
      SetOracle.uniformMean (fun π : Equiv.Perm A => f (π v)) := by
    let e := Equiv.mulRight (Equiv.swap x v)
    have h := Classic.mean_equiv e (fun π => f (π v))
    change SetOracle.uniformMean (fun π : Equiv.Perm A => f (π (Equiv.swap x v v))) = _ at h
    rwa [Equiv.swap_apply_right] at h
  have const {B : Type} [Nonempty B] [Fintype B] (c : ℝ≥0∞) :
      SetOracle.uniformMean (fun _ : B => c) = c := by
    simp only [SetOracle.uniformMean,← Finset.sum_mul,sum_unifW,one_mul]
  calc
    _ = SetOracle.uniformMean (fun _ : A => SetOracle.uniformMean (fun π : Equiv.Perm A => f (π x))) := (const _).symm
    _ = SetOracle.uniformMean (fun v : A => SetOracle.uniformMean (fun π : Equiv.Perm A => f (π v))) :=
      congrArg SetOracle.uniformMean (funext same)
    _ = SetOracle.uniformMean (fun π : Equiv.Perm A => SetOracle.uniformMean (fun v : A => f (π v))) := by
      simp only [SetOracle.uniformMean,Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm ..
    _ = _ := by simp_rw [Classic.mean_equiv]; exact const _

/-- Replacing only the first permutation call by an independent uniform
permutation makes the whole padded message PRF output exactly uniform.
The public permutation, signing input and test can all be fixed first. -/
theorem independent_round (π : Permutation) (k rand : S.Node) (m : List SLHDSA.Byte)
    (test : S.Node → ℝ≥0∞) :
    SetOracle.uniformMean (fun σ : Permutation =>
      test (SkFormat.split S (suffix π (laterBlocks S rand m) (σ (join (firstBlock S k rand m) 0)))).1) =
      SetOracle.uniformMean test := by
  exact (random_image (join (firstBlock S k rand m) 0) (fun w => test (SkFormat.split S (suffix π (laterBlocks S rand m) w)).1)).trans (independent_first S π (laterBlocks S rand m) test)

end Reduction.ShakePermutation.MsgTrajectory
#print axioms Reduction.ShakePermutation.MsgTrajectory.split_blocks
#print axioms Reduction.ShakePermutation.MsgTrajectory.first_key
#print axioms Reduction.ShakePermutation.MsgTrajectory.independent_round
