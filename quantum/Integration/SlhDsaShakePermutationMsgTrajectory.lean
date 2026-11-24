import Integration.SlhDsaShakePermutationSkFormat
import Integration.SlhDsaShakePermutationClassicalIdeal

namespace Reduction.ShakePermutation.MsgTrajectory
open MLink SLHDSA SLHDSA.Security ShakeXof Classical ENNReal
noncomputable section

def absorbBlock (r : Rate) : Equiv.Perm Words :=
  Function.Involutive.toPerm (fun s => join (rateXor r (rateOf s)) (capOf s)) (by
    intro s
    simp only [rate_join,cap_join]
    have e : rateXor r (rateXor r (rateOf s)) = rateOf s := by
      funext i; simp [rateXor,← UInt64.xor_assoc]
    rw [e,join_split])

/-- After the keyed first absorption, every suffix of rate blocks acts
bijectively on the full sponge state, even for a fixed permutation. -/
def suffix (π : Permutation) : List Rate → Permutation
  | [] => Equiv.refl _
  | b::bs => ((absorbBlock b).trans π).trans (suffix π bs)

theorem suffix_eval (π : Permutation) (rs : List Rate) (s : Words) :
    suffix π rs s = rs.foldl (fun w b => π (join (rateXor b (rateOf w)) (capOf w))) s := by
  induction rs generalizing s with
  | nil => rfl
  | cons b bs ih => exact ih _

theorem ordinary_cons (π : Permutation) (b : Rate) (bs : List Rate) :
    Fix.ordinary π (b::bs) = suffix π bs (π (join b 0)) := by
  rw [suffix_eval]
  unfold Fix.ordinary
  have z : rateXor b (rateOf 0) = b := by funext i; exact UInt64.xor_zero
  simp only [List.foldl_cons,z]
  rfl

def raw (S : Sha2Set) (k rand : S.Node) (m : List SLHDSA.Byte) := k.toList ++ rand.toList ++ m

theorem byte_prf (S : Sha2Set) (π : Permutation) (k rand : S.Node) (m : List SLHDSA.Byte)
    (b : Rate) (bs : List Rate) (path : messageBlocks (sp (raw S k rand m)) = b::bs) :
    (primitives (lanes π) S.vp.params).PRFmsg k rand m =
      (SkFormat.split S (suffix π bs (π (join b 0)))).1 := by
  change hash (lanes π) (nd k ++ nd rand ++ sp m) S.vp.params.n = _
  have layout : sp (raw S k rand m) = nd k ++ nd rand ++ sp m := by simp only [raw,sp_append,List.append_assoc]; rfl
  rw [← layout,← hash_prefix,answer_blocks,path,ordinary_cons,SkFormat.split_fst,
    ← head_eq_prefix (node_le_digest S)]
  apply Vector.ext; intro i hi; simp [head]

/-- The final PRF_msg output is exactly uniform if the first state is
independently uniform after the choice of the message and permutation. -/
theorem independent_first (S : Sha2Set) (π : Permutation) (bs : List Rate) (test : S.Node → ℝ≥0∞) :
    SetOracle.uniformMean (fun w : Words => test (SkFormat.split S (suffix π bs w)).1) =
      SetOracle.uniformMean test := by
  let e := (suffix π bs).trans (SkFormat.split S)
  have h := Classic.mean_equiv e (fun s => test s.1)
  apply h.trans
  rw [Classic.mean_prod]
  apply congrArg SetOracle.uniformMean
  funext a
  simp only [SetOracle.uniformMean,← Finset.sum_mul,sum_unifW,one_mul]

end
end Reduction.ShakePermutation.MsgTrajectory
#print axioms Reduction.ShakePermutation.MsgTrajectory.byte_prf
#print axioms Reduction.ShakePermutation.MsgTrajectory.independent_first
