import Integration.SlhDsaShakePermutationSparseBuckets
import Integration.SlhDsaShakePermutationSkFormat
import Integration.SlhDsaShakeXofTcr

/-! All one- and two-node inputs at a fixed public seed fit in a single
ordinary permutation call. Distinct tweaks and messages occupy distinct
formatted rows for each of the six SHAKE parameter sets. -/
namespace Reduction.ShakePermutation.SparsePort.Arity
open Classical MLink SLHDSA ShakeXof
variable (S : Sha2Set) (ar : ℕ) (pk : S.Node)
abbrev Msg := SetOracle.ArMsg S ar
abbrev Row := Bytes 32 × Msg S ar
def data (j : Row S ar) := thBytes S pk j.1 j.2.val

theorem single (j : Row S ar) (bound : ar ≤ 2) :
    messageBlocks (sp (data S ar pk j)) = [rateBlock (padded (sp (data S ar pk j))) 0] := by
  have n : S.vp.params.n ≤ 32 := by cases S <;> decide
  have k : S.vp.params.n*ar ≤ 32*2 := Nat.mul_le_mul n bound
  have lt : (sp (data S ar pk j)).length < 136 := by
    simp only [sp,List.length_map,data,thBytes,List.length_append,Vector.length_toList,MIdeal.Sha512.payload_length,j.2.property]
    omega
  unfold messageBlocks
  simp only [Nat.div_eq_of_lt lt,Nat.zero_add,List.ofFn_succ,List.ofFn_zero,Fin.val_cast,Fin.val_zero]

def input (bound : ar ≤ 2) : Row S ar ↪ Words where
  toFun j := join (rateBlock (padded (sp (data S ar pk j))) 0) 0
  inj' x y eq := by
    have hr := congrArg rateOf eq
    simp only [rate_join] at hr
    have same : messageBlocks (sp (data S ar pk x)) = messageBlocks (sp (data S ar pk y)) := by
      rw [single _ _ _ _ bound,single _ _ _ _ bound,hr]
    have byte := congrArg cv (messageBlocks_injective same)
    have row : data S ar pk x = data S ar pk y := by simpa [cv,sp,List.map_map,Function.comp_def] using byte
    obtain ⟨left,right⟩ := List.append_inj row (by simp)
    exact Prod.ext (Vector.toList_inj.mp (List.append_cancel_left left))
      (Subtype.ext (MIdeal.Sha512.payload_injective S right))

theorem fmt (a : Bytes 32) (xs : List S.Node) :
    sp (thBytes S pk a xs) = nd pk ++ nd a ++ nds xs := by
  have payload (l : List S.Node) : sp (Payload S l) = nds l := by
    induction l with
    | nil => rfl
    | cons v l ih => change sp (v.toList ++ Payload S l) = _; rw [sp_append,ih]; rfl
  rw [thBytes,sp_append,sp_append,payload]
  rfl

theorem hash_eq (bound : ar ≤ 2) (π : Permutation) (j : Row S ar) :
    (primitives (lanes π) S.vp.params).Thash pk j.1 j.2.val =
      (SkFormat.split S (π (input S ar pk bound j))).1 := by
  change hash (lanes π) (nd pk ++ nd j.1 ++ nds j.2.val) S.vp.params.n = _
  rw [← fmt S pk,← hash_prefix,answer_blocks,← head_eq_prefix (node_le_digest S)]
  rw [show thBytes S pk j.1 j.2.val = data S ar pk j from rfl,single _ _ _ _ bound]
  have st (r : Rate) : Fix.ordinary π [r] = π (join r 0) := by
    apply congrArg π
    apply congrArg₂ join _ rfl
    funext i
    exact UInt64.xor_zero
  rw [st,SkFormat.split_fst]
  change head _ (head _ (Completion.bytes (rateOf (π ((input S ar pk bound) j))))) = _
  apply Vector.ext; intro i hi; simp [head]

theorem row_bits (bound : ar ≤ 2) : Fintype.card (Row S ar) ≤ 2^768 := by
  have key : Fintype.card S.Node ≤ 2^256 := by
    change Fintype.card (Bytes _) ≤ _; rw [card_bytes']; cases S <;> decide +kernel
  have hm : Fintype.card (Msg S ar) = Fintype.card S.Node ^ ar := card_vector ar
  rw [Fintype.card_prod,hm,card_bytes']
  calc (256:ℕ)^32 * Fintype.card S.Node ^ ar ≤ 256^32 * (2^256)^2 := by gcongr; decide
       _ = _ := by decide +kernel

theorem bucket_bound (bound : ar ≤ 2) :
    Fintype.card {s : Row S ar → SkFormat.Suffix S // ¬ small s} * 2^384 ≤
      Fintype.card (Row S ar → SkFormat.Suffix S) := by
  apply bucket_risk (row_bits S ar bound)
  rw [SkFormat.card_suffix]; cases S <;> decide +kernel

end Reduction.ShakePermutation.SparsePort.Arity
#print axioms Reduction.ShakePermutation.SparsePort.Arity.hash_eq
#print axioms Reduction.ShakePermutation.SparsePort.Arity.bucket_bound
