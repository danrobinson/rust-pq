import Integration.SlhDsaShakePermutationCost
import Integration.SlhDsaShakeApiRaw

/-! Type-correct interface between the byte XOF and the Keccak permutation
experiments. Evaluating the sponge on either side gives the same honest calls. -/
namespace Reduction.ShakePermutation
open Spec.Keccak MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive

def answer (S : Sha2Set) (p : State → State) : ShakeApi.Xof S :=
  fun x => hash p (sp x) S.vp.params.m

private theorem squeeze_prefix (p : State → State) (a : State) (pos n m : Nat) (h : n ≤ m) :
    (squeeze p a pos m).take n = squeeze p a pos n := by
  induction n generalizing a pos m with
  | zero => rfl
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [squeeze,List.take_succ_cons]
      congr 1
      exact ih _ _ _ (by omega)

theorem hash_prefix (S : Sha2Set) (p : State → State) (x : List SLHDSA.Byte) :
    prefixBytes S.vp.params.n (answer S p x) = hash p (sp x) S.vp.params.n := by
  have h : S.vp.params.n ≤ S.vp.params.m := by cases S <;> decide
  apply Vector.toList_inj.mp
  rw [toList_prefixBytes_of_le h]
  change (cv (xof p (sp x) S.vp.params.m)).take _ = cv (xof p _ _)
  unfold cv
  rw [← List.map_take]
  exact congrArg _ (squeeze_prefix p _ _ _ _ h)

private theorem flatten_nodes {n : Nat} (xs : List (Bytes n)) :
    sp (xs.map Vector.toList).flatten = nds xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change sp (x.toList ++ (xs.map Vector.toList).flatten) = nd x ++ nds xs
    rw [sp_append, ih]
    rfl

theorem primitives_as_xof (S : Sha2Set) (p : State → State) :
    ShakeApi.primitives S (answer S p) = primitives p S.vp.params := by
  have th (pk : S.Node) (k : Bytes 32) (xs : List S.Node) :
      prefixBytes S.vp.params.n (answer S p (pk.toList ++ k.toList ++ (xs.map Vector.toList).flatten)) =
        hash p (nd pk ++ nd k ++ nds xs) S.vp.params.n := by
    rw [hash_prefix,sp_append,sp_append,flatten_nodes]
    rfl
  have pr (pk sk : S.Node) (a : Adrs) :
      prefixBytes S.vp.params.n (answer S p (pk.toList ++ a.toVector.toList ++ sk.toList)) =
        hash p (nd pk ++ nd a.toVector ++ nd sk) S.vp.params.n := by
    rw [hash_prefix,sp_append,sp_append]
    rfl
  have pm (sk rand : S.Node) (m : List SLHDSA.Byte) :
      prefixBytes S.vp.params.n (answer S p (sk.toList ++ rand.toList ++ m)) =
        hash p (nd sk ++ nd rand ++ sp m) S.vp.params.n := by
    rw [hash_prefix,sp_append,sp_append]
    rfl
  have hm (r pk root : S.Node) (m : List SLHDSA.Byte) :
      answer S p (r.toList ++ pk.toList ++ root.toList ++ m) =
        hash p (nd r ++ nd pk ++ nd root ++ sp m) S.vp.params.m := by
    simp only [answer,sp_append]
    rfl
  unfold ShakeApi.primitives
  rw [funext fun k => funext fun a => funext fun x => th k a x,
    funext fun r => funext fun k => funext fun root => funext fun m => hm r k root m,
    funext fun k => funext fun sk => funext fun a => pr k sk a,
    funext fun sk => funext fun r => funext fun m => pm sk r m]
  rfl

theorem answer_cost (S : Sha2Set) (xs : List SLHDSA.Byte) :
    EvalCost (fun H => pure (answer S (forward H) xs)) (xs.length / 136 + 1) := by
  simpa only [answer,sp,List.length_map] using hash_cost (sp xs) _ (output_sizes S).2

/-- One full hash request under the common benchmark input cap, for all six
sets. The longest accepted request requires 483 permutation calls. -/
theorem benchmark_answer_cost (S : Sha2Set) (xs : List SLHDSA.Byte)
    (hx : xs.length ≤ ShakeApi.rawCap S 67 65536) :
    EvalCost (fun H => pure (answer S (forward H) xs)) 483 := by
  apply (answer_cost S xs).mono
  have h : ShakeApi.rawCap S 67 65536 / 136 + 1 = 483 := by cases S <;> decide
  omega

end Reduction.ShakePermutation

#print axioms Reduction.ShakePermutation.primitives_as_xof
#print axioms Reduction.ShakePermutation.benchmark_answer_cost
