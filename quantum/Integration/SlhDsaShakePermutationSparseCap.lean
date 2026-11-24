import Integration.SlhDsaShakePermutationSparseSelectCost
import Integration.SlhDsaShakePermutationSparseMemo
import Integration.SlhDsaShakePermutationSparseTcr

/-! Agreement of capped and ordinary tweakable hashes at every allowed
challenge or collection read made by the native memoised class selector. -/
namespace Reduction.ShakePermutation.SparsePort.Memo
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash
open ShakeApi (Xof RawTable extend)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] arityTargets tcrTargets Select.choice
set_option maxRecDepth 12000
set_option maxHeartbeats 1750000
variable (S : Sha2Set) (ar : ℕ) (seeds : ProbComp S.Node)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "tab" => SkCost.table S N
local notation "pr" => fun π : Permutation => ShakeApi.primitives S (extend (tab (oracle π)))
local notation "rpr" => fun π : Permutation => primitives (lanes π) S.vp.params
def cappedGame (π : Permutation) := thashArityProblemT S.vp (pr π) seeds ar

theorem short (π : Permutation) (pk : S.Node) (d : Bytes 32) (xs : List S.Node) (hl : xs.length ≤ 67) :
    (pr π).Thash pk d xs = (rpr π).Thash pk d xs := by
  let w := pk.toList ++ d.toList ++ (xs.map Vector.toList).flatten
  have hw : w.length ≤ N := (ShakeApi.in_range S 67 65536 N le_rfl).1 pk d xs hl
  change prefixBytes S.vp.params.n (extend (tab (oracle π)) w) = _
  rw [SkCost.table,ShakeApi.extend_restrict _ _ _ _ hw]
  change prefixBytes S.vp.params.n (answer S (lanes π) w) = hash (lanes π) (nd pk ++ nd d ++ nds xs) S.vp.params.n
  rw [hash_prefix]
  simp only [w,sp_append,flatten_nodes]
  rfl

def interp (op : S.Node → Bytes 32 → List S.Node → S.Node) (pk : S.Node) :
    QueryImpl (Select.Spec S ar) (StateT (Select.History S ar) ProbComp) :=
  SM_DT_TCR_oracles (tcrWithEval (ShakeXof.Arity.base S ar seeds)
    (fun p d m => op p d m.val) (fun _ p d xs => op p d xs)) pk

private theorem interp_same (f g : S.Node → Bytes 32 → List S.Node → S.Node) (pk : S.Node)
    (agree : ∀ d xs, xs.length ≤ 67 → f pk d xs = g pk d xs) (i : (Select.Spec S ar).Domain)
    (s : Select.History S ar) (good : Select.tooLong S ar i ≠ true) :
    (interp S ar seeds f pk i).run s = (interp S ar seeds g pk i).run s := by
  obtain ⟨l,c⟩ := s
  rcases i with n|tm|t
  · rfl
  · have len : tm.2.val.length ≤ 67 := by by_contra! ht; exact good (by simpa [Select.tooLong,Ideal.Realize.bad1] using ht)
    change (SM_DT_TCR_challengeOracle _ pk tm).run (l,c) = (SM_DT_TCR_challengeOracle _ pk tm).run (l,c)
    by_cases h : arityTargets S.vp ar ≤ l.length ∨ ¬TweakFresh Prod.fst l c tm.1 <;>
      simp [SM_DT_TCR_challengeOracle,ShakeXof.Arity.base,h,agree _ _ len]
  · have len : t.2.2.length ≤ 67 := by by_contra! ht; exact good (by simpa [Select.tooLong,Ideal.Realize.bad1] using ht)
    let C (op : S.Node → Bytes 32 → List S.Node → S.Node) : TweakableHashCollection Unit S.Node (Bytes 32) S.Node :=
      ⟨fun _ => List S.Node,fun _ => op⟩
    change (collectionOracle (Q := Bytes 32 × Arity.Msg S ar) Prod.fst (C f) pk t).run (l,c) =
      (collectionOracle Prod.fst (C g) pk t).run (l,c)
    by_cases h : TweakReserved (Q := Bytes 32 × Arity.Msg S ar) Prod.fst l t.2.1 <;>
      simp [collectionOracle,C,h,agree t.2.1 t.2.2 len]

theorem choose_same {D : Type} (π : Permutation) (pk : S.Node) (p : OracleComp (Select.Spec S ar) D)
    (s : Select.History S ar) (len : IsQueryBoundP p (fun i => Select.tooLong S ar i = true) 0) :
    (simulateQ (interp S ar seeds (pr π).Thash pk) p).run s =
      (simulateQ (interp S ar seeds (rpr π).Thash pk) p).run s := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure x => simp only [simulateQ_pure,StateT.run_pure]
  | query_bind i k ih =>
    rw [isQueryBoundP_query_bind_iff] at len
    have hi := len.1.resolve_right (Nat.lt_irrefl 0)
    simp only [ite_eq_right hi] at len
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
      interp_same S ar seeds _ _ pk (short S π pk) i s hi]
    apply bind_congr
    rintro ⟨v,s'⟩
    exact ih v s' (len.2 v)

end Reduction.ShakePermutation.SparsePort.Memo
#print axioms Reduction.ShakePermutation.SparsePort.Memo.choose_same
