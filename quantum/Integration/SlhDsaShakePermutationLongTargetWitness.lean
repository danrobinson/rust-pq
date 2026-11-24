import Integration.SlhDsaShakePermutationLongTargetGrowth
import Integration.SlhDsaShakePermutationItsrWitness

/-! A verified second preimage yields a recorded target hit after replaying
its actual ordinary absorption trace. Complete known cells may uniformly
be substituted for the recording database in this implication. -/
namespace Reduction.ShakePermutation.ItsrLabel.Target
open Classical Tails MLink SLHDSA
noncomputable section
set_option maxRecDepth 11000
set_option maxHeartbeats 1400000

theorem good_of_clear {S π L goal k k' h} (graph : Graph.Good (layout π) k k')
    (no : ∀ (path : List Rate) pre z y, path.length ≤ L → Relabel.run π k k' path.reverse = some (pre,z) →
      h z = some y → goal path ≠ some (digest S pre y)) : Good S π L goal k k' h :=
  ⟨graph,fun p pre z y => no (List.ofFn p.2) pre z y
    (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ p.1.isLt)⟩

theorem result_digest (S : Sha2Set) (p : Report) : (SkFormat.split S (result p)).1 = digest S p.pre p.head := by
  rw [SkFormat.split_fst]
  simp only [digest,result,rate_join]

theorem replay_overwrite (π : Permutation) (H : Table) (xs : List Rate) :
    (replay π H xs).path.reverse = Fix.fix (rateOf ∘ Fix.overwrite (perm π H)) xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change ((rateXor b (rateOf (result (replay π H bs))))::(replay π H bs).path).reverse = _
    rw [List.reverse_cons,List.reverse_cons,Fix.fix_append,ih]
    congr 1
    cases bs with
    | nil =>
      simp only [Fix.fix_nil,Fix.maskNext,List.reverse_nil,List.isEmpty_nil,ite_true,replay,empty,result,rate_join]
      congr 1
      funext i
      simp [rateXor]
    | cons a bs =>
      simp only [Fix.maskNext,Fix.fix_empty,List.isEmpty_reverse,List.isEmpty_cons,Bool.false_eq_true,ite_false,Function.comp_apply]
      rw [replay_result,Fix.fixed_absorption]

theorem certify (S : Sha2Set) (π : Permutation) (H : Table) (L : ℕ) (goal : Goal S) (D : Bank) (xs : List Rate)
    (ne : xs ≠ []) (len : xs.length ≤ L) (mem : Matches D (replay π H xs.reverse).log)
    (target : goal (Fix.fix (rateOf ∘ Fix.overwrite (perm π H)) xs) =
      some ((SkFormat.split S (Fix.ordinary (perm π H) xs)).1)) :
    label S π L goal D = false := by
  let r := replay π H xs.reverse
  have bound : r.path.reverse.length ≤ L := by
    simpa only [r,List.length_reverse,(replay_length π H xs.reverse).2] using len
  let p := BList.ofList r.path.reverse bound
  have report : List.ofFn p.2 = r.path.reverse := List.ofFn_get _
  have hit := logged π H D xs.reverse mem
  have nrev : xs.reverse ≠ [] := by simpa only [ne_eq,List.reverse_eq_nil_iff] using ne
  have head : held D r.cap = some r.head := hit.2 nrev
  have vis : Relabel.visit π (masks D false) (masks D true) p = some (r.pre,r.cap) := by
    simpa only [Relabel.visit,report,List.reverse_reverse] using hit.1
  have ow := replay_overwrite π H xs.reverse
  have re := replay_result π H xs.reverse
  rw [List.reverse_reverse] at ow re
  apply decide_eq_false
  intro good
  apply good.2 p r.pre r.cap r.head vis head
  rw [report]
  change goal (replay π H xs.reverse).path.reverse = _
  rw [ow,target,← re,result_digest]

end
end Reduction.ShakePermutation.ItsrLabel.Target
#print axioms Reduction.ShakePermutation.ItsrLabel.Target.certify
