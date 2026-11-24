import Integration.SlhDsaShakePermutationSparseSelect
import Ideal.Realize.Phase1

/-! A phase-one query budget for the actual memoised TCR reduction.
The router caps all target/collection calls together and the structure
walk emits lists of at most 67 nodes, hence at most 17 blocks each. -/
namespace Reduction.ShakePermutation.SparsePort.Select
open Classical OracleComp OracleSpec SLHDSA MLink PQ.Interactive Ideal.Realize Phase

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] tcrTargets arityTargets

private theorem wcount_absorb (d : Bytes 32) (rs : List Rate) (w : Words) :
    WCount (fun i => if i.isRight = true then 1 else 0)
      (simulateQ erase (Phase.absorb d w rs)) rs.length := by
  induction rs generalizing w with
  | nil => simp only [Phase.absorb,simulateQ_pure]; trivial
  | cons r rs ih =>
    simp only [Phase.absorb,simulateQ_bind,simulateQ_spec_query,erase,wCount_query_bind]
    exact ⟨by simp,fun y => by simpa using ih y⟩

variable (S : Sha2Set) (ar : ℕ)
abbrev wt (i : Trace.Fwd.Domain) := if i.isRight = true then 1 else 0

theorem hash_cost (pk : S.Node) (d : Bytes 32) (xs : List S.Node) (hl : xs.length ≤ 67) :
    WCount wt (simulateQ erase (evalHash S pk d xs)) 17 := by
  have cap : (messageBlocks (sp (ShakeXof.thBytes S pk d xs))).length ≤ 17 := by
    rw [messageBlocks_length]
    have n : S.vp.params.n ≤ 32 := by cases S <;> decide
    have m := Nat.mul_le_mul n hl
    simp only [sp,List.length_map,ShakeXof.thBytes,List.length_append,Vector.length_toList,MIdeal.Sha512.payload_length]
    omega
  simp only [evalHash,simulateQ_bind,simulateQ_pure]
  exact (WCount.bind (wcount_absorb _ _ _) (m:=0) (fun _ => wCount_pure _ _ _)).mono (by simpa using cap)

def tooLong (i : (Spec S ar).Domain) :=
  bad1 (fun x : List S.Node => x.length = ar) 67 i

private theorem step_cost (pk : S.Node) (i : (Spec S ar).Domain) (s : History S ar)
    (good : tooLong S ar i ≠ true) :
    WCount wt (simulateQ erase ((handler S ar pk i).run s)) (if i.isRight then 17 else 0) := by
  obtain ⟨l,c⟩ := s
  rcases i with n|tm|t
  · simp only [handler,StateT.run_mk,simulateQ_bind,simulateQ_spec_query,erase,simulateQ_pure,wCount_query_bind]
    exact ⟨by exact Nat.zero_le 0,fun _ => trivial⟩
  · have len : tm.2.val.length ≤ 67 := by by_contra! hh; exact good (by simpa [tooLong,bad1] using hh)
    change WCount wt (simulateQ erase (if _ then _ else _)) 17
    split
    · rw [simulateQ_pure]; trivial
    · simp only [simulateQ_bind,simulateQ_pure]
      exact WCount.bind (m := 0) (hash_cost S pk _ _ len) (fun _ => wCount_pure _ _ 0)
  · have len : t.2.2.length ≤ 67 := by by_contra! hh; exact good (by simpa [tooLong,bad1] using hh)
    change WCount wt (simulateQ erase (if _ then _ else _)) 17
    split
    · rw [simulateQ_pure]; trivial
    · simp only [simulateQ_bind,simulateQ_pure]
      exact WCount.bind (m := 0) (hash_cost S pk _ _ len) (fun _ => wCount_pure _ _ 0)

theorem select_cost {A : Type} (pk : S.Node) (P : OracleComp (Spec S ar) A) (s : History S ar)
    (Q : ℕ) (q : IsQueryBoundP P (fun i => i.isRight = true) Q)
    (len : IsQueryBoundP P (fun i => tooLong S ar i = true) 0) :
    WCount wt (simulateQ erase (prog S ar pk P s)) (17*Q) := by
  induction P using OracleComp.inductionOn generalizing Q s with
  | pure x => simp [prog,wCount_pure]
  | query_bind i k ih =>
    rw [isQueryBoundP_query_bind_iff] at q len
    have good := len.1.resolve_right (Nat.lt_irrefl 0)
    have small (r) := len.2 r
    simp only [ite_eq_right good] at small
    simp only [prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    have each := WCount.bind (step_cost S ar pk i s good)
      (fun z => ih z.1 z.2 _ (q.2 z.1) (small z.1))
    exact each.mono (by split_ifs <;> simp_all; omega)

noncomputable def choice (base : ShakeApi.Xof S) : OracleComp (Spec S ar)
    (Open.TcrP1State S.vp (ShakeApi.primitives S base)) :=
  Open.tcrPhase1 S.vp (ShakeApi.primitives S base) ar

set_option linter.constructorNameAsVariable false in
theorem choice_cap (base : ShakeApi.Xof S) :
    IsQueryBoundP (choice S ar base) (fun i => i.isRight = true) (tcrTargets S.vp) := by
  let p := ShakeApi.primitives S base
  let c := Open.tcrChooseHF S.vp p
  let test := fun xs : List S.Node => xs.length = ar
  have h := routeHF_cap (PkSeed:=p.PkSeed) test (tcrTargets S.vp) c []
  rw [List.length_nil,Nat.sub_zero] at h
  kexact h

theorem choice_len (base : ShakeApi.Xof S) :
    IsQueryBoundP (choice S ar base) (fun i => tooLong S ar i = true) 0 := by
  let p := ShakeApi.primitives S base
  let c := Open.tcrChooseHF S.vp p
  let test := fun xs : List S.Node => xs.length = ar
  have length (xs : List S.Node) (h : OkLen S.vp xs) : xs.length ≤ 67 := by
    have a : S.vp.params.len ≤ 67 := by cases S <;> decide
    have b : S.vp.params.k ≤ 67 := by cases S <;> decide
    rcases h with h|h|h|h <;> omega
  kexact routeHF_len (PkSeed:=p.PkSeed) test (tcrTargets S.vp) 67 c
    (tcrChooseHF_len (vp:=S.vp) (prims:=p) 67 length) []

attribute [local irreducible] choice

theorem native_cost (pk : S.Node) (base : ShakeApi.Xof S) :
    CountBound (fun i => i.isRight = true) (simulateQ erase (prog S ar pk
      (choice S ar base) ([],[]))) (17*tcrTargets S.vp) := by
  apply (countBound_iff_wCount _ _ _).2
  exact select_cost S ar pk _ _ _ (choice_cap S ar base) (choice_len S ar base)

theorem benchmark_calls : 17*tcrTargets S.vp ≤ 2^100 := by rw [← Resources.structHashEvals_eq_tcrTargets]; cases S <;> decide +kernel

end Reduction.ShakePermutation.SparsePort.Select
#print axioms Reduction.ShakePermutation.SparsePort.Select.native_cost
#print axioms Reduction.ShakePermutation.SparsePort.Select.benchmark_calls
