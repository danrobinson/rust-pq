import Ideal.Realize.TcrCount
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport
attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets

abbrev Ph1 (n : ℕ) : Type := OracleComp (TcrP1Spec P₀ n) (TcrP1State Link.vp P₀)

theorem tcrPhase1_cap' (n : ℕ) (oa : Ph1 n) (hoa : oa = tcrPhase1 Link.vp P₀ n) :
    IsQueryBoundP oa (fun t => t.isRight = true) (tcrTargets Link.vp) := by
  delta tcrPhase1 at hoa
  generalize tcrChooseHF Link.vp P₀ = c at hoa
  subst hoa
  have h := routeHF_cap (PkSeed := P₀.PkSeed) (fun xs : List P₀.Y => xs.length = n)
    (tcrTargets Link.vp) c []
  rw [List.length_nil, Nat.sub_zero] at h
  exact h

theorem tcrPhase1_len' (n : ℕ) (oa : Ph1 n) (hoa : oa = tcrPhase1 Link.vp P₀ n) :
    IsQueryBoundP oa (fun t => bad1 (fun xs : List P₀.Y => xs.length = n) Bmax t = true) 0 := by
  delta tcrPhase1 at hoa
  generalize hc : tcrChooseHF Link.vp P₀ = c at hoa
  subst hoa
  exact routeHF_len (PkSeed := P₀.PkSeed) _ _ Bmax c
    (hc ▸ tcrChooseHF_len (vp := Link.vp) (prims := P₀) Bmax okLen_le) []

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)

theorem advT_choose : (advT S oR pkSeedDist n).choose =
    simulateQ embImpl (tcrPhase1 Link.vp P₀ n : Ph1 n) := by krfl

theorem advT_chooseBound : (advT S oR pkSeedDist n).ChooseBound 0 := by
  unfold TcrAdv.ChooseBound
  rw [advT_choose]
  generalize (tcrPhase1 Link.vp P₀ n : Ph1 n) = oa
  exact emb_noH (fun i => (F128T pkSeedDist n).isH i = true) (fun t => by
    rcases t with m | t <;> simp only [embIdx, THFam.isH] <;> decide) oa

theorem advT_chalBound : (advT S oR pkSeedDist n).ChalBound (tcrTargets Link.vp) := by
  unfold TcrAdv.ChalBound
  rw [advT_choose]
  generalize hoa : (tcrPhase1 Link.vp P₀ n : Ph1 n) = oa
  have h1 := tcrPhase1_cap' n oa hoa.symm
  refine emb_bound (fun i => (F128T pkSeedDist n).isChal i = true) oa _
    (IsQueryBoundP.of_imp (fun t ht => ?_) h1)
  rcases t with m | t
  · simp only [embIdx, THFam.isChal] at ht
    exact absurd ht (by decide)
  · rfl
end Ideal.Realize.Tcr
