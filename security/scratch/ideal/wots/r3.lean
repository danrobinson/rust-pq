import Ideal.Realize.WotsRealize

/-!
# The six WOTS-chain realisers and their parameter bounds

* `realizesUd`, `realizesPre`, `realizesWotsTcr` (SUF: the families at `S.typedS (optRandU oR)`)
  and `realizesUdE`, `realizesPreE`, `realizesWotsTcrE` (EUF: at `S.typedE (optRandU oR)`), with
  parameters `pU qf qs ℓ`, `pP qf qs ℓ`, `pW qf qs ℓ`, under the four forger hypotheses
  (`qf` compression queries, `qs` signing queries, signed and forged messages of at most `ℓ`
  bytes).
* `pU_le`, `pP_le`, `pW_le`: `P5.Le` at `QcW qf qs ℓ = qf + 11·(121857·qs + 146514) +
  (qs + 2)·((ℓ + 56)/64 + 3)` and `NW = 1062560399506556770327551 (≈ 2^79.81)`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Wots

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-! ## Embedded first phases: generic counts -/

section GenF

variable {PkSeed Tweak M Y ι : Type} {α : Type}

theorem genP_q1 (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + F.collS)) α) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_PRE_challengeSpec Tweak Y + F.collS)) oa)
      (fun i => F.pIsH i = true) 0 :=
  emb_noH _ (fun t => by rcases t with n | t <;> simp [embIdx, THFam.pIsH]) oa

theorem genP_chal (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + F.collS)) α) (n : ℕ)
    (h : IsQueryBoundP oa isChalI n) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_PRE_challengeSpec Tweak Y + F.collS)) oa)
      (fun i => F.pIsChal i = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isChalI, THFam.pIsChal]) h)

theorem genP_coll (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + F.collS)) α) (n : ℕ)
    (h : IsQueryBoundP oa isColl n) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_PRE_challengeSpec Tweak Y + F.collS)) oa)
      (fun i => F.pIsColl i = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isColl, THFam.pIsColl]) h)

theorem genT_q1 (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) α) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) oa)
      (fun i => F.isH i = true) 0 :=
  emb_noH _ (fun t => by rcases t with n | t <;> simp [embIdx, THFam.isH]) oa

theorem genT_chal (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) α) (n : ℕ)
    (h : IsQueryBoundP oa isChalI n) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) oa)
      (fun i => F.isChal i = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isChalI, THFam.isChal]) h)

theorem genT_coll (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) α) (n : ℕ)
    (h : IsQueryBoundP oa isColl n) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) oa)
      (fun i => F.isColl i = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isColl, THFam.isColl]) h)

end GenF

/-- A collection query with at most `Lw` blocks after the first (or no collection query). -/
def lenOk {T : Type} : ℕ ⊕ ((St × Blk) ⊕ (T ⊕ ((_ : Unit) × Bytes 22 × List (Bytes 16)))) → Prop
  | .inr (.inr (.inr q)) => (tblocks q.2.1 q.2.2).2.length ≤ Lw
  | _ => True

noncomputable instance {T : Type} : DecidablePred (lenOk (T := T)) :=
  fun _ => Classical.propDecidable _

/-- Collection lengths of an embedded first phase whose collection queries are SLH-DSA hash
calls. -/
theorem emb_okLen {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × Bytes 22 × List (Bytes 16)))}
    {α : Type} (oa : OracleComp (unifSpec + X) α)
    (h : @IsQueryBoundP _ (unifSpec + X) _ oa (badG (vp := Link.vp) (prims := P0) (T := T))
      instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0) :
    AllQueriesSatisfy (simulateQ (embImpl (X := X)) oa) (lenOk (T := T)) := by
  refine (isQueryBoundP_zero_iff _ _).1 (emb_bound _ oa 0 ?_)
  refine @IsQueryBoundP.of_imp _ _ _ _ (fun t => ¬ lenOk (embIdx t))
    (badG (vp := Link.vp) (prims := P0) (T := T)) _
    instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 (fun t ht => ?_) h
  rcases t with n | t | q
  · exact (ht trivial).elim
  · exact (ht trivial).elim
  · intro hb
    exact ht (tblocks_okLen _ _ hb)

/-! ## The challenge / collection counts as named constants

(Named so that the kernel, comparing a realiser's parameter with a count lemma, unfolds the name
instead of evaluating `wotsQc Link.vp` or `(wotsInsts Link.vp).length` as a numeral.) -/

/-- Challenge queries of the SM-UD and SM-PRE first phases: `#inst · len`. -/
irreducible_def chU : ℕ := (wotsInsts Link.vp).length * (Link.vp.params.len * 1)
/-- Collection queries of the SM-UD and SM-PRE first phases: `wotsQc + #inst · len · (w-1)`. -/
irreducible_def collU : ℕ :=
  wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1))
/-- Challenge queries of the SM-TCR first phase: `#inst · len · (w-1)`. -/
irreducible_def chW : ℕ := (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1))
/-- Collection queries of the SM-TCR first phase: `wotsQc + #inst · len`. -/
irreducible_def collW : ℕ := wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * 1)

/-! ## SM-UD -/

section Ud

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

theorem udAdv_q1 : (udAdv S oR pkSeedDist).PickBound 0 :=
  genP_q1 (FWotsPre128 pkSeedDist) _

theorem udAdv_chal : (udAdv S oR pkSeedDist).ChalBound chU := by
  rw [chU_def]
  exact   genP_chal (FWotsPre128 pkSeedDist) _ _ (rUd_pick_chal pkSeedDist (dF oR pkSeedDist))

theorem udAdv_coll : (udAdv S oR pkSeedDist).CollBound collU := by
  rw [collU_def]
  exact   genP_coll (FWotsPre128 pkSeedDist) _ _ (rUd_pick_coll pkSeedDist (dF oR pkSeedDist))

end Ud
end Ideal.Realize.Wots
