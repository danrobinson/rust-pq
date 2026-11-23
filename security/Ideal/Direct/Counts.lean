import Ideal.Direct.Tagged
import Ideal.Realize.PrfReal

/-!
# Query counts of the tagged programs (D1 of `status/DIRECT.md`, counts)

* `qb_of_untag`: a query bound of the untagged program is a query bound of the tagged program
  for the pulled-back predicate (untagging maps queries one to one).
* `progS_comp`, `progE_comp`: the entry programs make at most `qPrf qf qs ℓ + 2·qOPrf qs`
  compression queries (the `PRF` realiser's compression count, plus two compression queries for
  each of its `PRF`-oracle queries).
* `progTS_all`, `progTE_all`: the same bound for **all** tagged queries (tags `F`, `H`, `V`
  together) of the tagged programs.  This is the cell budget `Q` of the collision term.
* `progTS_V`, `progTE_V`: the queries tagged `V` (the final check) are at most
  `(1 + verifyHashes)·thashCost thB + hmsgCost ℓ`, a constant plus the message length
  (`chkV_le`: `≤ 43219 + (ℓ + 56)/64 + 3` at SHA2-128s).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Ideal.Direct

open Ideal.Realize.Prf Reduction Reduction.Open
open Ideal.Realize.Msg (thB)
open Ideal.Realize (PortForgerProg isPortQ isSignQ isLongQ)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Untagging -/

/-- The untagged index of a tagged query. -/
def untagIdx : TSpec.Domain → (unifSpec + hS St Blk).Domain
  | .inl n => .inl n
  | .inr tq => .inr tq.2

/-- **Query bounds pull back through untagging.** -/
theorem qb_of_untag {α : Type} (p : (unifSpec + hS St Blk).Domain → Prop) [DecidablePred p]
    (X : OracleComp TSpec α) (n : ℕ) (h : IsQueryBoundP (simulateQ untagI X) p n) :
    IsQueryBoundP X (fun i => p (untagIdx i)) n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff]
    rw [simulateQ_query_bind] at h
    simp only [OracleQuery.input_query, monadLift_self] at h
    rcases t with m | tq
    · have h' := (isQueryBoundP_query_bind_iff (spec := unifSpec + hS St Blk) (p := p) (.inl m)
        (fun u => simulateQ untagI (k u)) n).1 h
      exact ⟨h'.1, fun u => ih u _ (h'.2 u)⟩
    · have h' := (isQueryBoundP_query_bind_iff (spec := unifSpec + hS St Blk) (p := p) (.inr tq.2)
        (fun u => simulateQ untagI (k u)) n).1 h
      exact ⟨h'.1, fun u => ih u _ (h'.2 u)⟩

/-! ## The entry programs -/

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

/-- `prfOI` costs one compression per compression query and two per `PRF` query. -/
theorem prfOI_step (k : Bytes 16) (t : (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))).Domain) :
    IsQueryBoundP (prfOI k t) (fun i => i.isRight = true)
      ((if isCompQ t = true then 1 else 0) + (if isPrfQ t = true then 2 else 0) +
        (if False then 0 else 0) + (if False then 0 else 0)) := by
  rcases t with n | q | d
  · simp only [prfOI, isCompQ, isPrfQ, Bool.false_eq_true, ite_false, add_zero]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp at h
  · simp only [prfOI, isCompQ, isPrfQ, Bool.false_eq_true, ite_false, ite_true, add_zero]
    exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · simp only [prfOI, isCompQ, isPrfQ, Bool.false_eq_true, ite_false, ite_true, add_zero,
      zero_add]
    exact isQueryBoundP_bind (n := 1) (m := 1)
      ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      fun c _ => (isQueryBoundP_bind (n := 1) (m := 0)
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
        fun u _ => isQueryBoundP_pure _ _ _)

/-- Compression queries of `progOf A` from those of `A`. -/
theorem progOf_comp (A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)) (n₁ n₂ : ℕ)
    (h1 : IsQueryBoundP A (fun i => isCompQ i = true) n₁)
    (h2 : IsQueryBoundP A (fun i => isPrfQ i = true) n₂) :
    IsQueryBoundP (progOf A) (fun i => i.isRight = true) (n₁ + 2 * n₂) := by
  unfold progOf
  refine (isQueryBoundP_bind (m := n₁ + 2 * n₂)
    (liftM_zeroG (X := hS St Blk) _ (fun i => i.isRight = true) fun n => by simp)
    fun k _ => ?_).mono (by omega)
  have := qb_simulateQ_classes4 (p₀ := fun _ => False) (p₁ := fun i => isCompQ i = true)
    (p₂ := fun i => isPrfQ i = true) (p₃ := fun _ => False) (p₄ := fun _ => False)
    (q := fun i => i.isRight = true) (impl := prfOI k) 1 2 0 0
    (fun t _ => by simpa using prfOI_step k t) (oa := A)
    (isQueryBoundP_false A 0) h1 h2 (isQueryBoundP_false A 0) (isQueryBoundP_false A 0)
  exact this.mono (by omega)

variable {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

/-- **Compression queries of the SUF entry program.** -/
theorem progS_comp :
    IsQueryBoundP (progS S oR pkSeedDist) (fun i => i.isRight = true)
      (qPrf qf qs ℓ + 2 * qOPrf qs) := by
  have hF := Ideal.Realize.Msg.mainC_bounds S hqf hqs hlong hout
  exact progOf_comp _ _ _
    (chain_comp _ (bPrfWCOpenP_port _ _ hF)
      (IsQueryBoundP.of_imp qTh_imp (bPrfWCOpenP_hash _ _ hF)) (bPrfWCOpenP_hm _ _ hF)
      (bPrfWCOpenP_pm _ _ hF) (bPrfWCOpenP_bad _ _ hF thB Ideal.Realize.Msg.okLen_le))
    (chain_prf _ (bPrfWCOpenP_game _ _ hF))

/-- **Compression queries of the EUF entry program.** -/
theorem progE_comp :
    IsQueryBoundP (progE S oR pkSeedDist) (fun i => i.isRight = true)
      (qPrf qf qs ℓ + 2 * qOPrf qs) := by
  have hF := Ideal.Realize.Msg.mainC_bounds S hqf hqs hlong hout
  exact progOf_comp _ _ _
    (chain_comp _ (bPrfCOpenP_port _ _ hF)
      (IsQueryBoundP.of_imp qTh_imp (bPrfCOpenP_hash _ _ hF)) (bPrfCOpenP_hm _ _ hF)
      (bPrfCOpenP_pm _ _ hF) (bPrfCOpenP_bad _ _ hF thB Ideal.Realize.Msg.okLen_le))
    (chain_prf _ (bPrfCOpenP_game _ _ hF))

/-- **All tagged queries of the tagged SUF program** (the cell budget). -/
theorem progTS_all :
    IsQueryBoundP (progTS S oR pkSeedDist) (fun i => i.isRight = true)
      (qPrf qf qs ℓ + 2 * qOPrf qs) := by
  have h := progS_comp S oR pkSeedDist hqf hqs hlong hout
  rw [← untag_progTS] at h
  refine IsQueryBoundP.of_imp (fun i hi => ?_) (qb_of_untag _ _ _ h)
  rcases i with n | tq <;> simp_all [untagIdx]

/-- **All tagged queries of the tagged EUF program.** -/
theorem progTE_all :
    IsQueryBoundP (progTE S oR pkSeedDist) (fun i => i.isRight = true)
      (qPrf qf qs ℓ + 2 * qOPrf qs) := by
  have h := progE_comp S oR pkSeedDist hqf hqs hlong hout
  rw [← untag_progTE] at h
  refine IsQueryBoundP.of_imp (fun i hi => ?_) (qb_of_untag _ _ _ h)
  rcases i with n | tq <;> simp_all [untagIdx]

end Ideal.Direct

#print axioms Ideal.Direct.qb_of_untag
#print axioms Ideal.Direct.progS_comp
#print axioms Ideal.Direct.progTS_all
#print axioms Ideal.Direct.progTE_all
