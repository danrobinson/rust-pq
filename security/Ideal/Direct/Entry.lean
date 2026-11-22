import Ideal.Realize.PrfReal
import Ideal.Core.HPTable

/-!
# The entry point of the direct proof (D0 of `status/DIRECT.md`)

The SUF (and EUF) experiment of an ideal-model forger as ONE closed compression program per
table, obtained from the *real* side of the `PRF` realiser game (no `PRF` bound is charged: the
game is only used as a wrapper that exposes the experiment as a compression program).

* `prfOI k`: the `PRF` game oracle at the key `k` answered by its two compression calls
  `out16 (g (g (IV, sb128 pk), blk128 a k))`; compression queries and coins forwarded.
* `progOf A := k ← $ᵗ (Bytes 16); simulateQ (prfOI k) A`, a program over `unifSpec + hS St Blk`.
* `progS S oR pkSeedDist := progOf (AprfS S oR pkSeedDist)` (SUF), `progE` (EUF).
* **`sufI_le_progS`**: `sufI S (optRandU oR) pkSeedDist ≤ cfAdvantage fun g =>
  simulateQ (instImpl₀ g) (progS S oR pkSeedDist)`, and `eufI_le_progE`.
* **`cfAdvantage_eq_lazy`**: for any program, the table average equals the probability over a
  lazily sampled table (`romImpl`), so `sufI_le_lazy`, `eufI_le_lazy`.

The inequality (not an equality) comes only from the byte-to-typed transfer
`Reduction.bytes_strong_advantage_le`, as in every existing composition.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Ideal.Direct

open Ideal.Realize.Prf

set_option linter.unusedSectionVars false

/-! ## The PRF oracle as compression calls -/

/-- The `PRF` game oracle at the key `k`, answered by two compression queries; coins and
compression queries forwarded. -/
def prfOI (k : Bytes 16) :
    QueryImpl (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))) (OracleComp (unifSpec + hS St Blk))
  | .inl n => (unifSpec + hS St Blk).query (.inl n)
  | .inr (.inl q) => (unifSpec + hS St Blk).query (.inr q)
  | .inr (.inr d) => do
      let c ← (unifSpec + hS St Blk).query (.inr (IV128, sb128 d.1))
      let u ← (unifSpec + hS St Blk).query (.inr (c, blk128 d.2 k))
      pure (out16 u)

/-- The closed compression program of an ideal-model `PRF` distinguisher on the real side:
sample the key, answer the oracle by compression calls. -/
noncomputable def progOf (A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)) :
    OracleComp (unifSpec + hS St Blk) Bool := do
  let k ← (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp (unifSpec + hS St Blk) _)
  simulateQ (prfOI k) A

theorem prfOI_inst (g : CF St Blk) (k : Bytes 16) (t : (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))).Domain) :
    simulateQ (instImpl₀ g) (prfOI k t) =
      simulateQ ((prfSchemeI IV128 sb128 blk128 out16 g).prfRealQueryImpl k)
        (instImpl (spec := Dsk →ₒ Bytes 16) g t) := by
  rcases t with n | q | d
  · simp [prfOI, instImpl, instImpl₀, unifFwdAnswerImpl, PRFScheme.prfRealQueryImpl]
  · simp [prfOI, instImpl, instImpl₀, unifFwdAnswerImpl]; rfl
  · simp [prfOI, instImpl, instImpl₀, unifFwdAnswerImpl, prfSchemeI, prfF]; exact ⟨_, rfl, rfl⟩

/-- At every table, the real `PRF` experiment of `A` (Reduction's scheme `skPrfC`) is the
program `progOf A` answered by the table. -/
theorem prfReal_eq_progOf (g : CF St Blk) (A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)) :
    (Reduction.skPrfC Link.vp (primsG (liftC g))).prfRealExperiment (A.inst g) =
      simulateQ (instImpl₀ g) (progOf A) := by
  rw [skPrfC_eq]
  unfold progOf PRFScheme.prfRealExperiment PrfAdvI.inst
  rw [simulateQ_bind, Ideal.Realize.instImpl₀_liftM]
  refine bind_congr fun k => ?_
  exact (Ideal.Realize.simulateQ_comm_of_step _ _ _ _ (fun t => (prfOI_inst g k t).symm) A)

/-! ## The SUF and EUF programs -/

/-- **The SUF experiment as one compression program.** -/
noncomputable def progS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp (unifSpec + hS St Blk) Bool :=
  progOf (AprfS S oR pkSeedDist)

/-- **The EUF experiment as one compression program.** -/
noncomputable def progE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp (unifSpec + hS St Blk) Bool :=
  progOf (AprfE S oR pkSeedDist)

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

/-- Per table: the strong-forgery advantage is at most the probability that `progS` returns
`true` at that table. -/
theorem sufAdv_le_progS (g : CF St Blk) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (S.sufInst (optRandU oR) pkSeedDist g) ≤
      𝒟[simulateQ (instImpl₀ g) (progS S oR pkSeedDist)] {true} := by
  refine (Reduction.bytes_strong_advantage_le _).trans (le_of_eq ?_)
  refine (Reduction.strongAdvantage_eq_expW _).trans ?_
  have h1 := (Reduction.prfRealPr_bPrfWC (structuralG g) Reduction.sufCheck
    (S.typedS (optRandU oR) pkSeedDist g)).symm
  refine h1.trans ?_
  unfold Reduction.prfRealPr
  rw [bPrfWC_eq_inst S oR pkSeedDist g, prfReal_eq_progOf]
  rfl

/-- Per table: the EUF advantage is at most the probability that `progE` returns `true`. -/
theorem eufAdv_le_progE (g : CF St Blk) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (S.eufInst (optRandU oR) pkSeedDist g) ≤
      𝒟[simulateQ (instImpl₀ g) (progE S oR pkSeedDist)] {true} := by
  refine (Reduction.bytes_advantage_le _).trans (le_of_eq ?_)
  have h1 := (Reduction.prfRealPr_bPrfC (structuralG g) (S.typedE (optRandU oR) pkSeedDist g)).symm
  refine (?_ : _ = _).trans (h1.trans ?_)
  · rfl
  unfold Reduction.prfRealPr
  rw [bPrfC_eq_inst S oR pkSeedDist g, prfReal_eq_progOf]
  rfl

/-- **Entry point (SUF).** -/
theorem sufI_le_progS :
    sufI S (optRandU oR) pkSeedDist ≤
      cfAdvantage fun g => simulateQ (instImpl₀ g) (progS S oR pkSeedDist) := by
  rw [sufI_eq_cfAvg, cfAdvantage_eq_cfAvg]
  exact cfAvg_mono fun g => sufAdv_le_progS S oR pkSeedDist g

/-- **Entry point (EUF).** -/
theorem eufI_le_progE :
    eufI S (optRandU oR) pkSeedDist ≤
      cfAdvantage fun g => simulateQ (instImpl₀ g) (progE S oR pkSeedDist) := by
  rw [eufI_eq_cfAvg, cfAdvantage_eq_cfAvg]
  exact cfAvg_mono fun g => eufAdv_le_progE S oR pkSeedDist g

/-! ## Lazy table -/

/-- The table average of a compression program is its success probability over a lazily
sampled table (generic in the table types, so that the kernel never sees the concrete
SHA-256 carriers). -/
theorem cfAdvantage_eq_lazy_gen {S B : Type} [DecidableEq S] [DecidableEq B] [Finite S]
    [Finite B] [SampleableType S] [SampleableType (CF S B)]
    (X : OracleComp (unifSpec + hS S B) Bool) :
    (cfAdvantage fun g => simulateQ (instImpl₀ g) X) =
      HP.prT ((simulateQ (hS S B).romImpl X).run' ∅) := by
  unfold cfAdvantage
  rw [← HP.prT_eq]
  refine (HP.prT_congr ?_).symm
  let : SampleableType ((t : S × B) → (hS S B).Range t) :=
    inferInstanceAs (SampleableType (CF S B))
  rw [OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable]
  refine congrArg _ (bind_congr fun g => ?_)
  rw [OracleComp.completeTable_empty]
  rfl

theorem cfAdvantage_eq_lazy (X : OracleComp (unifSpec + hS St Blk) Bool) :
    (cfAdvantage fun g => simulateQ (instImpl₀ g) X) =
      HP.prT ((simulateQ (hS St Blk).romImpl X).run' ∅) :=
  cfAdvantage_eq_lazy_gen X

/-- **Entry point (SUF), lazy-table form.** -/
theorem sufI_le_lazy :
    sufI S (optRandU oR) pkSeedDist ≤
      HP.prT ((simulateQ (hS St Blk).romImpl (progS S oR pkSeedDist)).run' ∅) :=
  (sufI_le_progS S oR pkSeedDist).trans (le_of_eq (cfAdvantage_eq_lazy _))

/-- **Entry point (EUF), lazy-table form.** -/
theorem eufI_le_lazy :
    eufI S (optRandU oR) pkSeedDist ≤
      HP.prT ((simulateQ (hS St Blk).romImpl (progE S oR pkSeedDist)).run' ∅) :=
  (eufI_le_progE S oR pkSeedDist).trans (le_of_eq (cfAdvantage_eq_lazy _))

end Ideal.Direct

#print axioms Ideal.Direct.prfReal_eq_progOf
#print axioms Ideal.Direct.sufI_le_progS
#print axioms Ideal.Direct.eufI_le_progE
#print axioms Ideal.Direct.sufI_le_lazy
#print axioms Ideal.Direct.eufI_le_lazy
