import Ideal.Compose128
import Ideal.Inst.ItsrNumeric

/-!
# The ITSR term of the composition

`RealizesItsr B q qs ℓ`: the family `B g` of ITSR adversaries (in the composition:
`Reduction.Lazy.bItsrL` of the typed forger at table `g`) has, for every table, the ITSR advantage
of one ideal-model adversary with `q` compression queries, `qs` target queries and messages of
at most `ℓ` bytes.  `itsrSufI_le` then discharges the hypothesis `hI` of `Ideal.suf_ideal_bound`
with `εI := reuseSum 63 12 14 (q + 2 (qs + 1)) + (q + (qs + 1) ((ℓ + 56) / 64 + 3))² / 2^256`,
and `itsrSufI_le_2_64` evaluates it at `q = qs = 2^64`, `ℓ = 2^26` bytes: `≤ 2^-50 + 2^-86`.
The realiser itself is a hypothesis.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal KeyedHash

namespace Ideal

open Ideal.Itsr

/-- Realiser for a family of ITSR adversaries. -/
structure RealizesItsr
    (B : ∀ g : CF St Blk, ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g))))
    (q qs ℓ : ℕ) where
  A : OracleComp (unifSpec + (hS St Blk + ITSRTargetSpec X128 (Bytes 16))) (Bytes 16 × X128)
  eq : ∀ g, KeyedHash.ITSRAdvantage (B g) = KeyedHash.ITSRAdvantage (instItsr A g)
  hq : IsQueryBoundP A (fun i => isCompI i = true) q
  hqs : IsQueryBoundP A (fun i => isTgtI i = true) qs
  htgt : AllQueriesSatisfy A (tgtOK (msgLe ℓ))
  hout : ∀ kx ∈ support A, msgLe ℓ kx

theorem cfAvg_itsr_le
    {B : ∀ g : CF St Blk, ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g)))}
    {q qs ℓ : ℕ} (R : RealizesItsr B q qs ℓ) :
    (cfAvg fun g => KeyedHash.ITSRAdvantage (B g)) ≤
      reuseSum 63 12 14 (q + 2 * (qs + 1)) +
        (((q + (qs + 1) * ((ℓ + 56) / 64 + 3)) ^ 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have h1 : (cfAvg fun g => KeyedHash.ITSRAdvantage (B g)) =
      cfAvg fun g => 𝒟[ITSRExperiment (instItsr R.A g)] {true} :=
    cfAvg_congr fun g => (R.eq g).trans (ITSRAdvantage_eq_evalDist_experiment _)
  have h2 : itsrI R.A = cfAvg fun g => 𝒟[ITSRExperiment (instItsr R.A g)] {true} :=
    cfAdvantage_eq_cfAvg _
  rw [h1, ← h2]
  exact itsr_bound_128s R.A q qs ℓ R.hq R.hqs R.htgt R.hout

section
variable (S : ForgerI)
  (optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
  (pkSeedDist : ProbComp (Bytes 16))

/-- `hI` of `suf_ideal_bound` from a twelfth realiser. -/
theorem itsrSufI_le {q qs ℓ : ℕ}
    (R : RealizesItsr (fun g => Reduction.Lazy.bItsrL (S.typedS optRand pkSeedDist g)) q qs ℓ) :
    itsrSufI S optRand pkSeedDist ≤
      reuseSum 63 12 14 (q + 2 * (qs + 1)) +
        (((q + (qs + 1) * ((ℓ + 56) / 64 + 3)) ^ 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  cfAvg_itsr_le R

/-- At `q = qs = 2^64` and messages of at most `2^26` bytes: `≤ 2^-50 + 2^-86`. -/
theorem itsrSufI_le_2_64
    (R : RealizesItsr (fun g => Reduction.Lazy.bItsrL (S.typedS optRand pkSeedDist g))
      (2 ^ 64) (2 ^ 64) (2 ^ 26)) :
    itsrSufI S optRand pkSeedDist ≤ ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 86)⁻¹ :=
  (itsrSufI_le S optRand pkSeedDist R).trans
    (add_le_add reuseSum_q64_qs64 (natMul_inv_pow_le _ _ _ (by norm_num)))

end

end Ideal

#print axioms Ideal.cfAvg_itsr_le
#print axioms Ideal.itsrSufI_le_2_64
