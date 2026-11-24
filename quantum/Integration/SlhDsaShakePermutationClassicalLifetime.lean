import Integration.SlhDsaShakePermutationClassicalSignature
import Integration.SlhDsaShakeAdaptiveSignature

namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp MLink SLHDSA SLHDSA.Security PQ.Interactive Quantum
open SetOracle (uniformMean signingCheckpoint)
open scoped ENNReal Classical
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

/-- Public permutation calls plus a worst-case padded-block charge for all
honest calls during key generation, signing and final verification. -/
def blockBudget (S : Sha2Set) (q s : ℕ) := q+483*Honest.honestCharge S s

/-- The complete classical sponge crossing cost has a common 512-bit
denominator from the capacity of SHAKE256. -/
theorem crossing_certificate (t b : ℕ) (cert : (5*t^2+4*t)*2^b ≤ 2^512) :
    classicalLoss t ≤ ((2:ℝ≥0∞)^b)⁻¹ := by
  have cap : Fintype.card Capacity = 2^512 := by
    change Fintype.card (Fin 8 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  unfold classicalLoss capLoss hiddenLoss
  rw [cap]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← one_div,le_div_iff₀ (by positivity)]
  have h : ((5:ℝ)*(t:ℝ)^2+4*t)*2^b ≤ 2^512 := by exact_mod_cast cert
  linarith only [show ((t:ℝ)*((2*t+2)/(2:ℝ)^512)+(t*(2*t+2)+t^2)/(2:ℝ)^512)*2^b =
    ((5:ℝ)*t^2+4*t)*2^b/2^512 by ring, (div_le_one (by positivity : (0:ℝ)<2^512)).mpr h]

/-- Exponent for the classical permutation-to-XOF loss at budget t. -/
def crossingBits (t : ℕ) := 512-((5*t^2+4*t-1).log2+1)

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (F : CForger Port Words) (c : Caps) (msg : c.ml = 65536)
local notation "N" => inputLimit S
local notation "F₀" => liftClassical (false,0) F
include msg

/-- Transfer both freshness games at arbitrary budgets. The source bound
holds uniformly for the simulated classical player with its raw XOF port. -/
theorem signature_of_raw (q s : ℕ) (bound : ℝ≥0∞) (cap : Completion.blockCap N ≤ blockBudget S q s)
    (ports : ∀ pk, CountBound (fun i => publicRead (X := Port) (Y := Words) i = true) (F pk) q)
    (signs : ∀ pk, CountBound (fun i => signRead (X := Port) (Y := Words) i = true) (F pk) s)
    (hc : ∀ pk, AllQueries (readCap (X := Port) (Y := Words) c) (capOut c) (F pk))
    (source : ∀ (g : Completion.Private (blockBudget S q s)) (k : Fix.Domain (blockBudget S q s) → Capacity) (u : Port → Words),
      let player := liftClassical (BList.ofList [] (by simp)) (sourceForger S N (blockBudget S q s) cap g k u F)
      uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds player H)) ≤ bound ∧
      uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds player H)) ≤ bound) :
    strongAdvantage S rand seeds F₀ ≤ bound + classicalLoss (blockBudget S q s) ∧
    advantage S rand seeds F₀ ≤ bound + classicalLoss (blockBudget S q s) :=
  ⟨transfer_queries S rand seeds F c msg hc q s _ cap le_rfl ports signs strongFresh _ (fun g k u => (source g k u).1),
   transfer_queries S rand seeds F c msg hc q s _ cap le_rfl ports signs existentialFresh _ (fun g k u => (source g k u).2)⟩

/-- Classical forward/inverse permutation access at every signature checkpoint. -/
theorem signature_signing_checkpoint
    (ports : ∀ pk, CountBound (fun i => publicRead (X := Port) (Y := Words) i = true) (F pk) (2^40))
    (signs : ∀ pk, CountBound (fun i => signRead (X := Port) (Y := Words) i = true) (F pk) (2^(signingCheckpoint S).1))
    (hc : ∀ pk, AllQueries (readCap (X := Port) (Y := Words) c) (capOut c) (F pk)) :
    let bound := ((2:ℝ≥0∞)^(signingCheckpoint S).2)⁻¹ + ((2:ℝ≥0∞)^(crossingBits (blockBudget S (2^40) (2^(signingCheckpoint S).1))))⁻¹
    strongAdvantage S rand seeds F₀ ≤ bound ∧ advantage S rand seeds F₀ ≤ bound := by
  let s := 2^(signingCheckpoint S).1
  let t := blockBudget S (2^40) s
  have fit : Completion.blockCap N ≤ t := by cases S <;> decide +kernel
  have pair := signature_of_raw S rand seeds F c msg (2^40) s _ fit ports signs hc (fun g k u =>
      ShakeXof.signature_signing_checkpoint S N rand seeds _ c msg le_rfl
        (fun pk => (source_bounds S N t fit g k u F pk _ _ c (ports pk) (signs pk) (hc pk)).1)
        (fun pk => (source_bounds S N t fit g k u F pk _ _ c (ports pk) (signs pk) (hc pk)).2.1)
        (fun pk => (source_bounds S N t fit g k u F pk _ _ c (ports pk) (signs pk) (hc pk)).2.2))
  have loss := crossing_certificate t (crossingBits t) (by cases S <;> decide +kernel)
  exact ⟨pair.1.trans (add_le_add le_rfl loss),pair.2.trans (add_le_add le_rfl loss)⟩

/-- Full lifetime for both 256-bit families with 2^94 public permutation
queries, including all sponge calls made by the signers. -/
theorem wide_lifetime_signature (wide : S.vp.params.n = 32)
    (ports : ∀ pk, CountBound (fun i => publicRead (X := Port) (Y := Words) i = true) (F pk) (2^94))
    (signs : ∀ pk, CountBound (fun i => signRead (X := Port) (Y := Words) i = true) (F pk) (2^64))
    (hc : ∀ pk, AllQueries (readCap (X := Port) (Y := Words) c) (capOut c) (F pk)) :
    let bound := (3:ℝ≥0∞)⁻¹ + ((2:ℝ≥0∞)^319)⁻¹
    strongAdvantage S rand seeds F₀ ≤ bound ∧ advantage S rand seeds F₀ ≤ bound := by
  let t := blockBudget S (2^94) (2^64)
  have fit : Completion.blockCap N ≤ t := by cases S <;> decide +kernel
  have pair := signature_of_raw S rand seeds F c msg (2^94) (2^64) _ fit ports signs hc (fun g k u =>
      ShakeXof.wide_lifetime_signature S N rand seeds _ wide c msg le_rfl
        (fun pk => (source_bounds S N t fit g k u F pk _ _ c (ports pk) (signs pk) (hc pk)).1)
        (fun pk => (source_bounds S N t fit g k u F pk _ _ c (ports pk) (signs pk) (hc pk)).2.1)
        (fun pk => (source_bounds S N t fit g k u F pk _ _ c (ports pk) (signs pk) (hc pk)).2.2))
  have loss := crossing_certificate t 319 (by cases S <;> first | contradiction | decide +kernel)
  exact ⟨pair.1.trans (add_le_add le_rfl loss),pair.2.trans (add_le_add le_rfl loss)⟩

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.signature_signing_checkpoint
#print axioms Reduction.ShakePermutation.Classic.wide_lifetime_signature
