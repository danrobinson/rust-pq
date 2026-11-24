import HashSig.SLHDSA.Security.Profile

/-! Full-lifetime SUF-CMA bounds for all six classical pure-mode SHAKE profiles.
The adversary and the honest algorithms share the fixed-output random oracle
of the selected profile. The context is fixed and the signing mode can be
deterministic or hedged. The budget counts direct hash queries separately
from signing requests. -/

namespace Reduction.ShakeClassicalProfiles

open SLHDSA SLHDSA.Security SignatureAlg KeyedHash.Covering
open scoped ENNReal

/-- Logarithm of the direct hash-query budget for the half-success threshold. -/
def queryBits (profile : ShakeProfile) : ℕ :=
  match profile.parameterSet with
  | .SLHDSA_SHAKE_128s => 125
  | .SLHDSA_SHAKE_128f => 124
  | .SLHDSA_SHAKE_192s | .SLHDSA_SHAKE_192f => 189
  | .SLHDSA_SHAKE_256s | .SLHDSA_SHAKE_256f => 252
  | _ => 0  -- excluded by profile.shakeFamily

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

private theorem half_certificate (profile : ShakeProfile) :
    profile.boundEvaluator (2^(queryBits profile)) (2^64) < 1/2 := by
  rcases profile with ⟨set, family, mode, ctx⟩
  cases set <;> try contradiction
  all_goals cases mode <;> simp only [ShakeProfile.boundEvaluator, queryBits] <;> decide +kernel

/-- Full-lifetime strong forgery probability stays below one half up to the
profile's hash-query threshold, including the weak-seed contribution. -/
theorem lifetime_half (profile : ShakeProfile)
    (adv : StrongUnforgeableAdversary profile.algorithm)
    (budget : adv.RomQueryBound (2^(queryBits profile)) (2^64)) :
    strongUnforgeableAdvantage (shakeRuntime profile.parameterSet.validatedParams) adv < 1/2 := by
  apply (profile.strongUnforgeableAdvantage_le_boundEvaluator adv budget).trans_lt
  have h := half_certificate profile
  have h' : rationalValue (profile.boundEvaluator (2^(queryBits profile)) (2^64)) <
      rationalValue (1/2) := by simpa only [lt_iff_not_ge, rationalValue_le_iff] using h
  rwa [rationalValue_div _ (by norm_num), rationalValue_one, rationalValue_ofNat] at h'

/-- Conservative success exponents at 2^64 queries of each kind. -/
def successBits (profile : ShakeProfile) : ℕ :=
  match profile.parameterSet with
  | .SLHDSA_SHAKE_128s | .SLHDSA_SHAKE_128f => 62
  | .SLHDSA_SHAKE_192s | .SLHDSA_SHAKE_192f => 126
  | .SLHDSA_SHAKE_256s | .SLHDSA_SHAKE_256f =>
    match profile.signingMode with
    | .deterministic => 189
    | .hedged => 190
  | _ => 0

private theorem lifetime_certificate (profile : ShakeProfile) :
    profile.boundEvaluator (2^64) (2^64) ≤ 1 / 2^(successBits profile) := by
  rcases profile with ⟨set, family, mode, ctx⟩
  cases set <;> try contradiction
  all_goals cases mode <;> simp only [ShakeProfile.boundEvaluator, successBits] <;> decide +kernel

/-- Strong forgery probability after at most 2^64 direct hash queries and
2^64 signing requests under one key, retaining the full weak-seed term. -/
theorem lifetime_benchmark (profile : ShakeProfile)
    (adv : StrongUnforgeableAdversary profile.algorithm)
    (budget : adv.RomQueryBound (2^64) (2^64)) :
    strongUnforgeableAdvantage (shakeRuntime profile.parameterSet.validatedParams) adv ≤
      1 / 2^(successBits profile) := by
  apply (profile.strongUnforgeableAdvantage_le_boundEvaluator adv budget).trans
  have h := rationalValue_le (lifetime_certificate profile)
  rwa [rationalValue_div _ (by positivity), rationalValue_one, rationalValue_pow,
    rationalValue_ofNat] at h

end Reduction.ShakeClassicalProfiles

#print axioms Reduction.ShakeClassicalProfiles.lifetime_half
#print axioms Reduction.ShakeClassicalProfiles.lifetime_benchmark
