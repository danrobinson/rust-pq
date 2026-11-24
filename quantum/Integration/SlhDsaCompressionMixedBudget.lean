import Integration.SlhDsaCompressionMixedCollision

namespace Reduction.Compression.Transcript
open MLink Ideal SLHDSA
/-- Concrete check of the split collision estimate for a 1 KiB message cap,
2^40 public queries, and 2^20 signing queries, including the reduction's work. -/
theorem benchmark (S : Sha2Set) (hw : S.vp.params.n ≠ 16) :
    let c := tcrTargets S.vp * ClassCollision.walkMax S
    let q := ClassOne.budget S 1024 (2^40) (2^20) +
      (1 + 2*((38 + S.vp.params.n * max 2 (max S.vp.params.len S.vp.params.k))/128 + 1))
    256*(c^2 + c*(2*q+1)^2 + 16*(q+1)^3) ≤ 2^(8*S.vp.params.n) := by
  dsimp only
  cases S <;> first
    | exact (hw rfl).elim
    | (rw [MReduction.tcrTargets_192s_val]; decide +kernel)
    | (rw [MReduction.tcrTargets_192f_val]; decide +kernel)
    | (rw [MReduction.tcrTargets_256s_val]; decide +kernel)
    | (rw [MReduction.tcrTargets_256f_val]; decide +kernel)
end Reduction.Compression.Transcript
#print axioms Reduction.Compression.Transcript.benchmark
