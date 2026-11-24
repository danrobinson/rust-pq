import Integration.SlhDsaRawSearch
import Integration.SlhDsaShakeSingleTarget
import Integration.SlhDsaShakeApiRaw
import Integration.SlhDsaCompressionClassPort

namespace Reduction.ShakeSingle
open MLink Ideal SLHDSA SLHDSA.DigestTransport PQ.Interactive PQ.QROM Quantum OracleComp OracleSpec
open Compression.Recording
open scoped ComplexOrder
set_option maxRecDepth 8192
open Classical

/-- A bounded quantum computation reports two distinct raw byte strings whose
SHAKE outputs have the same FIPS-decoded digest. All addresses share a table. -/
theorem digest_search (S : Sha2Set) (N : ℕ) {E α : Type} [Fintype E] [DecidableEq E]
    (M : ShakeApi.RawTable S N → Closed (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) α)
    (pick : α → Option (ShakeApi.Input N × ShakeApi.Input N))
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ₀ : Matrix (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) _ ℂ)
    (pos : ρ₀.PosSemidef) (tr : ρ₀.trace = 1) :
    SetOracle.uniformMean (fun H => qWeight (fun z => Database.reports (coveringDigest S.vp) (pick z) H) (M H) ρ₀) ≤
      ENNReal.ofReal (16*((q:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k)) := by
  classical
  obtain ⟨x,hx,he⟩ := hq.exists_prog_qprob
  obtain ⟨ρ,rfl⟩ := exists_subState ρ₀ pos tr
  unfold SetOracle.uniformMean
  simp_rw [← he]
  apply Compile.mixed_mean_over _ x ρ q hx id _ _ (by positivity)
  intro v
  exact RawSearch.pure_mean (coveringDigest S.vp) _ (by positivity) (fun B => (fraction S B).le)
    _ (fun _ y => y) pick x q hx v

/-- Even after allowing 2^41 total raw XOF calls, including honest calls, the
common digest-collision term is at most 2^-100 for each of the six sets. -/
theorem digest_search_budget (S : Sha2Set) {q : ℕ} (hq : q ≤ 2^41) :
    ENNReal.ofReal (16*((q:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k)) ≤
      ENNReal.ofReal ((2:ℝ)^100)⁻¹ := by
  apply ENNReal.ofReal_le_ofReal
  have h : 231 ≤ S.vp.params.h+S.vp.params.a*S.vp.params.k := by cases S <;> decide +kernel
  have d : (2:ℝ)^231 ≤ 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k) := pow_le_pow_right₀ (by norm_num) h
  have q' : (q:ℝ) ≤ 2^41 := by exact_mod_cast hq
  calc _ ≤ 16*((2^41:ℝ)+1)^3 / 2^231 := by gcongr
       _ ≤ _ := by norm_num

end Reduction.ShakeSingle
#print axioms Reduction.ShakeSingle.digest_search
#print axioms Reduction.ShakeSingle.digest_search_budget
