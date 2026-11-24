import Integration.SlhDsaCompressionLongBenchmark
import Integration.SlhDsaCompressionSingleBenchmark
import Integration.SlhDsaCompressionClassicalWide

/-! Strong and existential unforgeability for all six pure SHA-2 byte schemes
with coherent access to the same random compression tables used by the signer. -/
namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

noncomputable def sharedBound (L q qs : ℕ) : ℝ≥0∞ :=
  if S.vp.params.n = 16 then
    if qs ≤ 1 then smallLongSingleBound S L q qs else smallLongBound S L q qs
  else if qs ≤ 1 then wideSingleBound S L q qs else wideMixedBound S L q qs

/-- Both forgery notions, with separate public and signing query budgets and an encoded message cap. -/
theorem shared_security (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤ sharedBound S c.ml q qs ∧
    SetOracle.uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤ sharedBound S c.ml q qs := by
  unfold sharedBound
  split_ifs with hn single single
  · exact ⟨small_long_single_suf S hn rand seeds F c q qs hq hs hc single, small_long_single_euf S hn rand seeds F c q qs hq hs hc single⟩
  · exact ⟨small_long_suf S hn rand seeds F c q qs hq hs hc, small_long_euf S hn rand seeds F c q qs hq hs hc⟩
  · exact ⟨wide_suf_single S rand seeds F hn c q qs single hq hs hc, wide_euf_single S rand seeds F hn c q qs single hq hs hc⟩
  · exact ⟨wide_suf_mixed S rand seeds F hn c q qs hq hs hc, wide_euf_mixed S rand seeds F hn c q qs hq hs hc⟩

def singleBits : Sha2Set → ℕ
  | .s128s | .s128f => 39
  | .s192s => 19
  | .s192f => 22
  | .s256s => 78
  | .s256f => 79

private theorem single_bound : sharedBound S 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^(singleBits S))⁻¹ := by
  obtain ⟨slow,fast⟩ := small_long_single_benchmark
  obtain ⟨a,b,c,d⟩ := wide_single_benchmark
  cases S
  · exact slow
  · exact fast
  · exact a
  · exact b
  · exact c
  · exact d

/-- At most one signing query, 2^40 public queries and 64 KiB encoded messages.
The returned bounds refer to the actual strong and existential signature experiments. -/
theorem shared_single_benchmark (c : Caps) (hL : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤ ((2:ℝ≥0∞)^(singleBits S))⁻¹ ∧
    SetOracle.uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤ ((2:ℝ≥0∞)^(singleBits S))⁻¹ := by
  have h := shared_security S rand seeds F c (2^40) 1 hq hs hc
  rw [hL] at h
  exact ⟨h.1.trans (single_bound S), h.2.trans (single_bound S)⟩

namespace ClassicalPort
open MIdeal.PureCompression
variable (A : MIdeal.PureCompression.Forger)
local notation "adv" => MIdeal.PureCompression.strong S rand seeds A

/-- The same six budgets for classical byte forgers with public access to both tables. -/
theorem classical_shared_security (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound (fun i => publicCount i = true) (A.main pk) q)
    (hs : ∀ pk, CountBound (fun i => signCount i = true) (A.main pk) qs)
    (hc : ∀ pk, AllQueries (capped c) (capOut c) (A.main pk)) :
    average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (adv g)) ≤ sharedBound S c.ml q qs ∧
    average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (adv g).toUnforgeableAdversary) ≤ sharedBound S c.ml q qs := by
  have strong : average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (adv g)) ≤ sharedBound S c.ml q qs := by
    rw [average_eq]
    simp_rw [← strong_eq S rand seeds A]
    obtain ⟨hp,hsg⟩ := count_forger A q qs hq hs
    exact (shared_security S rand seeds (asPort A) c q qs hp hsg (cap_forger A c hc)).1
  exact ⟨strong,(average_mono fun g => SignatureAlg.unforgeableAdvantage_le_strongUnforgeableAdvantage _
    (adv g).toUnforgeableAdversary).trans strong⟩

theorem classical_shared_single_benchmark (c : Caps) (hL : c.ml = 65536)
    (hq : ∀ pk, CountBound (fun i => publicCount i = true) (A.main pk) (2^40))
    (hs : ∀ pk, CountBound (fun i => signCount i = true) (A.main pk) 1)
    (hc : ∀ pk, AllQueries (capped c) (capOut c) (A.main pk)) :
    average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (adv g)) ≤ ((2:ℝ≥0∞)^(singleBits S))⁻¹ ∧
    average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (adv g).toUnforgeableAdversary) ≤ ((2:ℝ≥0∞)^(singleBits S))⁻¹ := by
  have h := classical_shared_security S rand seeds A c (2^40) 1 hq hs hc
  rw [hL] at h
  exact ⟨h.1.trans (single_bound S), h.2.trans (single_bound S)⟩
end ClassicalPort
end Reduction.Compression
#print axioms Reduction.Compression.shared_security
#print axioms Reduction.Compression.shared_single_benchmark
#print axioms Reduction.Compression.ClassicalPort.classical_shared_security
#print axioms Reduction.Compression.ClassicalPort.classical_shared_single_benchmark
