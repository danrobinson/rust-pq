import Integration.SlhDsaCompressionClassicalGame
import Integration.SlhDsaCompressionClassicalMean
import Integration.SlhDsaCompressionSingleTarget
import Integration.SlhDsaCompressionTargetSubset

/-!
Classical compression reads are exact basis queries to the shared quantum port. The simulation
preserves the public and signing query budgets, encoded message cap, and fixed-table forgery
probability. Averaging therefore transfers each wide-set quantum upper bound to classical forgers.
-/
namespace Reduction.Compression.ClassicalPort
open MLink Ideal PQ.Interactive PQ.QROM Quantum OracleComp OracleSpec ENNReal SLHDSA SLHDSA.Security
open MIdeal.PureCompression Classical
set_option maxRecDepth 12000
variable (S : Sha2Set) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable (A : MIdeal.PureCompression.Forger)
local notation "F" => MIdeal.PureCompression.strong S r seeds A

private def rawStrong {SK : Type} (alg : SignatureAlg ProbComp Msg (List Byte) SK Sgn)
    (A : MIdeal.PureCompression.Forger) (g : CompressionTables) : SignatureAlg.StrongUnforgeableAdversary alg :=
  ⟨fun pk => simulateQ (instImpl g.1) (simulateQ (instImpl g.2) (A.main pk))⟩

private theorem generic_eq {SK : Type} (alg : SignatureAlg ProbComp Msg (List Byte) SK Sgn)
    (A : MIdeal.PureCompression.Forger) (g : CompressionTables) :
    qStrongUnforgeableAdvantage ((asPort A).at (oracle g) alg) =
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (rawStrong alg A g) := by
  rw [SignatureAlg.strongUnforgeableAdvantage,ProbCompRuntime.probComp_evalDist,← prEvent_eq_evalDist_singleton]
  unfold qStrongUnforgeableAdvantage qStrongUnforgeableExperiment
  exact (classical_game alg A g _).trans rfl

private abbrev schemeOf {SK : Type} {alg : SignatureAlg ProbComp Msg (List Byte) SK Sgn}
    (_ : SignatureAlg.StrongUnforgeableAdversary alg) := alg

private theorem scheme_eq (g : CompressionTables) :
    pureBytesAlg S.vp (randPrims (functions S g)) (SetOracle.codecFor S (functions S g))
      (fun pk => r pk.pkSeed pk.pkRoot) seeds = schemeOf (F g) := by
  dsimp only [schemeOf, SetOracle.codecFor, MReduction.codec, Concrete.sha2WireCodec, MIdeal.PureCompression.codec]
  have hd : (fun a b : Bytes S.vp.params.n => (inferInstance : DecidableEq (Bytes S.vp.params.n)) a b) = MIdeal.PureCompression.instDecidableEqYTablePrimitivesParamsVp S g := Subsingleton.elim _ _
  rw [← hd]
  qm_kernel_rfl

/-- Exact equality of the strong forgery probabilities at each fixed pair of tables. -/
theorem strong_eq (g : CompressionTables) :
    qStrongUnforgeableAdvantage (experimentForger S r seeds (asPort A) g) =
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (F g) := by
  have h := congrArg (fun alg : SignatureAlg ProbComp Msg (List Byte) (List Byte) Sgn =>
    qStrongUnforgeableAdvantage ((asPort A).at (oracle g) alg)) (scheme_eq S r seeds A g)
  exact h.trans (generic_eq (schemeOf (F g)) A g)

/-- Inherit the sharper full-digest reduction when zero or one signing query is allowed. -/
noncomputable def wideClassicalLoss (L q qs : ℕ) :=
  if qs ≤ 1 then wideSingleBound S L q qs else wideMixedBound S L q qs

variable (c : Caps) (q qs : ℕ)
variable (hq : ∀ pk, CountBound (fun i => publicCount i = true) (A.main pk) q)
variable (hs : ∀ pk, CountBound (fun i => signCount i = true) (A.main pk) qs)
variable (hc : ∀ pk, AllQueries (capped c) (capOut c) (A.main pk))

include hq hs hc in
theorem wide_suf (hw : S.vp.params.n ≠ 16) :
    average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (F g)) ≤
      wideClassicalLoss S c.ml q qs := by
  rw [average_eq]
  simp_rw [← strong_eq S r seeds A]
  obtain ⟨hp,hsg⟩ := count_forger A q qs hq hs
  unfold wideClassicalLoss
  split
  · exact wide_suf_single S r seeds (asPort A) hw c q qs ‹_› hp hsg (cap_forger A c hc)
  · exact wide_suf_mixed S r seeds (asPort A) hw c q qs hp hsg (cap_forger A c hc)

include hq hs hc in
theorem wide_euf (hw : S.vp.params.n ≠ 16) :
    average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (F g).toUnforgeableAdversary) ≤
      wideClassicalLoss S c.ml q qs :=
  (average_mono fun g => SignatureAlg.unforgeableAdvantage_le_strongUnforgeableAdvantage _
    (F g).toUnforgeableAdversary).trans (wide_suf S r seeds A c q qs hq hs hc hw)
include hq hs hc in
theorem wide_suf_subset (hw : S.vp.params.n ≠ 16) (d : ℕ) (dk : d < S.vp.params.k)
    (many : qs*d < S.vp.params.k) :
    average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (F g)) ≤
      wideMaskBound S c.ml q qs d := by
  rw [average_eq]
  simp_rw [← strong_eq S r seeds A]
  obtain ⟨hp,hsg⟩ := count_forger A q qs hq hs
  exact wide_suf_mask S r seeds (asPort A) hw c q qs d dk many hp hsg (cap_forger A c hc)

include hq hs hc in
theorem wide_euf_subset (hw : S.vp.params.n ≠ 16) (d : ℕ) (dk : d < S.vp.params.k)
    (many : qs*d < S.vp.params.k) :
    average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (F g).toUnforgeableAdversary) ≤
      wideMaskBound S c.ml q qs d :=
  (average_mono fun g => SignatureAlg.unforgeableAdvantage_le_strongUnforgeableAdvantage _
    (F g).toUnforgeableAdversary).trans (wide_suf_subset S r seeds A c q qs hq hs hc hw d dk many)
end Reduction.Compression.ClassicalPort
#print axioms Reduction.Compression.ClassicalPort.strong_eq
#print axioms Reduction.Compression.ClassicalPort.wide_suf
#print axioms Reduction.Compression.ClassicalPort.wide_euf
#print axioms Reduction.Compression.ClassicalPort.wide_suf_subset
#print axioms Reduction.Compression.ClassicalPort.wide_euf_subset
