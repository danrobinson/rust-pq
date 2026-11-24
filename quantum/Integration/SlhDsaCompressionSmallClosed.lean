import Integration.SlhDsaCompressionWotsSmallSignature
import Integration.SlhDsaCompressionHmac256Signature
import Integration.SlhDsaCompressionSmallClass
import Integration.SlhDsaCompressionSmallItsr
import Integration.SlhDsaCompressionCompose

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal Resources2
open SetOracle (uniformMean)

private noncomputable def smallClassLoss (S : Sha2Set) (L q qs ar : ℕ) : ℝ≥0∞ :=
  16*((SmallClass.budget S L q qs ar:ℝ≥0∞)+1)^3/2^128

/-- Numerical strong and ordinary forgery loss in the shared ideal SHA-256/SHA-512
compression model at the 128-bit parameter sets. -/
noncomputable def smallBound (S : Sha2Set) (L q qs : ℕ) : ℝ≥0∞ :=
  let ch := Wots256.phaseLoss (Wots256.chooseBudget S) 9
  let ar := smallClassLoss S L q qs
  forsAndKeyLoss S L q qs +
    (Hmac256.loss (2*HmacKey.budget S L q qs) + SmallItsr.loss S L q qs (SmallItsr.bits S) +
      ar 2 + ar S.vp.params.len + ar S.vp.params.k + ar 1 +
      ((S.vp.params.w-2:ℕ):ℝ≥0∞) * (SetOracle.epsUdSet S (wotsBudget S L q qs (wotsWinHashes S.vp)) + 2*ch) +
      (SetOracle.epsPreSet S (wotsBudget S L q qs (wotsPreHashes S.vp)) + ch) +
      (epsTcr S (wotsBudget S L q qs (wotsTcrHashes S.vp)) + ch))

variable (S : Sha2Set) (hn : S.vp.params.n = 16) (rand : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

include hn

theorem small_suf_closed (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤ smallBound S c.ml q qs := by
  apply (suf_fors_key_partial S rand seeds F c q qs hq hs hc).trans
  unfold smallBound narrowRemaining wideRemaining
  have ar := fun k => SmallClass.class_tcr_le S hn rand seeds F k c q qs hq hs hc
  have msg := Hmac256.signature_bound S hn rand seeds F c q qs hq hs hc
  have itsr := SmallItsr.small_itsr S hn rand seeds F c q qs hq hs hc
  have ud := Wots256.ud_signature S hn rand seeds F c q qs hq hs hc
  have pre := Wots256.pre_signature S hn rand seeds F c q qs hq hs hc
  have step := Wots256.tcr_signature S hn rand seeds F c q qs hq hs hc
  exact add_le_add le_rfl (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add msg itsr) (ar 2)) (ar S.vp.params.len)) (ar S.vp.params.k))
    (ar 1)) (mul_le_mul' le_rfl ud)) pre) step)

theorem small_euf_closed (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤ smallBound S c.ml q qs :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans (small_suf_closed S hn rand seeds F c q qs hq hs hc)

end Reduction.Compression
#print axioms Reduction.Compression.small_suf_closed
#print axioms Reduction.Compression.small_euf_closed
