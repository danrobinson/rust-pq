import Reduction.FinalV2
import Reduction.PrfDomainNonVacuity
import Reduction.Resources

/-!
# Version 2 at SLH-DSA-SHA2-128s

`slhdsa_sha2_128s_euf_cma_v2`: `slhdsa_euf_cma_v2` at `Link.vp`, `Link.prims`; no hypothesis
besides the forger.  `slhdsa_sha2_128s_euf_cma_v2_resources` adds the `qs`-dependent counts with
the numerals of SHA2-128s (`2^h'·len = 17920`, `signReads = 182784`, `k = 14`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

/-- **EUF-CMA security of SLH-DSA-SHA2-128s in the standard model, version 2.** -/
theorem slhdsa_sha2_128s_euf_cma_v2
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundV2 pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A) (Lazy.bOpenPreS A)
        (Lazy.bTcrS A) (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcr pkSeedDist (Lazy.bWotsS A)) :=
  slhdsa_euf_cma_v2 structural_128s A

/-- Form `∀ A, Adv A ≤ β A` at SHA2-128s. -/
theorem slhdsa_sha2_128s_euf_cma_v2'
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed) :
    ∀ A : Forger Link.vp Link.prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaV2 A :=
  slhdsa_euf_cma_v2' structural_128s

/-- The bound with the `qs`-dependent query counts at SHA2-128s, as numerals. -/
theorem slhdsa_sha2_128s_euf_cma_v2_resources
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaV2 A ∧
      IsQueryBoundP (bPrfC A) (fun i => i.isRight = true) (17920 + qs * 182784) ∧
      IsQueryBoundP (Lazy.bPrfMsgL A) (fun i => i.isRight = true) qs ∧
      IsQueryBoundP (Lazy.bItsrL A).main (fun i => i.isRight = true) qs ∧
      ∀ st pkSeed ys, IsQueryBoundP ((Lazy.bOpenPreS A).find st pkSeed ys)
        (fun i => i.isRight = true) (qs * 14) := by
  have h := slhdsa_euf_cma_v2_resources structural_128s A qs hA
  rw [Resources.keygenReads_128s, Resources.signReads_128s] at h
  exact h

#print axioms slhdsa_sha2_128s_euf_cma_v2
#print axioms slhdsa_sha2_128s_euf_cma_v2_resources

end Reduction

namespace Reduction

/-- Hash evaluations of key generation at SHA2-128s (closed form of `Lazy.keygenHashes`). -/
theorem keygenHashes_128s : Lazy.keygenHashes Link.vp = 269824 := by decide

/-- Hash evaluations of one signature at SHA2-128s (closed form of `Lazy.signHashes`). -/
theorem signHashes_128s : Lazy.signHashes Link.vp = 2007385 := by decide

end Reduction
