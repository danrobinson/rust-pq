import Reduction.Final
import Link.Basic

/-!
# Instantiation at SLH-DSA-SHA2-128s

The phase-1 theorem `slhdsa_euf_cma` at the bundle `Link.prims` (VCVio's executable SHA-2 primitives, proved equal to
our FIPS 205 transcription in `Link`), `d = 7`, `h' = 9`, `w = 16`.  The only obligation specific
to the instance is `structural_128s`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

instance : Inhabited Link.prims.Y := ⟨Vector.replicate 16 0⟩

/-- The structural side conditions hold for SLH-DSA-SHA2-128s: `Bytes 16` nodes are their own
encoding, the compressed address `ADRSc` is injective on in-range addresses
(`Adrs.compressSha2_injective_of_fits`), and the FIPS widths hold (`fipsApprovedAddressBounds`). -/
theorem structural_128s : Structural Link.vp Link.prims :=
  have hb : ApprovedAddressBounds Link.vp.params := fipsApprovedAddressBounds Link.S128
  ⟨Concrete.sha2Primitives_byteLaws Link.vp.params,
    Concrete.keyInjective_sha2Primitives Link.vp hb, hb.toCanonicalAddressBounds⟩

/-- The full VCVio key discipline at SLH-DSA-SHA2-128s; beyond `structural_128s` it also gives
key separation (`KeySeparated`), which `Structural` does not ask for. -/
theorem keyDiscipline_128s : Link.prims.core.KeyDiscipline Link.vp :=
  Concrete.keyDiscipline_sha2Primitives Link.vp (fipsApprovedAddressBounds Link.S128)

/-- (Phase 1; superseded by `Reduction.slhdsa_sha2_128s_euf_cma_final_split` and
`slhdsa_sha2_128s_suf_cma_final_split`, `Reduction/HeadlineSplit.lean`.)
**EUF-CMA security of SLH-DSA-SHA2-128s in the standard model**, with coefficient
`w - 2 = 14` on the undetectability term. -/
theorem slhdsa_sha2_128s_euf_cma
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A)) :=
  slhdsa_euf_cma structural_128s A

#print axioms structural_128s
#print axioms keyDiscipline_128s
#print axioms slhdsa_sha2_128s_euf_cma

end Reduction
