import Reduction.Suf
import Reduction.Instance128s

/-!
# SUF-CMA at SLH-DSA-SHA2-128s

`slhdsa_suf_cma` at the bundle `Link.prims`; the only instance-specific obligation is
`structural_128s`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

/-- (Superseded by `Reduction.slhdsa_sha2_128s_suf_cma_final_split`, which uses the PRF game on
secret-key addresses and table-free adversaries.)
**SUF-CMA security of SLH-DSA-SHA2-128s in the standard model**: the EUF-CMA bound of
`slhdsa_sha2_128s_euf_cma` with the two PRF distinguishers replaced by their strong-forgery
variants; no hypothesis except the strong forger. -/
theorem slhdsa_sha2_128s_suf_cma
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : SignatureAlg.StrongUnforgeableAdversary
      (realAlg Link.vp Link.prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      bound pkSeedDist (bPrfW sufCheck S.toUnforgeableAdversary)
        (bPrfMsgW sufCheck S.toUnforgeableAdversary)
        (bItsr S.toUnforgeableAdversary) (bOpenPre S.toUnforgeableAdversary)
        (bTcr S.toUnforgeableAdversary)
        (rUd pkSeedDist (bWots S.toUnforgeableAdversary))
        (rPre pkSeedDist (bWots S.toUnforgeableAdversary))
        (rTcr pkSeedDist (bWots S.toUnforgeableAdversary)) :=
  slhdsa_suf_cma structural_128s S

#print axioms slhdsa_sha2_128s_suf_cma

end Reduction
