import Link.Verify
import Link.Security

/-!
# The end-to-end statement

`Link.verify_eq` (in `Link/Verify.lean`): our specification's verifier *is* VCVio's executable
SLH-DSA-SHA2-128s verifier.

`Link.security_128s` (in `Link/Security.lean`): the scheme `romScheme prims.core …`, in which the
tweakable hash, `H_msg` and `PRF_msg` are three independent random oracles, is SUF-CMA secure with
the explicit bound `securityBound vp.params (256^16) 2 1 qh qs`.

The theorem below is the precise sense in which the two are about the same verification
algorithm: the verifier of the scheme the security theorem speaks about is an oracle program,
and running that program with its oracles answered by the SHA-2 functions of FIPS 205 §11.2.1
computes `Spec.slhVerifyInternal` on the FIPS wire encodings.  This is an identity of programs; it
does not (and no theorem here does) transfer the probability bound from random oracles to SHA-256.
-/

namespace Link

open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg

/-- The verification algorithm of the scheme covered by `security_128s`, with its random oracles
instantiated by the FIPS 205 SHA-2 functions, is our specification's `slh_verify_internal` on the
FIPS encodings of the signature and the public key. -/
theorem romScheme_verify_eq_spec (e : prims.SkSeed ≃ prims.Y)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (k : PublicKeyCore prims.core) (msg : Spec.Bytes)
    (s : GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (unifFwdAnswerImpl (romAnswer prims))
        ((romScheme (vp := vp) prims.core e optRand pkSeedDist).verify k (cv msg) s) =
      (pure (Spec.slhVerifyInternal msg (sigBytes s) (pkBytes k)) : ProbComp Bool) := by
  rw [romScheme_verify_eq, verify_eq_typed]

end Link

#print axioms Link.romScheme_verify_eq_spec
