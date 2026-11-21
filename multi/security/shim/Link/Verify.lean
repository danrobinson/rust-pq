import Link.Hash
import HashSig.SLHDSA.External

/-!
# Stand-in for `security/Link/Verify.lean` (the two Spec-free abbreviations, verbatim)
-/

namespace Link

open SLHDSA SLHDSA.Concrete

/-- VCVio's strict FIPS decoder of a signature for SLH-DSA-SHA2-128s. -/
abbrev decodeSig (raw : List UInt8) :
    Except CodecError (GeneralScheme.SignatureCore vp prims.core) :=
  decodeApprovedSignature S128 raw

/-- VCVio's strict FIPS decoder of a public key for SLH-DSA-SHA2-128s. -/
abbrev decodePk (raw : List UInt8) : Except CodecError (PublicKeyCore prims.core) :=
  decodeApprovedPublicKey S128 raw

end Link
