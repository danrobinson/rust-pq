import Link.Hash
import HashSig.SLHDSA.External

/-!
# VCVio's signature and public-key decoders at SLH-DSA-SHA2-128s

The two Spec-free abbreviations of the single-set tree's `Link.Verify` (git commit `26aa3d8`),
verbatim; its `Spec` = VCVio verification proofs are, for all six sets, `MLink/Verify.lean`.
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
