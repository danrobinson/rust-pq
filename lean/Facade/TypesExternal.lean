module
public import Slhdsa.Types
@[expose] public section
open Aeneas Aeneas.Std
namespace slh_dsa

-- Observations exported by the external DER parser and its accessors.
abbrev const_oid.ObjectIdentifier (_max : Usize) := Slice U8
abbrev der.asn1.octet_string.OctetStringRef := Slice U8
abbrev der.asn1.bit_string.BitStringRef := Option (Slice U8)
abbrev der.asn1.any.AnyRef := Slice U8
abbrev der.length.Length := Nat
abbrev core.str.error.Utf8Error := Unit
-- The API theorem observes the ASN.1 error category, independent of its position.
abbrev der.error.Error := Unit

-- Type-only typenum indices in the sealed family implementations.
structure typenum.uint.UInt (U B : Type) where
  marker : U × B

end slh_dsa
