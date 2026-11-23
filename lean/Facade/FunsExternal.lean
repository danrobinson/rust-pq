module
public import Facade.Types
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

namespace slh_dsa
def core.bool.Bool.then_some {T : Type} (b : Bool) (x : T) : Result (Option T) :=
  ok (if b then some x else none)
def signature.error.Error.new : Result signature.error.Error := ok ()

def core.option.Option.ok_or_else {T E F : Type _} (f : Aeneas.Std.core.ops.function.FnOnce F Unit E)
    (o : Option T) (closure : F) : Result (Aeneas.Std.core.result.Result T E) := do
  match o with
  | some x => ok (.Ok x)
  | none => do
    let e ← f.call_once closure ()
    ok (.Err e)

def const_oid.ObjectIdentifier.as_bytes {n : Usize} (oid : const_oid.ObjectIdentifier n) := ok oid
def der.asn1.bit_string.BitStringRef.as_bytes (s : der.asn1.bit_string.BitStringRef) := ok s
def der.asn1.octet_string.OctetStringRef.as_bytes (s : der.asn1.octet_string.OctetStringRef) := ok s
def der.tag.Tag.value_error (t : der.tag.Tag) := ok (der.error.ErrorKind.Value t)
def der.error.ErrorKind.to_error (_ : der.error.ErrorKind) : Result der.error.Error := ok ()
def spki.error.Error.Insts.CoreConvertFromError.from (e : der.error.Error) := ok (spki.error.Error.Asn1 e)
def pkcs8.error.Error.Insts.CoreConvertFromError.from (e : spki.error.Error) := ok (pkcs8.error.Error.PublicKey e)
def pkcs8.error.Error.Insts.CoreConvertFromKeyError.from (e : pkcs8.error.KeyError) := ok (pkcs8.error.Error.KeyMalformed e)

/-- DER contents of NIST signature OIDs under 2.16.840.1.101.3.4.3. -/
def slhOid (id : U8) : Slice U8 :=
  (Array.make 9#usize [0x60#u8, 0x86#u8, 0x48#u8, 1#u8, 0x65#u8, 3#u8, 4#u8, 3#u8, id]).to_slice

abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHA_2_128_S := Result.ok (slhOid 20#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHA_2_128_F := Result.ok (slhOid 21#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHA_2_192_S := Result.ok (slhOid 22#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHA_2_192_F := Result.ok (slhOid 23#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHA_2_256_S := Result.ok (slhOid 24#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHA_2_256_F := Result.ok (slhOid 25#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHAKE_128_S := Result.ok (slhOid 26#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHAKE_128_F := Result.ok (slhOid 27#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHAKE_192_S := Result.ok (slhOid 28#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHAKE_192_F := Result.ok (slhOid 29#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHAKE_256_S := Result.ok (slhOid 30#u8)
abbrev const_oid.db.generated.fips205.ID_SLH_DSA_SHAKE_256_F := Result.ok (slhOid 31#u8)

/-- Functional effect of overwriting a value in the zeroize crate. -/
def zeroize.Zeroize.Blanket.zeroize {Z : Type} (z : zeroize.DefaultIsZeroes Z) (_ : Z) :
    Result Z := z.coredefaultDefaultInst.default

def Slice.Insts.ZeroizeZeroize.zeroize {Z : Type} (z : zeroize.DefaultIsZeroes Z)
    (s : Slice Z) : Result (Slice Z) := do
  let value ← z.coredefaultDefaultInst.default
  ok (Slice.from (List.replicate s.val.length value) (by simpa using s.property))

def Array.Insts.ZeroizeZeroize.zeroize {Z : Type} {N : Usize} (z : zeroize.Zeroize Z)
    (a : Std.Array Z N) : Result (Std.Array Z N) := do
  let xs ← List.mapM_with_length z.zeroize a.val
  ok (Std.Array.from xs.val (xs.property.trans a.property))

abbrev slhdsa.sets.sha2_128s.params.N := Result.ok _root_.slhdsa.sets.sha2_128s.params.N
abbrev slhdsa.sets.sha2_128s.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_128s.params.PARAMS
abbrev slhdsa.sets.sha2_128s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_128s.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_128s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_128s.SPKI_PREFIX
abbrev slhdsa.sets.sha2_128f.params.N := Result.ok _root_.slhdsa.sets.sha2_128f.params.N
abbrev slhdsa.sets.sha2_128f.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_128f.params.PARAMS
abbrev slhdsa.sets.sha2_128f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_128f.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_128f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_128f.SPKI_PREFIX
abbrev slhdsa.sets.sha2_192s.params.N := Result.ok _root_.slhdsa.sets.sha2_192s.params.N
abbrev slhdsa.sets.sha2_192s.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_192s.params.PARAMS
abbrev slhdsa.sets.sha2_192s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_192s.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_192s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_192s.SPKI_PREFIX
abbrev slhdsa.sets.sha2_192f.params.N := Result.ok _root_.slhdsa.sets.sha2_192f.params.N
abbrev slhdsa.sets.sha2_192f.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_192f.params.PARAMS
abbrev slhdsa.sets.sha2_192f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_192f.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_192f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_192f.SPKI_PREFIX
abbrev slhdsa.sets.sha2_256s.params.N := Result.ok _root_.slhdsa.sets.sha2_256s.params.N
abbrev slhdsa.sets.sha2_256s.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_256s.params.PARAMS
abbrev slhdsa.sets.sha2_256s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_256s.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_256s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_256s.SPKI_PREFIX
abbrev slhdsa.sets.sha2_256f.params.N := Result.ok _root_.slhdsa.sets.sha2_256f.params.N
abbrev slhdsa.sets.sha2_256f.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_256f.params.PARAMS
abbrev slhdsa.sets.sha2_256f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_256f.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_256f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_256f.SPKI_PREFIX
abbrev slhdsa.sets.shake_128s.params.N := Result.ok _root_.slhdsa.sets.shake_128s.params.N
abbrev slhdsa.sets.shake_128s.params.PARAMS := Result.ok _root_.slhdsa.sets.shake_128s.params.PARAMS
abbrev slhdsa.sets.shake_128s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.shake_128s.PKCS8_PREFIX
abbrev slhdsa.sets.shake_128s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.shake_128s.SPKI_PREFIX
abbrev slhdsa.sets.shake_128f.params.N := Result.ok _root_.slhdsa.sets.shake_128f.params.N
abbrev slhdsa.sets.shake_128f.params.PARAMS := Result.ok _root_.slhdsa.sets.shake_128f.params.PARAMS
abbrev slhdsa.sets.shake_128f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.shake_128f.PKCS8_PREFIX
abbrev slhdsa.sets.shake_128f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.shake_128f.SPKI_PREFIX
abbrev slhdsa.sets.shake_192s.params.N := Result.ok _root_.slhdsa.sets.shake_192s.params.N
abbrev slhdsa.sets.shake_192s.params.PARAMS := Result.ok _root_.slhdsa.sets.shake_192s.params.PARAMS
abbrev slhdsa.sets.shake_192s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.shake_192s.PKCS8_PREFIX
abbrev slhdsa.sets.shake_192s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.shake_192s.SPKI_PREFIX
abbrev slhdsa.sets.shake_192f.params.N := Result.ok _root_.slhdsa.sets.shake_192f.params.N
abbrev slhdsa.sets.shake_192f.params.PARAMS := Result.ok _root_.slhdsa.sets.shake_192f.params.PARAMS
abbrev slhdsa.sets.shake_192f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.shake_192f.PKCS8_PREFIX
abbrev slhdsa.sets.shake_192f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.shake_192f.SPKI_PREFIX
abbrev slhdsa.sets.shake_256s.params.N := Result.ok _root_.slhdsa.sets.shake_256s.params.N
abbrev slhdsa.sets.shake_256s.params.PARAMS := Result.ok _root_.slhdsa.sets.shake_256s.params.PARAMS
abbrev slhdsa.sets.shake_256s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.shake_256s.PKCS8_PREFIX
abbrev slhdsa.sets.shake_256s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.shake_256s.SPKI_PREFIX
abbrev slhdsa.sets.shake_256f.params.N := Result.ok _root_.slhdsa.sets.shake_256f.params.N
abbrev slhdsa.sets.shake_256f.params.PARAMS := Result.ok _root_.slhdsa.sets.shake_256f.params.PARAMS
abbrev slhdsa.sets.shake_256f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.shake_256f.PKCS8_PREFIX
abbrev slhdsa.sets.shake_256f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.shake_256f.SPKI_PREFIX
end slh_dsa
