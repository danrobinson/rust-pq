-- Generated from locked RustCrypto SHA-2 initialization constants.
import Spec.Sha512
import Spec.Sha256

namespace slhdsa.RcSlhSha2
open Spec

def initial256 : List SHA256.Word := [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19]
theorem initial256_eq : initial256 = SHA256.H0 := rfl

def initial512 : List SHA512.Word := [0x6a09e667f3bcc908,0xbb67ae8584caa73b,0x3c6ef372fe94f82b,0xa54ff53a5f1d36f1,0x510e527fade682d1,0x9b05688c2b3e6c1f,0x1f83d9abfb41bd6b,0x5be0cd19137e2179]
theorem initial512_eq : initial512 = SHA512.H0 := rfl

end slhdsa.RcSlhSha2
