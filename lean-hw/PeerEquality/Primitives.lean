import Kspongel.Top
import Rcni.Top
import Rcavx.Top
import Streamscalar.Top
import Kappleouter.Top

open Aeneas Aeneas.Std Result

namespace slhdsa.PeerEquality

/-- Equality of complete results for every starting state and block sequence. -/
theorem sha256_scalar_rustcrypto (st : Array U32 8#usize) (bs : Slice (Array U8 64#usize)) :
    StreamScalarRust.sha256.stream.scalar st bs = RcNiRust.sha256.x86_sha.compress st bs := by
  obtain ⟨a,ha,sa⟩ := spec_imp_exists (X86.Stream.scalar256 st bs)
  obtain ⟨b,hb,sb⟩ := spec_imp_exists (Intel.RustCrypto.compress_spec st bs)
  rw [ha,hb]
  congr 1
  apply Aeneas.Std.Array.ext
  have h := congrArg (List.map (fun w : BitVec 32 => (⟨w⟩ : U32))) (sa.trans sb.symm)
  simpa [wv,List.map_map,Function.comp_def] using h

theorem sha512_scalar_rustcrypto (st : Array U64 8#usize) (bs : Slice (Array U8 128#usize)) :
    StreamScalarRust.sha512.stream.scalar st bs = RcAvxRust.sha512.x86_avx2.compress st bs := by
  obtain ⟨a,ha,sa⟩ := spec_imp_exists (X86.Stream.scalar512 st bs)
  obtain ⟨b,hb,sb⟩ := spec_imp_exists (X86.RustCrypto512.compress_spec st bs)
  rw [ha,hb]
  congr 1
  apply Aeneas.Std.Array.ext
  have h := congrArg (List.map (fun w : BitVec 64 => (⟨w⟩ : U64))) (sa.trans sb.symm)
  simpa [S512.wv,List.map_map,Function.comp_def] using h

theorem shake256_apple_linux (input out : Slice U8) :
    KappleouterRust.shake256.shake256 input out = KspongeLRust.shake256.shake256 input out := by
  obtain ⟨a,ha,sa⟩ := spec_imp_exists (PlatformShake.Apple.shake256_fips input out)
  obtain ⟨b,hb,sb⟩ := spec_imp_exists (PlatformShake.Linux.shake256_fips input out)
  rw [ha,hb]
  congr 1
  exact Aeneas.Std.Slice.ext a b ((bytes_inj a.val b.val).mp (sa.trans sb.symm))

#print axioms sha256_scalar_rustcrypto
#print axioms sha512_scalar_rustcrypto
#print axioms shake256_apple_linux
end slhdsa.PeerEquality
