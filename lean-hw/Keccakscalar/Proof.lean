import Keccakscalar.Funs
import Slhdsa.Proofs.Keccak
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake

theorem scalar_eq : KeccakScalarRust.shake256.permute=shake256.permute := by
  have table : KeccakScalarRust.shake256.RC=shake256.RC := by
    simp only [KeccakScalarRust.shake256.RC,shake256.RC]
  unfold KeccakScalarRust.shake256.permute shake256.permute
    KeccakScalarRust.shake256.permute_loop shake256.permute_loop
    KeccakScalarRust.shake256.permute_loop.body shake256.permute_loop.body
  simp only [table]
  rfl

theorem scalar_permute (a : Array U64 25#usize) : KeccakScalarRust.shake256.permute a ⦃
    out => Keccak.words out=Spec.Keccak.permute (Keccak.words a) ⦄ := by
  rw [scalar_eq]
  exact Keccak.permute_spec a
end slhdsa.PlatformShake
