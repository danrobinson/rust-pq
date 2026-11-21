import Ideal.Realize.ItsrReal
open OracleComp OracleSpec SLHDSA SLHDSA.Security KeyedHash
namespace Ideal.Realize.Itsr
open Reduction Reduction.Lazy Ideal.Realize Ideal.Itsr

variable (S : ForgerI) {qf : ℕ}
example (pk : PublicKeyCore P₀.core) : True := by
  have := typedP_bound (prims := P₀) codec₀ (fun i => isPortQ (S := List Byte) i)
    (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
  trivial

example (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) (pk : PublicKeyCore P₀.core) : IsQueryBoundP (typedP (prims := P₀) codec₀ S.main pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qf := by
  have := typedP_bound (prims := P₀) codec₀ (fun i => isPortQ (S := List Byte) i)
    (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk qf
  exact this (hqf _)
end Ideal.Realize.Itsr
