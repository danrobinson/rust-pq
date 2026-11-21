import Ideal.Realize.TcrCount
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport
attribute [local irreducible] Reduction.Lazy.sparseTable


theorem xx : IsQueryBoundP (tcrChooseHF Link.vp P₀) (fun t => bad0 (Tweak := P₀.AdrsKey) (Y := P₀.Y) Bmax t = true) 0 :=
    sorry
end Ideal.Realize.Tcr
