import Ideal.Realize.Chain
import Ideal.ComposeFinal
import Ideal.Transport.Verify
import Ideal.Transport.Sign
open OracleComp OracleSpec SLHDSA SLHDSA.Security Reduction
namespace Ideal.Realize
open Ideal.Transport Reduction.Open
abbrev P0 (g : CF St Blk) : Primitives Link.vp.params := setPrf (withTH Link.prims (thG g) (hmG g)) (prfG g) (pmG g)
variable (g : CF St Blk) (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16)) (n : ℕ)

example : Forger Link.vp (primsG (liftC g)) (optRandU oR g) d = Forger Link.vp (P0 g) (fun pk => oR pk.pkSeed pk.pkRoot) d := rfl
