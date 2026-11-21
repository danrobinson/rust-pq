import Ideal.Realize.Chain
import Ideal.ComposeFinal
import Ideal.Transport.Verify
import Ideal.Transport.Sign
open OracleComp OracleSpec SLHDSA SLHDSA.Security Reduction
namespace Ideal.Realize
open Ideal.Transport Reduction.Open
abbrev P0 (g : CF St Blk) : Primitives Link.vp.params := setPrf (withTH Link.prims (thG g) (hmG g)) (prfG g) (pmG g)
variable (g : CF St Blk) (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16)) (n : ℕ)

example : (inferInstance : SampleableType (primsG (liftC g)).SkSeed) = (inferInstance : SampleableType (P0 g).SkSeed) := rfl
example : (inferInstance : Inhabited (primsG (liftC g)).Y) = (inferInstance : Inhabited (P0 g).Y) := rfl
example : (inferInstance : DecidableEq (primsG (liftC g)).AdrsKey) = (inferInstance : DecidableEq (P0 g).AdrsKey) := rfl
