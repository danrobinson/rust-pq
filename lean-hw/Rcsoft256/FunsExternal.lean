module
public import Rcsoft256.Types
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std
namespace RcSoft256

/-- The locked implementation uses a volatile read of element i of the static
64-word constant array. The extraction gate checks the pointer expression and
the proof checks all sixty-four entries of the upstream array. -/
def sha256.soft.unroll.rk (i : Usize) : Result U32 := Array.index_usize slhdsa.sha256.K i

end RcSoft256
