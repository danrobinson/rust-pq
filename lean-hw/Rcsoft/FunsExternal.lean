module
public import Rcsoft.Types
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std
namespace RcSoft

/-- The locked implementation uses a volatile read of element i of the static
80-word constant array. The extraction gate checks the pointer expression and
the proof checks all eighty entries of the upstream array. -/
def sha512.soft.unroll.rk (i : Usize) : Result U64 := Array.index_usize slhdsa.sha512.K i

end RcSoft
