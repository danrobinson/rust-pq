import Ideal.Realize.ForsAdv
import Ideal.Realize.ForsBound
open Ideal.Realize.Fors
example : True := by
  have h := chal_of_eq (vp := Link.vp) (prims := P₀) phase1P phase1P_def
  trivial
example : True := by
  have h := chal_of_eq (vp := Link.vp) (prims := P₀) phase1P
  trivial
