import Link.Basic
import ToMathlib.Data.ByteArray

/-!
# Placeholder for the former `Link.Hash`

The single-set tree's `Link.Hash` (git commit `26aa3d8`) proved `Spec` = VCVio for the six hash
functions at SHA2-128s against that tree's single-set `Spec`; the six-set versions are in
`MLink/Hash.lean`.  Nothing of it is needed by `Reduction` (its one use, `Reduction.prf_128s_spec`,
was removed from `Reduction.PrfDomainNonVacuity`; its six-set replacement is `MReduction.prf_spec`).
The module is kept so that the imports of `Reduction` are unchanged.
-/
