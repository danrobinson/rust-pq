import Link.Basic
import ToMathlib.Data.ByteArray

/-!
# Stand-in for `security/Link/Hash.lean`

The original proves `Spec` = VCVio for the six hash functions at SHA2-128s against the single-set
`Spec`; the six-set versions are in `MLink/Hash.lean`.  Nothing of it is needed by the modules of
`security/Reduction` compiled here (its one use, `Reduction.prf_128s_spec`, is omitted from the
stand-in `Reduction.PrfDomainNonVacuity` and replaced by `MLink.PRF_eq`).
-/
