import Ideal.Direct.Bridge
import Ideal.Direct.Entry

/-!
# The entry point at the `PRF` table, per compression table

`sufI_le_extract`: the ideal-model SUF-CMA advantage of `suf_ideal_pure_closed_tight8`'s game
(`sufI S (optRandU oR) pkSeedDist`) is at most the table average, over a uniform compression
table `g`, of the probability that the run of the typed forger at `g` (the same forger as in
every existing composition, `S.typedS`) against the table signer at the `PRF` table of its key
is Cover, Hit, or HiddenEq (`Reduction.Direct.suf_real_le_extract` at the bundle
`primsG (liftC g)`).  The only inequality is the existing byte-to-typed transfer.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Ideal.Direct

open Reduction Reduction.Direct

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

open scoped Classical in
/-- **Entry point at the `PRF` table (SUF).** -/
theorem sufI_le_extract :
    sufI S (optRandU oR) pkSeedDist ≤ cfAvg fun g =>
      prTrue (pkSeedDist >>= fun pkSeed =>
        ($ᵗ (primsG (liftC g)).SkSeed : ProbComp (primsG (liftC g)).SkSeed) >>= fun k =>
        ($ᵗ (primsG (liftC g)).SkPrf : ProbComp (primsG (liftC g)).SkPrf) >>= fun skPrf =>
          g1Run (S.typedS (optRandU oR) pkSeedDist g) (prfTbl pkSeed k)
            (idealPk Link.vp (primsG (liftC g)) (prfTbl pkSeed k) pkSeed) skPrf >>= fun z =>
          pure (decide (evItsr pkSeed (prfTbl pkSeed k) z = true ∨
            evColl pkSeed (prfTbl pkSeed k) z = true ∨
            evHidF pkSeed (prfTbl pkSeed k) z ∨ evHidW pkSeed (prfTbl pkSeed k) z))) := by
  rw [sufI_eq_cfAvg]
  refine cfAvg_mono fun g => ?_
  refine (Reduction.bytes_strong_advantage_le _).trans ?_
  refine (le_of_eq (Reduction.strongAdvantage_eq_expW _)).trans ?_
  exact suf_real_le_extract (structuralG g) (S.typedS (optRandU oR) pkSeedDist g)

end Ideal.Direct

#print axioms Ideal.Direct.sufI_le_extract
