import Reduction.Main
import Reduction.PRFHop
import Reduction.PRFMsgHop
import Reduction.ITSR
import Reduction.OpenPRE
import Reduction.TCR
import Reduction.WotsEmbed
import Reduction.WotsUD
import Reduction.WotsFinal

/-!
# The final theorem

`slhdsa_euf_cma` is the unconditional statement: `final_of_steps` at the nine (choice-free, not
feasible; see below) reduction adversaries, with the nine step lemmas supplied.

**Superseded** (phase 2) by `Reduction.slhdsa_euf_cma_final` and `Reduction.slhdsa_suf_cma_final`
(`Reduction/Headline.lean`): PRF game on the secret-key address domain (the game `skPrf` used here
is false at SHA2-128s, `skPrf_broken_128s`), no eager table, FORS term `SM-DSPR + 3·SM-TCR`,
strong unforgeability; and those in turn by `slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_split`
(`Reduction/HeadlineSplit.lean`, per-function SM-TCR terms, twelve advantages).
The statements below are unchanged and still proved.  Everything is proved (no admitted lemma), and
the theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (see `#print axioms` at
the end of this file).

Corollaries: `slhdsa_euf_cma_uniform_seed` (the FIPS 205 scheme, `PK.seed` uniform) and
`slhdsa_euf_cma_resources` (the bound together with the proved query bounds of the three
reductions whose resources depend on the number `qs` of signing queries).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- **Standard-model EUF-CMA security of SLH-DSA (FIPS 205 internal algorithms).**
(Phase 1; superseded by `Reduction.slhdsa_euf_cma_final_split` / `slhdsa_suf_cma_final_split`,
`Reduction/HeadlineSplit.lean`.)

For every chosen-message forger `A` against `internalAlg vp prims optRand pkSeedDist`, the
adversaries `bPrf A`, `bPrfMsg A`, `bItsr A`, `bOpenPre A`, `bTcr A` and
`rUd/rPre/rTcr (bWots A)` — each a choice-free definition running `A` once; only `bPrf A` is
polynomial in the number of signing queries as written — satisfy

`Adv^{EUF-CMA}(A) ≤ Adv^{PRF}_{PRF}(bPrf A) + Adv^{PRF}_{PRF_msg}(bPrfMsg A)
   + Adv^{ITSR}_{H_msg}(bItsr A) + Adv^{SM-OpenPRE}_{F}(bOpenPre A) + Adv^{SM-TCR}_{Thash}(bTcr A)
   + (w-2)·Adv^{SM-UD}_{F}(rUd (bWots A)) + Adv^{SM-PRE}_{F}(rPre (bWots A))
   + Adv^{SM-TCR}_{F}(rTcr (bWots A))`.

`Structural vp prims` is non-cryptographic: injective node and address encodings and FIPS address
widths.  No random oracle and no idealised primitive occurs.

What is and is not claimed about the reductions:

* no choice principle occurs in the definition of any of the nine adversaries; each is black-box
  in `A`, straight-line (no rewinding), and runs `A` exactly once.  This is not an efficiency
  statement: see the last item;
* target and query caps: the SM games enforce their caps (`tcrTargets`, `openPreTargets`,
  `wotsChainTargets`, `wotsStepTargets`, all independent of the number of signing queries), and
  the reductions never exceed them (no query is refused); the `qs`-dependent counts are
  `bPrf_queryBound_exact`, `bPrfMsg_queryBound`, `bItsr_queryBound`
  (packaged in `slhdsa_euf_cma_resources`).  The caps are exponential in `h`: at 128s
  `openPreTargets = 14·2^75 ≈ 2^78.81`, `tcrTargets ≈ 2^79.81`, `wotsChainTargets ≈ 2^68.13`,
  `wotsStepTargets ≈ 2^72.13` (`Reduction/Resources.lean`).  `bOpenPre` and `bTcr` issue exactly
  the cap in every run; `rUd`, `rPre` issue at most `#inst·len` and `rTcr` at most
  `#inst·len·(w−1)` (below its cap `#inst·len·w`) in every run, for every `W`;
* the bound is tight in advantage (every coefficient is `1` except `w − 2`); nothing is claimed
  about the tightness in running time;
* **no running-time claim is made.**  As written `bPrfMsg`, `bItsr`, `bOpenPre`, `bTcr`, `bWots`
  sample the eager `2^256`-cell `sampleTable` and are not feasible.  `Reduction/Lazy/` gives
  variants with the same advantage: `bPrfMsgL`, `bItsrL` are polynomial in `qs`; the SM
  adversaries (`bOpenPre`, `bTcr`, `bWots` and hence `rUd/rPre/rTcr (bWots A)`) necessarily
  evaluate the whole key structure once (`≈ 2^79.81` `Thash` and `≈ 2^78.81` `PRF`-replacing
  samples at 128s, `Resources.structHashEvals_128s`, `structPrfEvals_128s`), because all targets
  must be fixed before `PK.seed` is revealed.

Deviations from Hülsing–Kudinov (ePrint 2022/346) Theorem 1: one SM-TCR game on the
variable-arity `Thash` (a cross-arity collision also wins; cap = all hash calls of the key
structure) instead of four per-function games; SM-DT-OpenPRE on `F` is assumed directly instead
of being reduced to SM-TCR + SM-DSPR; the PRF and ITSR adversaries choose `PK.seed` themselves.
Scope of this theorem: EUF-CMA, single key, FIPS 205 internal algorithms (Alg. 18–20).  (All
three deviations and the scope are lifted later: per-function SM-TCR terms, `SM-DSPR + 3·SM-TCR`,
SUF-CMA and the external interface in `Reduction/HeadlineSplit.lean`.) -/
theorem slhdsa_euf_cma (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A)) :=
  final_of_steps A (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A) (bWots A)
    (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A))
    (stepPRF hS A) (stepPRFmsg A) (stepSplit A) (stepITSR A) (stepOpenPRE hS A) (stepTCR hS A)
    (stepWotsEmbed hS A) (stepWotsUD hS pkSeedDist (bWots A))
    (stepWotsFinal hS pkSeedDist (bWots A))

/-- **The FIPS 205 scheme: `PK.seed` uniform.**  `slhdsa_euf_cma` at `pkSeedDist := $ᵗ PkSeed`;
all SM games then draw their seed uniformly, as in the literature. -/
theorem slhdsa_euf_cma_uniform_seed [SampleableType prims.PkSeed] (hS : Structural vp prims)
    (A : Forger vp prims optRand ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound ($ᵗ prims.PkSeed) (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd ($ᵗ prims.PkSeed) (bWots A)) (rPre ($ᵗ prims.PkSeed) (bWots A))
        (rTcr ($ᵗ prims.PkSeed) (bWots A)) :=
  slhdsa_euf_cma hS A

/-- **The bound with the `qs`-dependent resources of the reductions.**  If the forger makes at
most `qs` signing queries, then besides the bound: `bPrf A` makes at most
`2^h'·len + qs·(k·2^a + d·2^h'·len)` PRF-oracle queries, `bPrfMsg A` at most `qs`
`PRF_msg`-oracle queries, and `bItsr A` at most `qs` ITSR target queries.  The numbers of targets
of the five SM adversaries do not depend on `qs` because they cover the whole key structure:
between `2^68` and `2^80` at 128s (`Reduction/Resources.lean`).  No running-time statement is
included (see `slhdsa_euf_cma`).  Superseded by `Reduction.final_resources`. -/
theorem slhdsa_euf_cma_resources (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        bound pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
          (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A)) ∧
      IsQueryBoundP (bPrf A) (fun i => i.isRight = true)
        (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) ∧
      IsQueryBoundP (bPrfMsg A) (fun i => i.isRight = true) qs ∧
      IsQueryBoundP (bItsr A).main (fun i => i.isRight = true) qs :=
  ⟨slhdsa_euf_cma hS A, bPrf_queryBound_exact A qs hA, bPrfMsg_queryBound A qs hA,
    bItsr_queryBound A qs hA⟩

#print axioms slhdsa_euf_cma
#print axioms slhdsa_euf_cma_uniform_seed
#print axioms slhdsa_euf_cma_resources

end Reduction
