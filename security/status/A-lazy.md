# Package A (lazy): lazy `PRF_msg` and ITSR adversaries

New files (all compile, no `sorry`/`axiom`/`native_decide`; oleans written under
`.lake/build/lib/lean/Reduction/Lazy/`; axioms of every theorem below:
`[propext, Classical.choice, Quot.sound]`):

- `Reduction/Lazy/Open.lean` — shared open programs and counting.
- `Reduction/Lazy/MsgLazy.lean` — `bPrfMsgL`.
- `Reduction/Lazy/ItsrLazy.lean` — `bItsrL`.

Namespace `Reduction.Lazy`. `hspec := publicHashSpec prims.core`, `hI := PublicHash.impl prims`
(hash evaluations ARE countable queries), `D := SecIdx`, `V := prims.Y`.

## Open.lean
- `OSpec prims gspec := RSpec gspec SecIdx prims.Y (publicHashSpec prims.core)`.
- `secQ`, `gameQ`, `openKeygen prims gspec pkSeed`, `openSign prims gspec msg pkSeed pkRoot R`
  (VCVio's `keygenInternalWithSecretM` / `signInternalWithSecretRandomizerM` at provider `secQ`).
- `openKeygen_tbl : simulateQ (tblImpl (PublicHash.impl prims) g) (openKeygen prims gspec pkSeed) = pure (idealRoot vp prims g pkSeed)`;
  `openSign_tbl : … (openSign prims gspec msg pk.pkSeed pk.pkRoot R) = pure (idealSign vp prims g msg pk R)`.
- `evalDist_lazyRun_eq_table_run'` (`run'` variant of the Core theorem).
- Counting: `qb_*` (`IsQueryBoundP` for arbitrary predicate, budgets `cF cT cH cS`), `merkleB`,
  `authB`, `keygenB vp cS c`, `signB vp cS c`, `ind K K'`,
  `openKeygen_kindBound`, `openSign_kindBound`, closed forms `keygenB_sec` (`≤ 2^hp*len`),
  `signB_sec` (`≤ signReads vp`), `keygenB_hash` (`≤ keygenHashes vp`), `signB_hash`
  (`≤ signHashes vp`), `keygenB_game`, `signB_game` (`= 0`).
- `keygenHashes vp = 2^hp * (len*(w-1) + 2)`;
  `signHashes vp = 1 + k*(2^a*2) + (k*(1+a)+1) + d*(2^hp*(len*(w-1)+2) + (len*(w-1)+1+hp))`.

## MsgLazy.lean
- `msgOpen A : OracleComp (OSpec prims (msgG prims)) Bool`;
  `bPrfMsgL A : MsgPrfAdv prims := lazyRun (PublicHash.impl prims) (msgOpen A)`.
- `msgOpen_tbl`, `evalDist_prfReal_bPrfMsgL`, `evalDist_prfIdeal_bPrfMsgL`.
- `prfAdvantage_bPrfMsgL : (msgPrf vp prims).prfAdvantage (bPrfMsgL A) = (msgPrf vp prims).prfAdvantage (bPrfMsg A)`.
- `stepPRFmsg_lazy (A) : StepPRFmsg A (bPrfMsgL A)`.
- With `hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs`:
  - `bPrfMsgL_queryBound : IsQueryBoundP (bPrfMsgL A) (fun i => i.isRight = true) qs`
  - `bPrfMsgL_draws : IsQueryBoundP (lazyRes (msgOpen A)) (fun t => kind t = .sec) (2 ^ vp.params.hp * vp.params.len + qs * signReads vp)`
  - `bPrfMsgL_hashes : IsQueryBoundP (lazyRes (msgOpen A)) (fun t => kind t = .hash) (keygenHashes vp + qs * signHashes vp)`
  - `bPrfMsgL_gameRes` (game queries of `lazyRes (msgOpen A)` ≤ `qs`); `bPrfMsgL_eq` (`rfl`:
    `bPrfMsgL A = simulateQ (interp _) (lazyRes (msgOpen A))`).

## ItsrLazy.lean
- `itsrOpen A`, `bItsrL A : KeyedHash.ITSRAdversary (itsrProblem vp prims)` with
  `main := lazyRun (PublicHash.impl prims) (itsrOpen A)`.
- `evalDist_bItsrL_run : 𝒟[(bItsrL A).run] = 𝒟[(bItsr A).run]`.
- `itsrAdvantage_bItsrL : KeyedHash.ITSRAdvantage (bItsrL A) = KeyedHash.ITSRAdvantage (bItsr A)`.
- `stepITSR_lazy (A) : StepITSR A (bItsrL A)`.
- `bItsrL_queryBound` (on `(bItsrL A).main`, ≤ `qs`), `bItsrL_draws`, `bItsrL_hashes`,
  `bItsrL_gameRes`, `bItsrL_main_eq` — same shapes/bounds as for `bPrfMsgL`, on
  `lazyRes (itsrOpen A)`.

## Caveats
- The hash count covers key generation and signing. Not counted: the single final
  `verifyInternal` inside `harnessValid` of `msgOpen` (evaluated inline as a pure function; a
  fixed number of hash calls), the forger's own computation, and list work (cache lookups,
  transcript `find?`).
- `signHashes` is an upper bound, not exact (chain lengths bounded by `w-1`, `2^z - 1` by `2^z`).
- No named hypotheses left.
