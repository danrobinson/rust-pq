# OPEN-O2 — item R2 (final checks of the `PRF_msg` distinguishers as hash queries; ITSR)

File: `Reduction/Open/MsgV.lean` (new; compiles with no error, no `sorry`; olean written to
`.lake/build/lib/lean/Reduction/Open/MsgV.olean`). Namespace `Reduction.Open`. No `ItsrV.lean`
(not needed, see 4). Imports: `Lazy.SufMsgLazy`, `Lazy.ItsrLazy`, `TcrMemo`, `Instance128sV2`,
`Open.WithHash`. Nothing existing was changed.

## Definitions
- `hashEmb : QueryImpl hspec (OracleComp (RSpec gspec D V hspec))` — forwards a hash query as
  the hash-kind query; `emb (Q : OracleComp hspec α) : OracleComp (RSpec gspec D V hspec) α :=
  simulateQ hashEmb Q` (a program over the hash oracle alone, read as an open program).
- `abbrev WinCheckO vp prims := PublicKeyCore prims.core → List Byte × SignatureCore vp prims.core
  → SigLog vp prims → OracleComp (publicHashSpec prims.core) Bool` (a final check as a program);
  `WinCheckO.eval wO : WinCheck vp prims := fun pk f log => simulateQ (PublicHash.impl prims) (wO pk f log)`.
- `eufCheckO pk msgs msg sig := (fun b => decide (msg ∉ msgs) && b) <$> verifyInternalM vp prims.core msg sig pk`
  (VCVio's Algorithm 20 with `H_msg`/`F`/`H`/`T_l` as queries); `sufCheckO : WinCheckO vp prims`
  `:= fun pk f log => (fun b => !signingLogContains log f.1 f.2 && b) <$> verifyInternalM … f.1 f.2 pk`.
- `msgPre A`, `msgPreW A` — the common prefix (seed, `openKeygen`, `runForger`/`runForgerSig`
  with `msgSignO`), returning `(pk, z)`.
- `def msgOpenV (A : Forger vp prims optRand pkSeedDist) : OracleComp (OSpec prims (msgG prims)) Bool :=
  msgPre A >>= fun x => emb (eufCheckO x.1 x.2.2 x.2.1.1 x.2.1.2)`
- `def msgOpenWV (wO : WinCheckO vp prims) (A : Forger …) : OracleComp (OSpec prims (msgG prims)) Bool :=
  msgPreW A >>= fun x => emb (wO x.1 x.2.1 x.2.2)`

## Equations (equality of PROGRAMS, as requested)
- `lazyRun_msgOpenV A : lazyRun (PublicHash.impl prims) (msgOpenV A) = bPrfMsgL A`
- `lazyRun_msgOpenWV wO A : lazyRun (PublicHash.impl prims) (msgOpenWV wO A) = bPrfMsgWL wO.eval A`
- `lazyRun_msgOpenWV_of_eval w wO (hw : wO.eval = w) A : lazyRun … (msgOpenWV wO A) = bPrfMsgWL w A`
- `sufCheckO_eval : sufCheckO.eval = sufCheck`; `eufCheckO_eval : simulateQ (PublicHash.impl prims)
  (eufCheckO pk msgs msg sig) = harnessValid pk msgs msg sig`
- `lazyRun_msgOpenWV_sufCheck A : lazyRun (PublicHash.impl prims) (msgOpenWV sufCheckO A) = bPrfMsgWL sufCheck A`
- `bPrfMsgL_eq_lazyRes_msgOpenV`, `bPrfMsgWL_eq_lazyRes_msgOpenWV`: the same with
  `simulateQ (interp (PublicHash.impl prims)) (lazyRes …)` on the right.
- `msgOpenV_tbl`, `msgOpenWV_tbl`: same `tblImpl` interpretation as `msgOpen A` / `msgOpenW wO.eval A`.
- Support: `simulateQ_emb` (any handler answering hash queries by `hI` maps `emb Q` to
  `pure (simulateQ hI Q)`), `simulateQ_lazyImpl_emb`, `simulateQ_tblImpl_emb`,
  `msgOpen_eq_pre`, `msgOpenW_eq_pre`.

## Counts (hypothesis `hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs`)
- `emb_kindBound K Q n (hQ : IsTotalQueryBound Q n) : IsQueryBoundP (emb Q) (fun t => kind t = K) (n * ind K .hash)`
- `verifyInternalQueryBound_eq : GeneralScheme.verifyInternalQueryBound vp.params = 1 + Resources2.verifyHashes vp`;
  `eufCheckO_total`, `sufCheckO_total : IsTotalQueryBound (…) (1 + Resources2.verifyHashes vp)`.
- `msgOpenV_kindBound A K (hK : K ≠ .unif) qs hA : IsQueryBoundP (msgOpenV A) (fun t => kind t = K)
  (keygenB vp (ind K .sec) (ind K .hash) + qs * (ind K .game + signB vp (ind K .sec) (ind K .hash))
   + (1 + Resources2.verifyHashes vp) * ind K .hash)`
- `msgOpenWV_kindBound wO n (hw : ∀ pk f log, IsTotalQueryBound (wO pk f log) n) A K hK qs hA`:
  the same with `n * ind K .hash`.
- `msgOpenV_hashes`, `lazyRes_msgOpenV_hashes`, `msgOpenWV_suf_hashes`, `lazyRes_msgOpenWV_suf_hashes`:
  hash kind `≤ keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)`.
- `msgOpenV_game`, `lazyRes_msgOpenV_game`, `msgOpenWV_suf_game`, `lazyRes_msgOpenWV_suf_game`: game kind `≤ qs`.
- `msgOpenV_sec`, `lazyRes_msgOpenV_draws`, `msgOpenWV_suf_sec`, `lazyRes_msgOpenWV_suf_draws`:
  sec kind / draws `≤ 2 ^ vp.params.hp * vp.params.len + qs * signReads vp` (as for `msgOpen`).
- 128s: `msgOpenV_hashes_128s`: all four hash bounds are `269824 + qs * 2007385 + 3929`
  (`verifyHashes Link.vp = 3928`, plus 1 for `H_msg`). Sec: `2^9·35 + qs·182784` (existing numerals).

## Independence of `Thash`/`Hmsg` (formal content of "no direct evaluation")
With `withTH`/`castForger` of `Open/WithHash.lean`:
- `msgOpenV_castForger T H A : msgOpenV (prims := withTH prims T H) (castForger T H A) = msgOpenV A` (`rfl`)
- `msgOpenWV_castForger T H A` (same for `msgOpenWV sufCheckO`), 
- `bPrfMsgL_castForger : bPrfMsgL (prims := withTH prims T H) (castForger T H A) =
  lazyRun (PublicHash.impl (withTH prims T H)) (msgOpenV (prims := prims) A)`, `bPrfMsgWL_castForger`
  (same with `sufCheck`/`sufCheckO`): the distinguisher over ANY `T`, `H` is the one fixed open
  program with hash queries answered by `T`, `H`. (`PRF`, `PRF_msg` live in `prims.core` and are
  not covered by these statements; by inspection the programs do not call them.)

## Item 4 (ITSR)
`Lazy.itsrOpen A` has NO final check: it returns `(z.1.2.randomness, (pkSeed, root, z.1.1))`.
Its components: `liftM pkSeedDist`, `liftM (optRand pk)` (unif), `openKeygen`, `openSign` (VCVio's
provider-parametric programs at the instance `openQ`, i.e. every `F`/`H`/`T_l`/`H_msg` is a
hash-kind query; secrets via `secQ`), `itsrRandomizerO` (a log lookup or one game query). So no
`itsrOpenV` is needed. Proven: `itsrOpen_castForger T H A : Lazy.itsrOpen (prims := withTH prims T H)
(castForger T H A) = Lazy.itsrOpen A`, and `bItsrL_castForger_main : (bItsrL (prims := withTH prims T H)
(castForger T H A)).main = lazyRun (PublicHash.impl (withTH prims T H)) (itsrOpen (prims := prims) A)`.
Existing counts `Lazy.itsrOpen_kindBound`, `bItsrL_hashes/draws/queryBound` therefore already
cover all its hash evaluations.

## Deviations from the request
1. `msgOpenWV` takes the OPEN check `wO : WinCheckO` (not a `WinCheck`); the headline instance is
   `msgOpenWV sufCheckO A` (not `msgOpenWV sufCheck A`). For a general `w` use
   `lazyRun_msgOpenWV_of_eval` with the hypothesis `wO.eval = w`.
2. Hash bound is `… + (1 + verifyHashes vp)`, not `… + verifyHashes vp`: `verifyHashes` (TcrMemo)
   excludes the `H_msg` evaluation of verification. The SUF check costs the same (one verification).
3. The verification program is VCVio's `verifyInternalM` over `publicHashSpec` embedded by `emb`,
   not `verifyFree` of `memoForgeOpen` (that one excludes `H_msg` and returns the root).
4. The 128s theorem states hash counts only; game/sec numerals follow from the general theorems.

## Not done
Nothing of R2 is left open. Not addressed (outside R2): `PRF`/`PRF_msg` independence as a theorem.

## Axioms (`#print axioms`, all 12 listed theorems)
`[propext, Classical.choice, Quot.sound]` for `lazyRun_msgOpenV`, `lazyRun_msgOpenWV_sufCheck`,
`msgOpenV_hashes`, `msgOpenV_game`, `msgOpenV_sec`, `lazyRes_msgOpenV_hashes`,
`lazyRes_msgOpenWV_suf_hashes`, `msgOpenV_castForger`, `itsrOpen_castForger`,
`bItsrL_castForger_main`, `bPrfMsgWL_castForger`, `msgOpenV_hashes_128s`.
