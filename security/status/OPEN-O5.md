# OPEN-O5 — R3 / R7, second phases of `rUd`, `rPre`, `rTcrT` at `Lazy.bWotsS A`

File: `Reduction/Open/Wots.lean` (new; namespace `Reduction.Open`; imports `Open/WithHash`,
`Resources2Wots`, `TightCapsHeadline`). Compiles with no error/warning; olean written
(`.lake/build/lib/lean/Reduction/Open/Wots.olean`). No `sorry`/`axiom`/`native_decide`.
Nothing existing was edited. Everything requested is done; no conditional theorems.
## Result
Each second phase EQUALS `simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) P` for an open program
`P : OracleComp (Lazy.OSpec prims gspec) _` with NO post-processing; `P` is invariant under
`withTH prims T H` (all `T`, `H`), so no `prims.Thash`/`prims.Hmsg` evaluation is outside the oracle.
## Direct `prims` evaluations found in the old `wots_r*_phase2_eq` and how closed
Only one: `wotsAnswer tbl hist ⟨pk,root⟩ msg sig` inside `wotsPhase2O` (pure; also takes `tbl`).
Replaced by `wotsAnswerOpen` (table read via `secQ`). `wotsWinO`/`wotsPreAnswerO`/`wotsTcrAnswerO`
(wrapper chain completions) were already open and are reused.
## Definitions (heads)
```
def layerStepM (core) {m} [Monad m] [HasQuery (publicHashSpec core) m] (pk adrs idx sig msg) : m (Vector core.Y len × core.Y)
def layerTraceM (core) {m} … (pkSeed parts s m0) : ℕ → m (List (core.Y × Vector core.Y len) × core.Y)
def wotsAnswerOf (hist parts sig) (fl rl : List (prims.Y × Vector prims.Y len)) : ℕ × prims.Y × WotsSig …  -- comparisons only
def wotsAnswerOpen (hist : List (WotsGame.Entry prims)) (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × prims.Y × WotsSig vp.params prims.core)
noncomputable def wotsPhase2All (A) (hist) (root) (pk) {β} (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
    OracleComp (Lazy.OSpec prims gspec) β) : OracleComp (Lazy.OSpec prims gspec) β :=
  wotsForgeOpen A hist root pk >>= fun r => wotsAnswerOpen hist ⟨pk, root⟩ r.1.1 r.1.2 >>= tail
noncomputable def wotsUdOpenAll  (A) (hist hist2) (root) (pk) : OracleComp (Lazy.OSpec prims gspec) Bool
noncomputable def wotsPreOpenAll (A) (hist hist2) (root) (pk) : OracleComp (Lazy.OSpec prims gspec) (ℕ × prims.Y)
noncomputable def wotsTcrOpenAll (A) (hist hist2) (root) (pk) : OracleComp (Lazy.OSpec prims gspec) (ℕ × prims.Y)
def wotsAnswerHashes (vp) : ℕ := 1 + wotsSignHistHashes vp + 2*(k*(1+a)+1) + 2*(d*(len*(w-1)+1+hp))
```
`wotsAnswerOpen` is MEMOISED: one `hmsg` query, `wotsSignFromHistO`, two `forsPkFromSigM`, and per
signature one pass of `d` layer steps (chain ends, `T_len`, climb computed once per layer).
## Theorems (verbatim statements, binders abbreviated)
```
theorem wotsAnswerOpen_tbl (tbl hist pk msg sig) :
  simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) (wotsAnswerOpen hist pk msg sig) =
    pure (wotsAnswer tbl hist pk msg sig)
theorem wotsAnswerOpen_kindBound (K) … (fun t => Lazy.kind t = K) (wotsAnswerB vp (Lazy.ind K .sec) (Lazy.ind K .hash))
theorem wotsAnswerOpen_hashes (hist pk msg sig) :
  IsQueryBoundP (wotsAnswerOpen (gspec := gspec) hist pk msg sig) (fun t => Lazy.kind t = .hash) (wotsAnswerHashes vp)
theorem wotsAnswerHashes_128s : wotsAnswerHashes Link.vp = 129714
theorem wotsUd_phase2_open_eq (A) (tbl) (hist hist2) (root) (pk) :
  (liftM ((rUd pkSeedDist (Lazy.bWotsS A)).distinguish ((tbl, hist, root), hist2) pk) : OracleComp (unifSpec + gspec) Bool) =
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) (wotsUdOpenAll A hist hist2 root pk)
theorem wotsPre_phase2_open_eq   … (rPre pkSeedDist (Lazy.bWotsS A)).invert …  = simulateQ … (wotsPreOpenAll A hist hist2 root pk)
theorem wotsTcrT_phase2_open_eq  … (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).forge … = simulateQ … (wotsTcrOpenAll A hist hist2 root pk)
theorem wotsTcr_phase2_open_eq   … same for rTcr
theorem wotsUd_phase2_open_hashes (A) (qs) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) (hist hist2 root pk) :
  IsQueryBoundP (wotsUdOpenAll (gspec := gspec) A hist hist2 root pk) (fun t => Lazy.kind t = .hash)
    (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsWinHashes vp))
theorem wotsPre_phase2_open_hashes  … (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsPreHashes vp))
theorem wotsTcrT_phase2_open_hashes … (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsTcrHashes vp))
theorem wotsUd_phase2_open_hashes_128s   … (qs * 121857 + 130239)      -- at Link.vp / Link.prims
theorem wotsPre_phase2_open_hashes_128s  … (qs * 121857 + 130274)
theorem wotsTcrT_phase2_open_hashes_128s … (qs * 121857 + 146514)
theorem wotsUdOpenAll_hashfree (T H A hist hist2 root pk) :
  wotsUdOpenAll (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist hist2 root pk =
    wotsUdOpenAll (gspec := gspec) A hist hist2 root pk   -- likewise wotsPre/TcrOpenAll_, wotsAnswerOpen_, wotsForgeOpen_hashfree
theorem wotsPhase2All_reads … (fun t => Lazy.kind t = .sec) ((qs + 1) * (vp.params.k * 2 ^ vp.params.a))
theorem wotsPhase2All_game  … (fun t => Lazy.kind t = .game) 0        -- for sec-/game-free tails
```
R7: `wotsUd/wotsPre/wotsTcrT_phase2_open_eq_main (main : PublicKeyCore prims.core → OracleComp (unifSpec +
(List Byte →ₒ SignatureCore)) (List Byte × SignatureCore))` — the same equalities at the forger `⟨main⟩`
(a `Forger` is exactly its `main`); `wotsForgeOpen_eq_main`: `wotsForgeOpen A hist root pk` is
`StateT.run (simulateQ (ofLift.liftTarget + logSignOracle optRand ⟨pk,root⟩ lazyRandomizerLift
(wotsSignFromHistO hist ⟨pk,root⟩)) (A.main ⟨pk, root⟩)) []` (`rfl`): the forger enters only via `main`.

## Deviations / notes
* The bound proved is the memoised one (129714), better than the literal 182144; `wotsAnswer` itself is
  unchanged, the equality `wotsAnswerOpen_tbl` is to the literal `wotsAnswer`.
* Bounds for `rTcr`/`rTcrT` share one program; summary names use `wotsTcrT_…` (`rTcrT_forge` is `rfl`).
* State is explicit, `((tbl, hist, root), hist2)`, as in the existing `*_phase2_eq`. Uniform-bit queries
  (forger coins, `optRand`, fresh randomizers) are kind `.unif`, not counted.
* The `_hashfree` lemmas are not `rfl` at top level (Lean's unifier does not unfold stuck matchers);
  they are proved by case split, component lemmas `lazyRandomizer_hashfree`, `wotsWinO_hashfree`, ….
* Not done: compatibility lemmas with `Reduction/Gen` (optional).

## Axioms
All `#print axioms` (end of file): `[propext, Classical.choice, Quot.sound]`; `wotsAnswerHashes_128s`: `[propext]`.
