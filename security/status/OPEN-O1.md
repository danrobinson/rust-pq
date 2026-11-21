# OPEN-O1 — R1: the PRF distinguishers as open programs (done, no hypothesis left)

Files (new, both compile, oleans written): `Reduction/Open/HSpec.lean`, `Reduction/Open/Prf.lean`.
Namespace `Reduction.Open`. No `sorry`/axiom; every `#print axioms` ⊆ [propext, Classical.choice, Quot.sound].
## Definitions (HSpec.lean; `{p : Params} (prims : Primitives p)`)
```
abbrev HSpec prims := publicHashSpec prims.core + ((prims.SkPrf × prims.Y × List Byte) →ₒ prims.Y)
def HSpec.impl prims : QueryImpl (HSpec prims) Id        -- .inl q ↦ PublicHash.impl prims q; .inr t ↦ prims.PRFmsg t.1 t.2.1 t.2.2
abbrev PSpec prims (D : Type) := unifSpec + ((D →ₒ prims.Y) + HSpec prims)
inductive HKind | unif | game | hash | prfmsg ;  def hkind : ℕ ⊕ (D ⊕ (P ⊕ M)) → HKind ;  def hind K K' := if K = K' then 1 else 0
def closeImpl prims D : QueryImpl (PSpec prims D) (OracleComp (unifSpec + (D →ₒ prims.Y)))
   -- unif forwarded, .inr (.inl d) ↦ PRFScheme.functionQuery d, .inr (.inr q) ↦ pure (HSpec.impl prims q)
def restrictO (r : D → Option D') : QueryImpl (PSpec prims D) (OracleComp (PSpec prims D'))   -- open Restrict.restrictImpl
def hashEmb prims D : QueryImpl (publicHashSpec prims.core) (OracleComp (PSpec prims D))       -- each query = one hash query
```
Also `gameQ`, `prfMsgQ` (single queries), `openQ`/`closedQ` (HasQuery instances), `closeHom` (QueryHom).
Lemmas: `close_liftM`, `close_gameQ`, `close_prfMsgQ`,
`close_hashEmb : simulateQ (closeImpl prims D) (simulateQ (hashEmb prims D) oa) = pure (simulateQ (PublicHash.impl prims) oa)`,
`close_restrictO : simulateQ (closeImpl prims D') (simulateQ (restrictO r) oa) = simulateQ (Restrict.restrictImpl r) (simulateQ (closeImpl prims D) oa)`,
`restrictO_kindBound` (no kind count increases), `hashEmb_kindBound` (`≤ hind K .hash * n`), `liftM_kindBound`.
## Programs (Prf.lean; `prfGameSpec` = `(prims.PkSeed × Adrs) →ₒ prims.Y`, resp. `… × SkAdrs vp` for the C forms)
```
abbrev OpenCheck vp prims := PublicKeyCore prims.core → List Byte × SignatureCore vp prims.core → SigLog vp prims
                              → OracleComp (publicHashSpec prims.core) Bool
noncomputable def bPrfOpen  (A : Forger vp prims optRand pkSeedDist) : OracleComp (PSpec prims (prims.PkSeed × Adrs)) Bool
noncomputable def bPrfWOpen (wO : OpenCheck vp prims) (A) : OracleComp (PSpec prims (prims.PkSeed × Adrs)) Bool
noncomputable def bPrfCOpen  (A)    : OracleComp (PSpec prims (prims.PkSeed × SkAdrs vp)) Bool := simulateQ (restrictO (skRestrict vp prims)) (bPrfOpen A)
noncomputable def bPrfWCOpen (wO) (A) : … := simulateQ (restrictO (skRestrict vp prims)) (bPrfWOpen wO A)
def sufCheckOpen : OpenCheck vp prims   -- verifyInternalM (free program) >>= fun v => pure (!signingLogContains log f.1 f.2 && v)
def eufCheckW : WinCheck vp prims       -- NEW: !log.wasQueried f.1 && verifyInternal …      (no existing EUF WinCheck in the project)
def eufCheckOpen : OpenCheck vp prims
```
Construction: the SAME generic code as `bPrf` (`keygenInternalWithSecretM`, `signInternalWithSecretRandomizerM`,
`runForger`/`runForgerSig`) with the `HasQuery` instance an actual query (`openQ`), secrets = `gameQ (pkSeed, a)`,
`R ←` ONE `prfMsgQ skPrf addrnd m` query per signature, final check = `GeneralScheme.verifyInternalM` (VCVio's free
verification program; `verifyInternal` is its `PublicHash.impl` interpretation by `rfl`) run through `hashEmb`.
## Equations
```
theorem bPrfOpen_close (A) : simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (bPrfOpen A) = bPrf A
theorem bPrfWOpen_close (w : WinCheck vp prims) (wO : OpenCheck vp prims)
    (hw : ∀ pk f log, simulateQ (PublicHash.impl prims) (wO pk f log) = w pk f log) (A) :
    simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (bPrfWOpen wO A) = bPrfW w A
theorem bPrfCOpen_close (A) : simulateQ (closeImpl prims (prims.PkSeed × SkAdrs vp)) (bPrfCOpen A) = bPrfC A
theorem bPrfWCOpen_close (w) (wO) (hw) (A) : simulateQ (closeImpl prims (prims.PkSeed × SkAdrs vp)) (bPrfWCOpen wO A) = bPrfWC w A
theorem sufCheckOpen_eq pk f log : simulateQ (PublicHash.impl prims) (sufCheckOpen pk f log) = sufCheck pk f log
theorem eufCheckOpen_eq pk f log : simulateQ (PublicHash.impl prims) (eufCheckOpen pk f log) = eufCheckW pk f log
instances: bPrfWOpen_close_suf, bPrfWCOpen_close_suf (… sufCheckOpen A) = bPrfW(C) sufCheck A), bPrfWOpen_close_euf
```
## Counts (predicate `fun t => hkind t = K`; `hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs`)
```
def prfB vp K qs c := Lazy.keygenB vp (hind K .game) (hind K .hash)
                      + qs * (hind K .prfmsg + Lazy.signB vp (hind K .game) (hind K .hash)) + hind K .hash * c
theorem bPrfOpen_kindBound (A) (K) (hK : K ≠ .unif) (qs) (hA) :
    IsQueryBoundP (bPrfOpen A) (fun t => hkind t = K) (prfB vp K qs (1 + Resources2.verifyHashes vp))
theorem bPrfWOpen_kindBound (wO) (c) (hc : ∀ pk f log, IsQueryBoundP (wO pk f log) (fun _ => True) c) (A) (K) (hK) (qs) (hA) :
    IsQueryBoundP (bPrfWOpen wO A) (fun t => hkind t = K) (prfB vp K qs c)
theorem verifyInternalM_bound msg sig pk (also sufCheckOpen_bound, eufCheckOpen_bound, same bound) : IsQueryBoundP (verifyInternalM vp prims.core msg sig pk) (fun _ => True) (1 + Resources2.verifyHashes vp)
```
Corollaries, for each of `bPrfOpen`, `bPrfCOpen` (and `bPrfWOpen wO`, `bPrfWCOpen wO` with `c`; `bPrfWCOpen sufCheckOpen`
as `bPrfWCOpen_suf_*` with `c = 1 + verifyHashes`):
* `*_hashes`: `.hash` ≤ `Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp)`
* `*_prfmsg`: `.prfmsg` ≤ `qs`
* `*_game`: `.game` ≤ `2 ^ vp.params.hp * vp.params.len + qs * signReads vp` (the bound of `bPrf_queryBound_exact`)

128s: `bPrfCOpen_hashes_128s`, `bPrfWCOpen_suf_hashes_128s`: `.hash` ≤ `269824 + qs * 2007385 + 3929`
(`.prfmsg ≤ qs`; `.game ≤ 17920 + qs·182784` follows from `*_game` with `Resources.keygenReads_128s`/`signReads_128s`, not restated).
## Deviations from the specification
1. Verification term is `1 + verifyHashes`, not `verifyHashes`: `Resources2.verifyHashes` excludes the `H_msg` of the
   forgery (3928 at 128s); the true count is 3929. Same for SUF: `sufCheck` does one verification, the log test hashes nothing.
2. A general `WinCheck w` cannot be opened (an arbitrary Bool function); `bPrfWOpen` takes an open form `wO : OpenCheck`
   and the equation needs `hw` (named hypothesis of `bPrfWOpen_close`), discharged for `sufCheck` and `eufCheckW`.
   `eufCheckW` is a new definition; `bPrf` itself (the EUF adversary) is covered directly by `bPrfOpen`.
3. Counting predicate is `hkind t = K` on `PSpec` (own `HKind`, since `Lazy.Kind` has no `prfmsg`); bounds are for
   `K ≠ .unif`. PRF-game counts are stated on the open programs; with the `*_close` equations the existing
   `bPrf(C)_queryBound_exact`/`bPrfW(C)_queryBound_exact` remain the statements for the closed adversaries.
4. C forms are the open restriction `restrictO` applied to the open program (not separately written programs).
## Not done
Nothing of R1 is missing. No theorem that the open programs do not depend on `prims.Thash/Hmsg/PRFmsg` (by inspection
only `prims.core`, `optRand`, `pkSeedDist` occur; `prims.PRF` is never evaluated).
Integration: import `Reduction.Open.Prf`; the instances `openQ`/`closedQ` are local, nothing global is added.
