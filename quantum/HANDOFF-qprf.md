# HANDOFF (agent `qprf`): `hInd` and the `PRF_msg` bridge — both PROVED

Nothing committed. Four new Integration files (not lake modules; compile as in
`scripts/check-integration.sh` step 3, in this order):

| file | content |
|---|---|
| `Integration/SlhDsaBridgeInd.lean` | `hInd` proved (`QInd.prfMachSuf_withPrf` `:330`, `QInd.prfMachEuf_withPrf` `:338`) |
| `Integration/SlhDsaComposedEnc2.lean` | headlines `…_qrom_enc2` = `…_qrom_enc` without `hInd` |
| `Integration/SlhDsaBridgeMsg.lean` | `PRF_msg` term proved (`QMsg.msg_term_suf` `:777`, `QMsg.msg_term_euf` `:827`) |
| `Integration/SlhDsaComposedEnc2Msg.lean` | headlines `…_qrom_enc2msg`: `hInd` and `BridgesRest.msg` removed |

No existing file was edited. Imports: the new files import `Ideal.Transport.AdvPrf`,
`Ideal.Transport.AdvMsg` (compiled security oleans).

## Headlines

`Integration/SlhDsaComposedEnc2Msg.lean:78` (SUF; EUF at `:111` identical except
`qUnforgeableAdvantage`):

```lean
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc2msg
    (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (_htl : 35 ≤ c.tl)
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesRest10 c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F) q qs r) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r.noPrfMsg
```

* `BridgesRest10` (`SlhDsaComposedEnc2Msg.lean:35`): `BridgesRest` minus its `msg` field, the ten
  other fields copied verbatim (`itsr, dspr, tcrFv, tcr1, tcr2, tcrLen, tcrK, ud, pre, tcrT`).
  UNPROVED.
* `RedCounts.noPrfMsg r = {r with prf := 0, msg := 0}` (`:68`): both PRF terms are charged `q`
  only (the reduction never evaluates `PRF` / `PRF_msg`). This is a strengthening of the old
  bound (old: `r.noPrf`, msg term `epsPrf (q + r.msg)`).
* `hq, hqs, hcap, _htl`: assumptions on the forger / caps, as before. `hcap` is now USED (by the
  `PRF_msg` term).

`Integration/SlhDsaComposedEnc2.lean:28` / `:63`: `…_qrom_enc2`, verbatim `…_qrom_enc` without
`hInd` (still with all eleven `BridgesRest` fields, bound `r.noPrf`).

## How (short)

* `hInd` is true literally. `primsΩ (ω.withPrf g)` is definitionally
  `setPrf (primsΩ ω) (fun pk sk a ↦ g pk sk (sha2AdrsKey a)) (primsΩ ω).PRFmsg`, `codecR` is
  `trCodec`, the byte forger `F.at H _` has the same program. Generic quantum transport
  (`wrap0_wrap0`, `wrap_wrap0`, `wrap_map_state`, `wrap_qPureBytesToInternal_tr`, then
  `qRunForgerSig_tr`, `qRunForger_tr`) + classical `bSignW_tr`/`bSignC_tr`,
  `sufCheck_setPrf`/`harnessValid_setPrf` give `qbPrfW(C)_setPrf`, `qbPrf(C)_setPrf`.
* `PRF_msg`: independence via `castQ` (kernel identity of the open interfaces, `krfl`) +
  `qMsgOpenW_setPrf`/`qMsgOpen_setPrf`. The PRF game is on `BN × List Byte` (infinite), so the
  machine is put behind `Restrict.restrictImpl (rcap c)` into `BN × BList Byte c.ml`: real game
  equal always (`msgPrf_real_restrict`), ideal game equal when all function queries are in the
  cap (`qPrfIdealPr_restrict`); the cap invariant is proved from `hcap` through every layer
  (`allQ_msgMachSuf/Euf`). Then resampling `avΩ_resample_prfMsg` and
  `prf_PU_real_le_ideal_add` with key `id`, exactly as `prf_term_of_indep`.

## Build (last run)

Each file compiled with `LEAN_PATH="$LP" lean -o "$OUT/Integration/NAME.olean" Integration/NAME.lean`:
no errors, no warnings; `#print axioms` lines all `[propext, Classical.choice, Quot.sound]`
(13 in BridgeInd, 2 in ComposedEnc2, 14 in BridgeMsg, 2 in ComposedEnc2Msg). The full
`scripts/check-integration.sh` was NOT run (coordinator's job).

## Not done / next

* The ten `BridgesRest10` fields (TCR family, DSPR, TCR-FV, UD, PRE, WOTS-TCR, ITSR): untouched
  (other agents `qmach`/`qtcr`). Restate the headline again when they land: pass their term
  inequalities straight to `composed_of_linear_eps` as done here for `hmsg`.
* `_htl` still unused.
* Not independently audited.

---

# Part C — ITSR term (game side): DONE modulo `hModel`

## Part C — hypothesis consumed

File `quantum/Integration/SlhDsaBridgeItsr.lean`, namespace `Reduction.QItsr`. Section variables
as in `SlhDsaBridgePrf.lean` (`c`, `optRand₀`, `pkSeedDist₀`, `F : PortForger (EncX c) EncY E`).
Definitions (all in that file):

```lean
abbrev BM : Type := Bytes Link.vp.params.m
abbrev ItsrXm (c : Caps) : Type := BN × BN × BList Byte c.ml          -- (PK.seed, PK.root, M)
def hmsgTable (c : Caps) (Hf : BN × ItsrXm c → BM) : BN → BN → BN → BList Byte c.ml → BM :=
  fun r pk root ms ↦ Hf (r, (pk, root, ms))
def FinFns.withHmsg (ω : FinFns p c) (g : …) : FinFns p c := { ω with hmsg := g }
def idxOf (d : BM) : List (Adrs × ℕ) := forsIndices Link.vp (splitDigest Link.vp.params d)
def idxCov (S : Finset BM) (u : BM) : Prop := ∀ i ∈ idxOf u, ∃ d ∈ S, i ∈ idxOf d
```

The hypothesis (one, named `hModel`, `q' = q + r.itsr`):

```lean
(hModel : ∀ ω₀ : Ω128 c, ∃ (L : LocalSig.{1, 0}) (A : QReg) (I : L.Interp) (ρ : SubState A)
    (x : IAdv L (qromSpec (BN × ItsrXm c) BM) (ItsrXm c) BN (fun _ ↦ BN × ItsrXm c) qs A),
    IAdv.IsQueryBound qs x (fun _ ↦ q') ∧
    ∀ Hf : BN × ItsrXm c → BM,
      qItsrAdvantage (itsrProblem Link.vp (primsΩ (ω₀.withHmsg (hmsgTable c Hf))))
          (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F (ω₀.withHmsg (hmsgTable c Hf))))
          F.ρ₀ ≤
        avg fun Rs : Fin qs → BN ↦
          qprob I Hf (IAdv.flat (rndCh Rs) (IAdv.stop (L := L)
            (spec := qromSpec (BN × ItsrXm c) BM)) qs [] x) ρ (itsrAWin idxCov Rs Hf))
```

In words: for each world `ω₀` (only its `H_msg` component is varied) ONE Part-2 interactive
adversary `x` of `PQ/QROM/MultiPhaseGame.lean` / `ExactItsr4.lean` — quantum access to the
in-cap `H_msg` table `Hf` (digest values `Bytes m`, bytewise group), target requests in
`ItsrXm c`, responses the randomizers, at most `qs` requests, at most `q'` oracle calls — whose
winning probability against the presampled randomizer challenger `rndCh Rs`, averaged over `Rs`,
with the Part-1 win relation `idxCov` (= `itsrProblem`'s index cover, on digests), dominates the
Part-1 ITSR advantage at world `ω₀.withHmsg (hmsgTable c Hf)`, for every `Hf`.

Why this shape (machine side, for `qmach`):
* the Part-2 ITSR theorem (`itsr4_adaptive_le`) exists only for `IAdv` over the bare oracle
  `qromSpec (K × Xm) D` with a request/response interface; there is NO `HybridModel`-level or
  pullback form of it. So the machine side must produce `x` over the `H_msg` component directly:
  each port call `U_{encΩ ω}` is simulated with ONE call to `U_Hf` (the other three components of
  `ω₀` are fixed and computed classically; non-`hmsg` inputs need the output register routed
  past the oracle, e.g. a uniform-superposition ancilla, which is invariant under addition);
  the reduction's own `H_msg` evaluations (signing, final check) become oracle calls (counted in
  `q'`); uniform-sampling nodes compiled as in `PUE.exists_prog`; target requests become IAdv
  requests (`toIAdv`-style, `PQ/Interactive/QromBridgeReq.lean`).
* expected to hold under `hq`, `hqs` (≤ `qs` target requests, so `rndCh Rs` presampling is
  exact), `hcap` (every target request and the candidate are within the cap, so the Part-1
  digests are `Hf` values and Part-1 `Wins` is `itsrAWin idxCov` read through `BList.ofList`).
  An inequality (not equality) is asked so that out-of-cap / over-budget paths may be dropped.
* `D = Bytes m` (NOT `Ix × (Fin k → Lx)`): the port adds digests bytewise, which is not a group
  isomorphism onto any `Ix × (Fin k → Lx)` structure. The FORS digest structure is handled on
  the game side (coverProb pushforward through `coveringDigest`).

Game side (this agent): `H_msg` resampling over `Ω128 c`, average swap to `itsrAdaptiveExp`,
`itsr4_adaptive_le` with `Cov := idxCov`, `coverProb (Fin qs) idxCov ≤ coverProb_fors` closed
form via VCVio's `card_fiber_coveringDigest` (uniform pushforward through `splitDigest`), card
`2^128`, `= epsItsr Link.vp.params q' qs`.

## Part C — result

`quantum/Integration/SlhDsaBridgeItsr.lean:291` (compiled, no warnings, standard axioms):

```lean
theorem itsr_term (q' qs : ℕ)
    (hModel : <exactly the hypothesis above>) :
    avΩ c (fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω))
      (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) ≤ epsItsr Link.vp.params q' qs
```

It is the `hitsr` argument of `composed_of_linear_eps` with `q' := q + r.itsr` (same machine for
SUF and EUF). Proved pieces: `coverProb_le_of_fiber` (generic pushforward), `coverProb_idxCov_le`
(`:215`, uniform `Bytes m` → covering digest via VCVio `card_fiber_coveringDigest`),
`avΩ_resample_hmsg` (`:243`), `itsr_bound_le` (`coverProb_fors`, `|K| = 2^128` → `epsItsr`).
The reprogramming loss `2q'√(qs/2^128)` is kept (general regime `itsr4_adaptive_le`).

What `hModel` bundles (all UNPROVED, machine side): (1) simulation of the four-component port by
the `H_msg`-component oracle, one oracle call per port call, plus the reduction's own `H_msg`
evaluations as oracle calls; (2) compilation of uniform-sampling nodes and target requests into
an `IAdv`; (3) presampling of the ITSR randomizers (`rndCh Rs`, needs ≤ `qs` requests: `hqs`);
(4) the cap (`hcap`: requests and candidate within `c.ml`, so Part-1 digests are `Hf` values and
`Wins` = `itsrAWin idxCov`). (3) and (4) are game-side in nature and could be peeled off with a
deterministic-challenger form of the hypothesis (next step, not done).

---

# Part D — `hModel` discharged on the game side; ONE machine hypothesis `hPort` left

## Part D — what qmach should deliver

EXACTLY the hypothesis `hPort` of `Reduction.QItsr.itsr_term_port`
(`quantum/Integration/SlhDsaBridgeItsrD.lean:834`, compiled), with `q' = q + itsrHashes Link.vp qs`
(`itsrHashes_openCounts128s`: `= (openCounts128s qs).itsr`). Definitions it uses:
`ItsrInB := BN × BN × List Byte` (`:830`), `rndImpl` (`:52`):

```lean
noncomputable def rndImpl (Rs : Fin s → K) :
    QueryImpl (unifSpec + ITSRTargetSpec X K) (StateT (List X) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List X) ProbComp) +
    fun x ↦ (StateT.mk fun t ↦ pure (rndAt Rs t.length, t ++ [x]) : StateT (List X) ProbComp _)
```

```lean
(hPort : ∀ ω₀ : Ω128 c, ∃ (L : LocalSig.{1, 0}) (A : QReg) (I : L.Interp) (ρ : SubState A)
  (x : IAdv L (qromSpec (EncX c) EncY) ItsrInB BN (fun _ ↦ Option (BN × ItsrInB)) qs A),
  IAdv.IsQueryBound qs x (fun _ ↦ q') ∧
  ∀ (Hm : BN → BN → BN → BList Byte c.ml → BM) (Rs : Fin qs → BN)
    (Ev : Option (BN × ItsrInB) × List ItsrInB → Prop) [DecidablePred Ev],
    qprob I (encΩ (ω₀.withHmsg Hm))
        (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (EncX c) EncY)) qs [] x)
        ρ (fun p ↦ Ev p.2) =
      qWeight (fun z ↦ Ev (some z.1, z.2))
        (close (rndImpl (X := ItsrInB) Rs) (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω₀.withHmsg Hm))) []) F.ρ₀)
```

Notes for qmach:
* `ω₀.withHmsg Hm` is `{ ω₀ with hmsg := Hm }` (definitional); `BN = Bytes n`, `BM = Bytes m`;
  `ItsrIn (primsΩ ω)`, `(primsΩ ω).Y` are definitionally `ItsrInB`, `BN` (stating with the
  concrete types avoids a `whnf` timeout).
* one `x` for all `Hm` and `Rs`; `none` output = over-budget convention (never on the right:
  needs `hqs`); `rndImpl Rs` answers the `i`-th target query with `rndAt Rs i`, state = request
  list (exactly the challenger `rndCh Rs` on the left).
* your `itsrMach` (`SlhDsaBridgeMachItsr.lean:121`, `= qbItsrL …` at `encΩ` by `itsrMach_encΩ`)
  closed with `rndImpl Rs` is the right-hand side; the remaining work is the compiler from the
  non-closed `PUE` family into an `IAdv` over the port (your Round 3 (a)/(b)).

## Part D — result

`itsr_term_port (q' qs) (hPort) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
(hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
avΩ c (fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (internalΩ c optRand₀
pkSeedDist₀ encΩ F ω)) (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) ≤ epsItsr Link.vp.params q' qs`
— the `hitsr` argument of `composed_of_linear_eps`. Standard axioms. Proved here:

* item 4 (presampling, `presample` `:166`) and item 5 (cap + count support, `supp_qbItsrL` `:809`,
  `close_rndImpl_supp`, `win_conv`): Part-1 `Wins` ⇒ `itsrAWin idxCov` on the in-cap reading.
* item 1 (oracle mismatch), route (a): `PQ/QROM/ItsrPullback.lean` (lake module
  `PQ.QROM.ItsrPullback`, built), `PQ.QROM.Pull.itsrP_adaptive_le` (`:455`): the bound of
  `itsr4_adaptive_le` verbatim for an `IAdv` over ANY port oracle `φ H : X → Y` that embeds `H`
  locally along an injective `ι` (`φ H z ≠ φ G z → ∃ w, ι w = z ∧ H w ≠ G w`), with requests read
  through `tg` and outputs through `oc`. Proof = `ExactItsr4`'s, every generic step
  (`nRuntime_sqrt_le`, `massN`, `pflat_branch_congr`, `pflat_queryWeight_congr`, `Hidden`) being
  stated for arbitrary port functions; only the row reading (`rowOf`) and the masses at embedded
  points changed. No ancilla simulation (routes (b), (c) not needed).
* `hq` is not needed (the port count is the query bound in `hPort`).

Not done: `hPort` itself (machine side, qmach Round 3). Coordinator: add
`import PQ.QROM.ItsrPullback` to `PQ.lean` (or keep it as an extra built module).
