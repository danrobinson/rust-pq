# HANDOFF — agent `qmach` (machine side of the class-TCR bridge)

Status: DONE for items 1–5 (quantum/HANDOFF.md §4 steps 2a, 2b, 2c, 3 for class TCR, all arities
`n`, one proof). All results print `[propext, Classical.choice, Quot.sound]` (or fewer).
No `sorry`/`axiom`/`native_decide`. Nothing committed.

## New modules (coordinator: add to the build)
* `quantum/PQ/Interactive/QromBridgeEvalProg.lean` — lake module `PQ.Interactive.QromBridgeEvalProg`
  (add `import PQ.Interactive.QromBridgeEvalProg` to `PQ.lean`). Built with
  `lake build PQ.Interactive.QromBridgeEvalProg`.
* `quantum/Integration/SlhDsaBridgeMach.lean` — Integration file (imports
  `Integration.SlhDsaBridgePrf`, `Reduction.Open.Tcr`, `Reduction.Open.Phase1Tcr`,
  `Reduction.Instance128sV2`, `PQ.Interactive.QromBridgeEvalProg`). Compiles in ≈ 37 s; olean
  written to `.lake/build/integration/Integration/SlhDsaBridgeMach.olean`.
* `quantum/PQ/Interactive/QromBridgeEval.lean`: header comment only (points to the new file).
  No `security/` file was created or changed.

## Headlines

`PQ/Interactive/QromBridgeEvalProg.lean`
* `:28` `PUE.exists_prog` — exactly the statement of HANDOFF §4/2a.
* `:117` `PUE.exists_prog_qprob` — as `PU.exists_prog_qprob`.
* `:139` `PUE.exists_model` — exactly HANDOFF §4/2c:
  `(h : PUE (spec := unifSpec) cnt0 Mach q) (ρ : SubState ((X × Y) × E)) : ∃ Mo : PQ.QROM.HybridModel X Y α q, ∀ H Ev [DecidablePred Ev], Mo.prob H Ev = qWeight Ev (Mach H) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)`
* `:156` `PUE.compileQ (cnt) (P) (n) (hP : WCount (compileW cnt) P n) : PUE cnt (fun H ↦ compileQ H P) n`
  (`compileW cnt = Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 1) cnt)`, i.e. the §4/2b weight).
* `:187` `wCount_of_countBound isP isS w c (hw : ∀ t, w t ≤ (if isP t then 1 else 0) + (if isS t then c else 0)) P q qs (hq : CountBound isP P q) (hs : CountBound isS P qs) : WCount w P (q + qs * c)`.
* `:247` `wCount_of_isQueryBoundP` (security-side `IsQueryBoundP` → `WCount` with indicator
  weights), `WCount.map`, `wCount_liftM_query`.

`Integration/SlhDsaBridgeMach.lean` (section variables `c optRand₀ pkSeedDist₀ F` as in
`SlhDsaBridgePrf.lean`)
* `:285` `tcrMach_encΩ`: `tcrMach c optRand₀ F ω₀ n st pk (encΩ { ω₀ with thash := T }) = (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk`
* `:459` `pue_tcrMach … (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) : PUE (spec := unifSpec) cnt0 (tcrMach c optRand₀ F ω₀ n st pk) (q + tcrMHashes Link.vp qs)`
* `:500` `tcr_mach_exists` (step 3 as asked): `∃ Mach, PUE cnt0 Mach (q + tcrMHashes Link.vp qs) ∧ ∀ T, Mach (encΩ { ω₀ with thash := T }) = (qbTcrArM n (internalΩ … { ω₀ with thash := T })).forge st pk`
* `:515` `tcr_forge_model` (step 5, state `ρ ⊗ |()⟩⟨()|`), `:535` `tcr_forge_model_ρ₀` (state = the adversary's `ρ₀`).
* `:557` **`tcr_hModel`** — the hypothesis `hModel` of `quantum/HANDOFF-qtcr.md`, verbatim, with
  `q' := q + tcrMHashes Link.vp qs`:
  ```lean
  theorem tcr_hModel (n q qs : ℕ)
      (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
      ∀ (ω₀ : Ω128 c) (st : Open.TcrP1State Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
        ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY
            (ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n}) (q + tcrMHashes Link.vp qs),
          ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
              Bytes Link.vp.params.n)
            (Ev : ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n} → Prop)
            [DecidablePred Ev],
            Mo.prob (encΩ { ω₀ with thash := T }) Ev =
              qWeight Ev ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
                { ω₀ with thash := T })).forge st pk) F.ρ₀
  ```
* `tcrMHashes vp qs := Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2)`;
  `tcrMHashes_128s : … = 269824 + qs * 2007385 + 7857`; `tcrMHashes_openCounts128s`: equal to the
  `tcr1/tcr2/tcrLen/tcrK` fields of `openCounts128s qs`.

## How it is built (design notes)
* No change to `PUE`/`EvalCost` was needed; the design worked as is on the real machine.
* GAP of §4/3 (per-query open forms) closed without new `security/` files: the per-query lemmas
  already exist (`Lazy.openKeygen_tbl`, `Lazy.openSign_tbl`, `Resources2.collO_tbl`,
  `verifyCalls_eq_free`). The machine is re-written (`qmMach`, generic in `prims`) with open
  programs over `Lazy.OSpec prims []ₒ` interpreted by `qmImpl ans tbl : QueryImpl _ ProbComp`;
  `qmImpl_bridge` relates it to `Lazy.tblImpl`; `qMemoForge_eq_qmMach` (Part A).
* Each hash query = ONE port evaluation: `hashH c ω₀ H` (in cap: `(H (.inl …)).1` /
  `(H (.inr (.inl …))).2`; out of cap: `default`, as `FinFns.toRand`), `evalCost_hashH`;
  `impl_primsΩ_withThash : PublicHash.impl (primsΩ {ω₀ with thash := T}) = hashH c ω₀ (encΩ …)`.
  Counts via `wCount_of_isQueryBoundP` from `openKeygen_kindBound`/`openSign_kindBound`/
  `verifyFree_bound`+`collO_step_bound`.
* Cross-world equality (`{ω₀ with thash := T}` vs `ω₀`): the wrappers' `Coded.View` carries the
  (T-dependent) schemes as implicit arguments; `qmCSign_eq`/`qmCRead_eq` remove them, then the
  elaborator (forger) resp. the kernel (`qm_kernel_rfl`, whole machine) checks the rest in
  seconds. A kernel `rfl` before that rewrite timed out using > 60 GB (do not try it).
* Signing queries are weighted `Lazy.signHashes` each (`sgnW`), through `compileQ`, the two
  `wrap0` wrappers (`pue_qmForger`) and `PUE.close` (`evalCost_qmImplS`).

## Not done / next
* Only class TCR (`tcr1/tcr2/tcrLen/tcrK`). The same recipe (generic open-form rewrite +
  `hashH` + kernel rfl) should apply to `tcrT`/`ud`/`pre` (WOTS open programs) and FORS terms.
* The game side (resampling, `spr_embedded_obs_weighted_le`, discharge of `BridgesRest` fields)
  is agent `qtcr`'s.

---

# Round 2 (remaining bridge terms)

FORS (`qToTcr`/`qToDspr`): reassigned to `qtcr`; qmach started NO FORS file.

## WOTS — DONE: `quantum/Integration/SlhDsaBridgeMachWots.lean`
(imports `Integration.SlhDsaBridgeMach`, `Reduction.Open.Wots`, `Reduction.Open.Phase1Wots`;
compiles in a few seconds; olean in `.lake/build/integration/Integration/`).
Shared machinery: `qmSignG` (signing oracle with any OPEN signer) + `qmSignG_ideal`;
`qmWotsMach` (generic in `prims` and in the open post-processing) + `qWotsForge_post_eq`
(Part A, from `wotsSignFromHistO_tbl`, `wotsAnswerOpen_tbl`); `wotsMach … ω₀ st pk post H`;
`pue_wotsMach` (budget `q + (qs·wotsSignHistHashes + (wotsAnswerHashes + cp))`).
`WotsSt c ω₀` is `Open.RState Link.vp (primsΩ ω₀)` (same term).

Per machine (all `[propext, Classical.choice, Quot.sound]`; counts `[propext]`):
| machine | field | primitive form (∃ Mach, PUE ∧ ∀ T, eq) | model form (`F.ρ₀`) | count lemma |
|---|---|---|---|---|
| `qrTcrT` `.forge` | `tcrT` | `wotsTcrT_mach_exists` `:222` | `wotsTcrT_hModel` `:241`; `tcrT_hModel` `:413` (verbatim `hModel` of `tcrT_term`, `SlhDsaBridgeTcrT.lean:191`) | `qmWotsTcrTHashes_openCounts128s` `:197` |
| `qrUd` `.distinguish` (out `Bool`) | `ud` | `wotsUd_mach_exists` `:289` | `wotsUd_hModel` `:306` | `qmWotsUdHashes_openCounts128s` `:264` |
| `qrPre` `.invert` (out `ℕ × Bytes n`) | `pre` | `wotsPre_mach_exists` `:353` | `wotsPre_hModel` `:370` | `qmWotsPreHashes_openCounts128s` `:328` |

Model form, e.g. `wotsUd_hModel (q qs) hq hqs : ∀ ω₀ (st : WotsSt c ω₀) (pk : Bytes n), ∃ Mo : HybridModel (EncX c) EncY Bool (q + qmWotsUdHashes Link.vp qs), ∀ T Ev [Dec], Mo.prob (encΩ {ω₀ with thash := T}) Ev = qWeight Ev ((qrUd (internalΩ … {ω₀ with thash := T})).distinguish st pk) F.ρ₀`.
Checked by compiling: `tcrT_term … (tcrT_hModel …)` closes
`avΩ c (qSM_DT_TCR_Advantage ∘ qrTcrT ∘ internalΩ …) ≤ epsTcr0 (q + (openCounts128s qs).tcrT)`
(scratch `quantum/scratch/qmach/P1.lean`).
`qwots`: no `HANDOFF-qwots.md` existed when this landed; if your hypothesis differs, say so.

## New PQ module: `PQ/Interactive/QromBridgeEvalQ.lean` (lake module `PQ.Interactive.QromBridgeEvalQ`; add to `PQ.lean`)
`EvalCostQ E cnt f n` (the analogue of `EvalCost` in front of NON-closed `PUE cnt` families),
`.const/.eval/.bind/.mono`; `PUE.wrap0E` (stateless wrapper whose code depends on the port
function); `wCount_zero`, `WCount.bind`. Built: `lake build PQ.Interactive.QromBridgeEvalQ` OK.

## ITSR — machine side DONE in primitive form: `quantum/Integration/SlhDsaBridgeMachItsr.lean`
(imports `Integration.SlhDsaBridgeMach`, `PQ.Interactive.QromBridgeEvalQ`.)
* `qbItsrL_eq` `:57` (`rfl`): `qbItsrL Q = qLazyRun (PublicHash.impl prims) (qmItsrOpen optRand pkSeedDist Q.main)`.
* `itsrMach c optRand₀ pkSeedDist₀ F ω₀ H : QOC (WS (EncX c) EncY E) (unifSpec + Lazy.itsrG (primsΩ ω₀)) _` `:121`
  — NOT closed: it still talks to the ITSR target oracle.
* `itsrMach_encΩ` `:129`: `itsrMach … ω₀ (encΩ { ω₀ with hmsg := Hm }) = qbItsrL (internalΩ … { ω₀ with hmsg := Hm })`
  (`FinFns.withHmsg ω g` of `qprf` is the same term).
* `pue_itsrMach` `:225`: `PUE (fun _ ↦ 0) (itsrMach …) (q + itsrHashes Link.vp qs)` (target queries
  weigh 0: they are the game's); `itsr_mach_exists` `:251` (primitive ∃ form);
  `itsrHashes_openCounts128s` `:151`: `itsrHashes Link.vp qs = (openCounts128s qs).itsr`.
* NOT done: `qprf`'s Part-C `hModel` (an `IAdv` over `qromSpec (BN × ItsrXm c) BM`, the `H_msg`
  component alone). From the `PUE` family above it still needs (1) a `PUE → IAdv` compiler for
  open families (as `PUE.exists_prog`, with target queries as `IAdv` requests), and (2) simulating
  the four-component port `U_{encΩ ω}` by ONE call of `U_Hf` (non-`hmsg` inputs must not reach the
  oracle: ancilla/routing argument). Neither exists. `qprf` now owns the ITSR term; no "Part D"
  section was present in `HANDOFF-qprf.md` when this was written.

## UD / PRE consumer
No `quantum/HANDOFF-qwots.md` existed when the WOTS file landed; `wotsUd_hModel`/`wotsPre_hModel`
are in the `tcr_hModel` shape (state `WotsSt c ω₀ = Open.RState …`, matrix `F.ρ₀`); the primitive
forms `wotsUd_mach_exists`/`wotsPre_mach_exists` let any other shape be derived.

---

# Round 3 — ITSR IAdv over the port oracle

## Statement to be delivered (b) — written before the proof
File `quantum/Integration/SlhDsaBridgeMachItsr2.lean`; section variables as in
`SlhDsaBridgePrf.lean` (`c optRand₀ pkSeedDist₀ F`); `detImpl ch` = uniform bits forwarded,
game query `r` answered by the deterministic challenger `ch r : St → Resp × St`
(`detImpl ch = (QueryImpl.ofLift unifSpec ProbComp).liftTarget _ + fun r ↦ StateT.mk fun s ↦ pure (ch r s)`):
```lean
theorem itsr_iadv (ω₀ : Ω128 c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ x : IAdv LocalSig.instruments.{0} (qromSpec (EncX c) EncY) (ItsrIn (primsΩ ω₀))
        (primsΩ ω₀).Y (fun _ ↦ (primsΩ ω₀).Y × ItsrIn (primsΩ ω₀)) qs (progReg (EncX c) EncY E),
      IAdv.IsQueryBound qs x (fun _ ↦ q + itsrHashes Link.vp qs) ∧
      ∀ (St : Type) (ch : ItsrIn (primsΩ ω₀) → St → (primsΩ ω₀).Y × St) (s : St) (T)
        (ρ : SubState ((EncX c × EncY) × E))
        (Ev : ((primsΩ ω₀).Y × ItsrIn (primsΩ ω₀)) × St → Prop) [DecidablePred Ev],
        qprob LocalSig.Interp.instruments (encΩ { ω₀ with hmsg := T })
            (IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
              (spec := qromSpec (EncX c) EncY)) qs s x) ρ (fun p ↦ Ev p.2) =
          qWeight Ev (close (detImpl ch)
            (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with hmsg := T }))) s)
            (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
```
i.e. ONE interactive adversary over the PORT oracle, `≤ q + itsrHashes qs` port calls (=
`q + (openCounts128s qs).itsr`), `≤ qs` requests (the ITSR targets), whose run against any
deterministic challenger (e.g. `rndCh Rs` from `[]`) is the Part-1 machine `qbItsrL` closed with
that challenger, at the port function of every world `{ω₀ with hmsg := T}`. Going from the
Part-1 game's sampling challenger `ITSROracles` to `rndCh Rs` (presampling) is `qprf`'s.
Generic compiler (a): `PUE.exists_iadv` in `quantum/PQ/Interactive/QromBridgeEvalIAdv.lean`.

## Round 3 — DELIVERED
Change to the statement written above: the request/answer types are now the concrete
`QItsr.ItsrInB` (`= BN × BN × List Byte`) and `BN`, because `ItsrIn (primsΩ ω₀)` / `(primsΩ ω₀).Y`
caused `whnf` timeouts. `Integration/SlhDsaBridgeMachItsr2.lean` now imports `qprf`'s
`Integration.SlhDsaBridgeItsrD` and uses its `ItsrInB` and `rndImpl`.
* (a) `PQ/Interactive/QromBridgeEvalIAdv.lean`, a lake module (add it to `PQ.lean`):
  - `PUE.exists_iadv` `:129` / `PUE.exists_iadv_qprob` `:271` (needs `[Nonempty α]`): a family with
    `PUE (fun _ ↦ 0) Mach q` over `unifSpec + (Req →ₒ Resp)` gives, for every `n`, ONE
    `x : IAdv LocalSig.instruments (qromSpec X Y) Req Resp (fun _ ↦ α) n (progReg X Y E)` with
    `IAdv.IsQueryBound n x (fun _ ↦ q)`.
  - Semantics: for every `St`, deterministic `ch`, `s`, `Ev`, `H` with
    `CountBound isGameQ (Mach H) n`:
    `qprob I H (IAdv.flat ch IAdv.stop n s x) ρ (Ev ∘ snd) = qWeight Ev (close (detImpl ch) (Mach H) s) (ρ ⊗ |()⟩⟨()|)`.
  - Count transfer: `WCount.simulateQ(_run)`, `.liftQ`, `.wrap0`, `.wrap`, `.compileQ`, `.wmono`,
    `countBound_iff_wCount`.
* (b) `Integration/SlhDsaBridgeMachItsr2.lean`:
  - `itsrMach_games` `:150`: at most `qs` target queries.
  - `itsr_iadv` `:178`: the form announced above, with the concrete types.
  - `itsr_hPort` `:211`: `qprf`'s `hPort`, verbatim, with `q' = q + itsrHashes Link.vp qs` and
    hypotheses `hq`, `hqs` only. The `Option` output comes from `some <$> itsrMach` (`PUE.map`);
    `rndImpl Rs` is `detImpl (rndCh Rs)` by `rfl`.
  - `itsr_closed` `:247`:
    `avΩ c (qItsrAdvantage … (qbItsrL (internalΩ … ω)) …) ≤ epsItsr Link.vp.params (q + (openCounts128s qs).itsr) qs`,
    from `hq hqs hcap`.
* All results print `[propext, Classical.choice, Quot.sound]` (count lemmas: `[propext, Quot.sound]`).
