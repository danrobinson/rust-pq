# R-prfmsg — `PRF` and `PRF_msg` realisers (agent `prfmsg`)

State: **done** for SUF and EUF, both families. Every module builds with `lake build <module>`;
`#print axioms` of every headline ⊆ `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`,
`axiom`, `native_decide`, `bv_decide`, `maxHeartbeats`. Not wired into `Ideal.lean`.

## Modules (new, owned by `prfmsg`; dependency order)
- `Ideal/Realize/MsgHarness.lean` — port harness `harnP` + fusion, `portR` (answer port by `g`),
  lazy cache commutes with it, `interpC`, `lazyRun_portR`, `liftP`, `lazyRes_bound_liftP`.
- `Ideal/Realize/MsgPort.lean` — `PRF_msg` port programs `msgOpenWVP`/`msgOpenVP`, fusion,
  `typedC`, `bytesToTypedS_inst`/`bytesToTyped_inst`, `msgOpenWVP_withTH`/`msgOpenVP_withTH` (`rfl`).
- `Ideal/Realize/MsgCount.lean` — `qb_run_classes`, `harnP_bound`, `verifyM_bound`, class counts.
- `Ideal/Realize/MsgReal.lean` — `AmsgS`/`AmsgE`, equations, `realizesMsgSuf`/`realizesMsgEuf`.
- `Ideal/Realize/PrfTr.lean` — **open-level `setPrf` transport** of `bPrfWCOpen sufCheckOpen`,
  `bPrfCOpen` (`bPrfWCOpen_setPrf` `:276`, `bPrfCOpen_setPrf` `:289`) and the missing `withTH`
  statements for the PRF open programs (`bPrfWCOpen_withTH` `:312`, `bPrfCOpen_withTH` `:319`;
  gap (a) of `OPEN.md` §2).
- `Ideal/Realize/PrfPort.lean` — `QSpec`, `embQ`, `portP`, `restrictP`, `bPrfWCOpenP`/`bPrfCOpenP`,
  fusion, `withTH`.
- `Ideal/Realize/PrfCount.lean` — class counts of the PRF port programs.
- `Ideal/Realize/PrfReal.lean` — `AprfS`/`AprfE`, equations, `realizesPrfSuf`/`realizesPrfEuf`,
  closed forms, `le_parts`.
`lake build Ideal.Realize.PrfReal` builds all eight (last run: `Build completed successfully (7264 jobs).`).

## Headline statements (verbatim)
Section variables of both realiser sections (`MsgReal.lean:281`, `PrfReal.lean:293`):
```
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
include hqf hqs hlong hout
```
`PrfReal.lean:303`, `:314`:
```
noncomputable def realizesPrfSuf :
    RealizesPrf (fun g => Reduction.bPrfWC Reduction.sufCheck
      (S.typedS (optRandU oR) pkSeedDist g)) (qPrf qf qs ℓ) (qOPrf qs)
noncomputable def realizesPrfEuf :
    RealizesPrf (fun g => Reduction.bPrfC (S.typedE (optRandU oR) pkSeedDist g))
      (qPrf qf qs ℓ) (qOPrf qs)
```
`MsgReal.lean:295`, `:307`:
```
noncomputable def realizesMsgSuf :
    RealizesMsg (fun g => Reduction.Lazy.bPrfMsgWL Reduction.sufCheck
      (S.typedS (optRandU oR) pkSeedDist g)) (qMsg qf qs ℓ) qs ℓ
noncomputable def realizesMsgEuf :
    RealizesMsg (fun g => Reduction.Lazy.bPrfMsgL (S.typedE (optRandU oR) pkSeedDist g))
      (qMsg qf qs ℓ) qs ℓ
```
All four are built from an EQUALITY of adversaries (`RealizesPrf.ofEq`, own `realizesMsg_ofEq`):
`bPrfWC_eq_inst` (`PrfReal.lean:123`), `bPrfC_eq_inst` (`:150`), `bPrfMsgWL_eq_inst`
(`MsgReal.lean:84`), `bPrfMsgL_eq_inst` (`:110`), e.g.
```
theorem bPrfWC_eq_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    bPrfWC sufCheck (S.typedS (optRandU oR) pkSeedDist g) = (AprfS S oR pkSeedDist).inst g
```
Parameters (definitions, no hand-copied numerals):
```
def qPrf (qf qs ℓ : ℕ) : ℕ :=                                            -- PrfReal.lean:225
  qf * 1 + hashN qs * thashCost thB + (qs + 1) * hmsgCost ℓ + qs * prfMsgCost ℓ
def qOPrf (qs : ℕ) : ℕ := 2 ^ Link.vp.params.hp * Link.vp.params.len + qs * signReads Link.vp
def qMsg (qf qs ℓ : ℕ) : ℕ := qf * 1 + hashN qs * thashCost thB + (qs + 1) * hmsgCost ℓ  -- MsgReal:148
abbrev hashN (qs : ℕ) : ℕ :=                                             -- MsgReal.lean:143
  keygenHashes Link.vp + qs * signHashes Link.vp + (1 + Resources2.verifyHashes Link.vp)
```
(`thB = Link.vp.params.len`; `hashN` is the bound of `Open.msgOpenWV_suf_hashes` /
`bPrfWCOpen_suf_hashes`, re-derived for the port programs from `openKeygen(P)_kindBound`,
`openSign(P)_kindBound`, `keygenB_hash`, `signB_hash`, `sufCheckO_total`/`verifyInternalM_bound`;
`qOPrf` from `keygenB_sec`, `signB_sec`; chain costs from `thashC_bound`, `hmsgC_bound`,
`prfMsgC_bound`.) Closed forms: `qPrf_128s` (`:333`) `= qf + (269824 + qs*2007385 + 3929)*11 +
(qs+1)*((ℓ+56)/64+3) + qs*((ℓ+24)/64+4)`; `qOPrf_128s` `= 17920 + qs*182784`; `qMsg_128s`
(`MsgReal:329`) the same without the last summand.

`Le`-shaped bounds (`PrfReal.lean:382`):
```
def QcPM (qf qs ℓ : ℕ) : ℕ := qf + (qs + 1) * (2 ^ 25 + 2 * ℓ)
def NPM (qs : ℕ) : ℕ := 2 ^ 18 * (qs + 1)
theorem le_parts (qf qs ℓ : ℕ) :
    qPrf qf qs ℓ ≤ QcPM qf qs ℓ ∧ qOPrf qs ≤ NPM qs ∧
      Ideal.Realize.Msg.qMsg qf qs ℓ ≤ QcPM qf qs ℓ ∧ qs ≤ qs ∧ ℓ ≤ 64 * ((ℓ + 63) / 64)
```
i.e. `q ≤ Qc`, `qO ≤ N`, `qm ≤ Qc`, `qOm ≤ qs`, `mlen ≤ 64·ℓ'` with `ℓ' = ⌈ℓ/64⌉` (or any
`ℓ' ≥ ℓ/64`, e.g. `ℓ' = ℓ`). Tighter: `qPrf_le'` `≤ qf + (qs+1)*(22081242 + 2*((ℓ+56)/64))`,
`qMsg_le'` `≤ qf + (qs+1)*(22081238 + (ℓ+56)/64)` (below the TCR cap `QcT` of `R-tcr.md`).

Composability checked (`scratch/ideal/prfmsg/compose_check.lean`): `{ R with q, qO, qm, qOm, mlen,
prf := realizesPrfSuf …, msg := realizesMsgSuf … } : SufRealizers S (optRandU oR) pkSeedDist`, and
the same for `EufRealizers` with the `…Euf` realisers, typecheck.

## Hypotheses
Exactly `hqf hqs hlong hout` in the agreed form. Nothing else (no `Structural`, no extra named
hypothesis). `pkSeedDist` arbitrary.

## Proof route (for reviewers)
SUF PRF: `bPrfWC sufCheck (typedS g)` = close of `bPrfWCOpen` at `primsG (liftC g)`
(`bPrfWCOpen_close_suf`) → open transport to `R₀ (thG g) (hmG g)` (`bPrfWCOpen_setPrf`; changes
`PRF` AND `PRF_msg`, possible only because the open program evaluates neither) → `close_castP'`
(the close handler read over the reference interface, `krfl`) → `bytesToTypedS_inst` (forger
= port forger `typedC …` with port answered by `g`) → port fusion → `withTH` (`krfl`) to
`Rd = R₀ dT dH` → `close_portP` (answering port + compression chains by `g`). Msg: closed
transport `Ideal.Transport.bPrfMsgWL_setPrf_S` → `lazyRun_msgOpenWV_sufCheck` → fusion →
`withTH` (`rfl`) → `lazyRun_portR`. The PRF game oracle of `RealizesPrf` is the game's (replaces
the scheme's `PRF`), the `PRF_msg` game oracle of `RealizesMsg` the game's (replaces `PRF_msg`);
the PRF distinguisher's `PRF_msg` evaluations are HMAC compression chains (`prfMsgC`).
Lesson: never let the elaborator compare `R₀ (thG g) _` with `R₀ dT dH` (timeouts); state
generic lemmas at variable `prims`/`T`/`H` and instantiate.

## Not done / not verified
- Not imported by `Ideal.lean`; the composed theorems are not restated with these realisers.
- Unaudited; I read only my own proofs. Hash count of the PRF program counts each `Thash` at
  the cost of a `len`-value call (11 compressions), as `R-tcr.md` does.
