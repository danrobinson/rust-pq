# R-wots — the three WOTS-chain realisers (SM-UD, SM-PRE, SM-TCR on `F`), SUF and EUF

Agent `wots`. All files in `security/Ideal/Realize/`, namespace `Ideal.Realize.Wots`. Each builds
with `lake build Ideal.Realize.<File>`; no `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`.

## Modules (dependency order; add the last one — it imports the rest — to `Ideal.lean`)
`WotsPort` → `WotsReal` → `WotsUniv` → `WotsCount1` → `WotsLen` → `WotsRealize` → `WotsRealizers`.

## Headline results (`Ideal/Realize/WotsRealizers.lean`)
Common hypotheses (exactly the requested four; nothing else):
```
(hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
(hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
(hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
(hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
```
for every `S : ForgerI`, `oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)`, `pkSeedDist`.

- `:177` `noncomputable def realizesUd : RealizesUd pkSeedDist (fun g => Reduction.rUd pkSeedDist (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pU qf qs ℓ)`
- `:187` `realizesUdE` — same with `S.typedE`.
- `:274` `noncomputable def realizesPre : RealizesPre pkSeedDist (fun g => Reduction.rPre pkSeedDist (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pP qf qs ℓ)`
- `:285` `realizesPreE` — same with `S.typedE`.
- `:336` `noncomputable def realizesWotsTcr : RealizesWotsTcr pkSeedDist (fun g => Reduction.rTcrT pkSeedDist (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pW qf qs ℓ)`
- `:347` `realizesWotsTcrE` — same with `S.typedE`.

Parameters (`P5 = ⟨q₁, qch, qc, L, q₂⟩`):
- `:159` `pU qf qs ℓ = ⟨0, 323449759100660631040, 1062560399506556770327551, Lw, q2 qf qs ℓ (udH qs)⟩`
- `:256` `pP qf qs ℓ = ⟨0, 323449759100660631040, 1062560399506556770327551, Lw, q2 qf qs ℓ (preH qs)⟩`
- `:318` `pW qf qs ℓ = ⟨0, 4851746386509909465600, 1058032102879147521492991, Lw, q2 qf qs ℓ (tcrH qs)⟩`

where (`WotsReal.lean:295–306`, `WotsRealize.lean:44`)
`udH/preH/tcrH qs = qs·wotsSignHistHashes + (wotsAnswerHashes + wotsWinHashes / wotsPreHashes / wotsTcrHashes)`
(the counts of `Reduction.Open.wots*_phase2_open_hashes`; `= 121857·qs + 130239 / 130274 / 146514`),
`q2 qf qs ℓ H = qf·1 + H·thashCost len + (qs + 2)·hmsgCost ℓ` (`thashCost 35 = 11`,
`hmsgCost ℓ = (ℓ+56)/64 + 3`), `Lw = (22 + 16·len + 8)/64 = 9`.
The numerals are proved equal to the `Reduction.Open` counts (`chU_eq`, `collU_eq`, `chW_eq`,
`collW_eq`: `#inst·len`, `wotsQc + #inst·len·(w-1)`, `#inst·len·(w-1)`, `wotsQc + #inst·len`,
from `udCollB_128s`, `tcrCollB_128s`, `wotsInsts_length_128s`); they are stated as numerals only
because the kernel would otherwise try to evaluate `wotsQc Link.vp` when comparing.

`P5.Le` bounds (`:387`, `:392`, `:397`):
`pU_le / pP_le / pW_le (qf qs ℓ) : (p qf qs ℓ).Le (QcW qf qs ℓ) NW` with
`QcW qf qs ℓ = qf + 11 * (121857 * qs + 146514) + (qs + 2) * ((ℓ + 56) / 64 + 3)` (`:361`),
`NW = 1062560399506556770327551 ≈ 2^79.81` (`:364`); `L = 9 ≤ 10`.

Axioms: realisers `[propext, Classical.choice, Quot.sound]`; `p*_le` `[propext, Quot.sound]`.

## How (one line each)
- `WotsPort`: port variants `wUdP/wPreP/wTcrP` of `wotsUdOpenAll/…` (forger's compression queries as
  game queries), fusion (`w*P_fusion`), counts: port ≤ qf, hash ≤ udH/preH/tcrH, `H_msg` ≤ qs+2,
  no long `Thash`/`H_msg` query (walk lemmas `pw_*` generic in the counted predicate).
- `WotsReal`: transport `stepUd/stepPre/stepTcr` (`Transport.r*_setPrf_S`), `udDist/preInv/tcrForge`
  = chain substitution (`chainImpl`) of the port programs, `*_inst` (`= second phase at table g`),
  `chain_count` (compression ≤ port + hash·thashCost B + hmsg·hmsgCost ℓ), `*_bound`.
- `WotsUniv`, `WotsCount1`: semantic collection/challenge counts (`simChoose_bWotsWith_count`) turned
  into `IsQueryBoundP` via a universal counting oracle (`qb_of_univ`).
- `WotsLen`: every collection query of the first phases is on `1, 2, len, k` values.
- `WotsRealize`: the adversaries `udAdv/preAdv/tcrAdv` and `B g = inst A g` (`*Adv_inst`).

## Not done / caveats
- Only the 128s numerals are used for `qch`, `qc` (the realisers are for `Link.vp` anyway).
- `q₂` charges every hash query of the second phase at the `Thash` cost of `len` values (11), and
  `H_msg` separately (`qs + 2` of them); no finer split.
- `WotsLen.rPre_choose_ok`, `rTcrT_choose_ok` (unused helpers) use local `maxHeartbeats 2000000`;
  `WotsRealizers` uses it on the three `*_len` lemmas (kernel-checked via `kexact`).
- Proofs use `kexact` (from `Ideal/Transport/Sign.lean`: kernel-only definitional check, no axiom).
- Not composed into `suf_final`/`euf_final` (coordinator's job); not independently audited.
