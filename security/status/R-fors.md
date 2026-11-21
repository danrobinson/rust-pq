# R-fors — the FORS-leaf realisers (`RealizesDspr`, `RealizesForsTcr`; SUF and EUF)

Agent `fors`. All files build (`lake build Ideal.Realize.ForsRealize` → "Build completed successfully
(7260 jobs)"), no `sorry`/`axiom`/`native_decide`/`bv_decide`; every `#print axioms` line is
`[propext, Classical.choice, Quot.sound]` (or a subset). Only `set_option synthInstance.maxHeartbeats
400000` is set (file-wide, all seven files). Not imported by `Ideal.lean` (coordinator: add the seven
modules below, or just `Ideal.Realize.ForsRealize`, which imports the rest).

## Headline results (`Ideal/Realize/ForsRealize.lean`, namespace `Ideal.Realize.Fors`)

Common binders: `S : ForgerI`, `oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)`,
`pkSeedDist : ProbComp (Bytes 16)`, `{qf qs ℓ : ℕ}` and exactly the four agreed hypotheses
```
(hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
(hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
(hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
(hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
```
(`isPortQ`, `isSignQ`, `isLongQ` = `Ideal.Realize.*` from `Port.lean`). No other hypothesis.

- `:169` `noncomputable def realizesDspr_S : RealizesDspr pkSeedDist (fun g => Reduction.toDspr
  (Reduction.Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g))) (pFors qf qs ℓ)`
- `:183` `realizesDspr_E` — the same with `S.typedE`
- `:197` `realizesForsTcr_S : RealizesForsTcr pkSeedDist (fun g => Reduction.toTcr
  (Reduction.Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g))) (pFors qf qs ℓ)`
- `:209` `realizesForsTcr_E` — the same with `S.typedE`
- `:34` `def pFors (qf qs ℓ : ℕ) : P3 := ⟨0, openPreTargets Link.vp, q2Fors qf qs ℓ⟩`
- `Ideal/Realize/ForsBound.lean:100` `def q2Fors qf qs ℓ := qf * 1 + forsHashes qs * thashCost
  Link.vp.params.len + (qs + (1 + qs)) * hmsgCost ℓ`, `:95` `forsHashes qs := Lazy.keygenHashes
  Link.vp + qs * forsSignHashes Link.vp + (1 + qs + Link.vp.params.k)` (the count of
  `Reduction.Open.forsFindOpen_hashes`)
- `:46` `theorem q2Fors_eq : q2Fors qf qs ℓ = qf + 2968229 + 21450308 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3)`
  (derived: `forsSignHashes_128s`, `keygenHashes = 269824`, `k = 14`, `thashCost 35 = 11` by `decide`)
- `:38` `theorem openPreTargets_eq : openPreTargets Link.vp = 528905046081400263933952` (`decide`; ≈ 2^78.8)
- `:54` `theorem pFors_le (hQ : qf + 2968229 + 21450308 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3) ≤ Qc)
  (hN : 528905046081400263933952 ≤ N) : (pFors qf qs ℓ).Le Qc N`

The equalities behind `success`/`sp`/`eq` are adversary EQUALITIES (`Ideal/Realize/ForsEq.lean:75–97`):
`dspr_eq_S/E g : toDspr (bOpenPreS (S.typedS/E (optRandU oR) pkSeedDist g)) = instForsDspr (dsprAdvI S oR pkSeedDist) g`,
`tcr_eq_S/E g : toTcr (…) = instFors (tcrAdvI S oR pkSeedDist) g`. The same ideal adversary serves SUF and EUF.

## Construction (files, in import order)
- `ForsProg.lean`: game interface `GP = forsG + hS`; `liftG`; port forger run `portRunF`; port program
  `forsFindOpenP` (keygen and answer extraction = those of `forsFindOpen`, lifted); `portAns g`;
  `fusion2` (generic); **`forsFindOpenP_fusion`** (`:197`): port answered by `g` after the table
  interpretation = table interpretation of `forsFindOpen` at the forger with port answered by `g`.
- `ForsGuess.lean`: over `P₀ = R₀ dT dH`: `chainImplP` (hash query ↦ `hashC` chain), `outerC`
  (openings answered inside, port ↦ compression query), `phase2C`; **`phase2C_inst`** (`:110`).
- `ForsAdv.lean`: `codec₀`, transport `toDspr/toTcr_{S,E}_eq` (from `Transport.toDspr_setPrf(_S)`,
  `toTcr_setPrf(_S)`), `phase2_open`, `phase1P` (irreducible copy of `forsPhase1 Link.vp P₀`, see
  below), `dsprAdvI`, `tcrAdvI`.
- `ForsEq.lean`: the four adversary equalities.
- `ForsCount.lean`: counts of `forsFindOpenP`: port `≤ qf`, hash `≤ forsHashes`-shape (from
  `openKeygen_kindBound`, `forsSignOpen_kindBound`, `findAnswerO_kindBound`, `keygenB_hash`,
  `forsSignB_hash`), `H_msg ≤ qs + (1+qs)`, no long query; run invariants (log length, message lengths).
- `ForsBound.lean`: `chainImplP_bound` (via `qb_simulateQ_classes`, `thashC_bound`, `hmsgC_bound`),
  `outerC_bound`, **`phase2C_bound`** (`:109`), `forsPhase1_chal`, `chal_of_eq`.

## Notes / pitfalls (for other realiser agents)
- A theorem whose statement contains `IsQueryBoundP (forsPhase1 Link.vp P₀) …` fails with "maximum
  recursion depth" even with `:= sorry` (the elaborator/linters whnf the statement; the head constructor
  of the closed program needs the length of the WOTS+ index list). Fix: `noncomputable irreducible_def
  phase1P := forsPhase1 Link.vp P₀` and state bounds via `chal_of_eq X (hX : X = forsPhase1 …)`.
- Structure equality `toDspr X = instForsDspr A g`: first `refine (dsprAdv_eta _).trans ?_`,
  `unfold instForsDspr dsprAdvI`, then `dsprAdv_mk_congr ?_ ?_`, `dsimp only` in each goal, explicit
  `Eq.trans` with all arguments given (plain `exact (a).trans (b)` / `rw` time out).
- Give `(prims := P₀)` explicitly to generic lemmas (`typedP_bound`, `typedP_out`, `chal_of_eq`).

## Not done / not verified
- Nothing of the task is open. Not checked: that the coordinator's `N` is ≥ `openPreTargets Link.vp`
  (≈ 2^78.8 challenge queries — the FORS-leaf target cap, fixed by the reduction, not by the forger).
- `q2Fors` charges every hash query `thashCost 35 = 11` compressions and every `H_msg` query an extra
  `hmsgCost ℓ`; tighter per-kind accounting is possible but not needed for `P3.Le`.
