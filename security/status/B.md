# B — tight FORS term (Task 1, closed) and per-arity TCR split (Task 2, partly conditional)

**(Note added by the W6 documentation sweep) Task 2 is now closed, unconditionally:** the hypothesis `VerifyAritySound` is proved (`Reduction.verifyAritySound`, `Reduction/VerifyArity.lean`, `status/ARITY.md`); unconditional phase-1 forms in `Reduction/TcrSplitClosed.lean`, current theorems `slhdsa_*_cma_final_split` in `Reduction/HeadlineSplit.lean` (lazy/sparse adversaries, SUF and EUF, internal and external, 128s instances); per-class caps in `Reduction/TightCaps.lean`. Wherever this file says "conditional", "not proved" or "not done" about `VerifyAritySound` or the split, read it as the state when the file was written. "Headline" below means the phase-1 theorem `slhdsa_euf_cma`.

Taken over from the previous owner after a network failure; `Reduction/ForsTight.lean` was found
complete and was audited, the rest is new. Nothing existing was edited.

## Files (all check with `lake env lean <File>.lean`, no warnings, no `sorry`/`axiom`/`native_decide`)

| file | lines | imports | content |
|---|---|---|---|
| `Reduction/ForsTight.lean` | 891 | VCVio `OpenPREFromTCRDSPR` only | generic OpenPRE ≤ DSPR + 3·TCR |
| `Reduction/ForsTightFinal.lean` | 283 | `Reduction.Final`, `.NonVacuity`, `.Instance128s`, `.ForsTight` | games, reductions, resource lemmas, corollaries |
| `Reduction/ForsTightNonVacuity.lean` | 224 | `Reduction.ForsTightFinal` | non-vacuity of the two new games |
| `Reduction/TcrSplit.lean` | 501 | VCVio `SMDTTCR` only | generic per-class split of SM-TCR |
| `Reduction/TcrSplitFinal.lean` | 365 | `Reduction.Final`, `.TcrSplit`, `.ForsTightFinal` | split at `bTcr`, conditional headline |

`.olean`s for all five were written by hand into `.lake/build/lib/lean/Reduction/`. The lead must
add the five imports to `Reduction.lean`. Every `#print axioms` (at the end of each file) shows
`[propext, Classical.choice, Quot.sound]` or less. `scratch/B` is deleted (`scratch/A` is A's).

## Task 1 — audit of `ForsTight.lean` and what it proves

```lean
theorem Reduction.ForsTight.openPRE_le_dspr_add_three_tcr [SampleableType M]
    {prob : Problem ι PkSeed Tweak M Y} (hU : prob.HasUniformInputs) (adv : Adversary prob) :
    advantage adv ≤
      SM_DT_DSPR_SourceFinalValidity.advantage (toDSPR adv) +
        3 * SM_DT_TCR_SourceFinalValidity.advantage (toTCR adv)
```

(namespaces `TweakableHash.SM_DT_OpenPRE_SourceFinalValidity`; classes `DecidableEq Tweak/M/Y`,
`Inhabited M`, `Fintype M`.) Findings of the audit:

- **Unconditional.** It does not use VCVio's `CountingInterface`; the implication is proved
  directly. Only hypothesis: `prob.HasUniformInputs` (`inputGen = $ᵗ M`), which is `rfl` for
  `forsOpenPreProblem`. Arbitrary adversary, arbitrary problem (any collection, any cap).
- **Games are the genuine ones.** `SM_DT_DSPR_SourceFinalValidity` (VCVio) is EasyCrypt
  `SMDTDSPR.SM_DT_DSPR` / HK22 SM-DSPR: the adversary selects `(tweak, input)` targets with the
  seed hidden, then outputs `(j, b)`; it wins iff the monitor is valid (≤ cap targets, distinct
  tweaks) and `b = [∃ x' ≠ xⱼ, F(P,Tⱼ,x') = F(P,Tⱼ,xⱼ)]`. `advantage = Pr[DSPR] − Pr[SPprob]`
  truncated at 0, where `spExperiment` runs the same adversary and accepts iff the selected
  target has a second preimage: exactly `maxr 0 (DSPR − SPprob)` of `EUFCMA_SPHINCS_PLUS`
  (`SPHINCS_PLUS.ec:4349`). `SM_DT_TCR_SourceFinalValidity` is EC `SMDTTCR` (stand-alone,
  final-validity). I compared both against `TweakableHashFunctions.eca`.
- **Coefficients** 1 and 3, as in the paper/EC. No term is trivially ≥ 1 (see non-vacuity).
- **Reductions** are VCVio's `toDSPR`, `toTCR`: run `adv.pick` once, keep the first `numTargets`
  tweaks, sample one input per tweak and submit `(tweak, input)` as a target, run `adv.find` once
  answering opening `j` by a list lookup; TCR forwards `(j, m)`, DSPR returns
  `(j, [m ≠ xⱼ ∨ j opened])`. `#print axioms toTCR` = `[propext]`, `toDSPR` =
  `[propext, Quot.sound]`: no choice, no enumeration, no search. (The fibre permutation
  `exists_fibre_shift` and `Fintype M` occur in proofs and in the DSPR game's winning predicate
  only.)
- Proof idea (for a reviewer): all four experiments are one experiment `raw` followed by four
  predicates; pointwise `W + S ≤ D + T + 2·E₁`; `Pr[E₁] ≤ Pr[E₂] ≤ Pr[T]` by resampling the
  hidden input of the selected, unopened target along a fibre-preserving fixed-point-free
  permutation (`find_run_congr`, `sampleT_modify`, `inner_le`).

### New in `ForsTightFinal.lean` (exact statements)

```lean
def forsDsprProblem (pkSeedDist) : SM_DT_DSPR_SourceFinalValidity.Problem Empty PkSeed AdrsKey Y Y :=
  .standalone (fHash vp prims pkSeedDist) (openPreTargets vp)
def forsTcrProblem (pkSeedDist) : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed AdrsKey Y Y :=
  .standalone (fHash vp prims pkSeedDist) (openPreTargets vp)
abbrev ForsOpenPreAdv vp prims pkSeedDist :=
  SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsOpenPreProblem vp prims pkSeedDist)
noncomputable def toDspr (B : ForsOpenPreAdv vp prims pkSeedDist) : …Adversary (forsDsprProblem …)
noncomputable def toTcr  (B : ForsOpenPreAdv vp prims pkSeedDist) : …Adversary (forsTcrProblem …)

theorem forsOpenPre_le [Fintype prims.Y] (B : ForsOpenPreAdv vp prims pkSeedDist) :
    SM_DT_OpenPRE_SourceFinalValidity.advantage B ≤
      SM_DT_DSPR_SourceFinalValidity.advantage (toDspr B) +
        3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr B)

noncomputable def boundForsTight pkSeedDist B₁ B₂ B₃ D T B₅ B₆ B₇ B₈ : ℝ≥0∞   -- `bound` with slot 4
  -- replaced by (DSPR.advantage D + 3 * TCR.advantage T)

theorem bound_le_boundForsTight B₁ B₂ B₃ (B₄ : ForsOpenPreAdv …) B₅ B₆ B₇ B₈ :
    bound pkSeedDist B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ ≤
      boundForsTight pkSeedDist B₁ B₂ B₃ (toDspr B₄) (toTcr B₄) B₅ B₆ B₇ B₈

theorem forsTight_of_bound {α : Sort*} (Adv : α → ℝ≥0∞) b₁ … b₈
    (h : ∀ a, Adv a ≤ bound pkSeedDist (b₁ a) … (b₄ a) … (b₈ a)) :
    ∀ a, Adv a ≤ boundForsTight pkSeedDist (b₁ a) (b₂ a) (b₃ a) (toDspr (b₄ a)) (toTcr (b₄ a))
      (b₅ a) (b₆ a) (b₇ a) (b₈ a)

theorem slhdsa_euf_cma_fors_tight [Fintype prims.Y] (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundForsTight pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A)
        (toDspr (bOpenPre A)) (toTcr (bOpenPre A)) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A))

instance instFintypeY128s : Fintype Link.prims.Y   -- Y = Vector UInt8 16
theorem slhdsa_sha2_128s_euf_cma_fors_tight optRand pkSeedDist A : …   -- no hypothesis
```

Resource lemmas: `toTcr_choose_run`, `toDspr_choose_run` (selection phase inside the game =
`B.pick` once, then one uniform sample per retained tweak; targets = these pairs),
`toTcr_targets`, `toDspr_targets` (targets are the retained prefix of `B`'s commitment, in order;
count ≤ `openPreTargets vp` and ≤ number of tweaks `B` committed), `toTcr_forge`, `toDspr_guess`
(second phase = one run of `B.find`, openings by list lookup, constant post-processing).

`[Fintype prims.Y]` is needed only to *state* the DSPR game.

### Non-vacuity (`ForsTightNonVacuity.lean`)

- DSPR: `forsDspr_trivial_adv_zero` (= 0); `forsDsprGuesser_adv_one` (if `F(pk,t,·)` has no
  second preimage of `x`, targeting `(t,x)` and guessing `false` gives advantage 1);
  `forsDsprGuesser_adv_zero_of_collision` (guessing `true` on a target that always has a second
  preimage gives 0, not 1: the baseline subtraction bites); toy: `toyInj_forsDspr` on the new
  bundle `toyInjPrims` (`Thash` = first input), `toy_forsDspr_zero` on `toyPrims`.
- TCR (final-validity, on `F`): `forsTcr_trivial_adv_zero`, `forsTcrCollider_adv_one`,
  `toy_forsTcr`.

### Composition with A and C1

- A keeps its lazy `bOpenPre'` an adversary of `forsOpenPreProblem`. From A's
  `slhdsa_euf_cma_efficient : … ≤ bound pkSeedDist b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈` the lead gets the tight
  version by `forsTight_of_bound` (family form) or `(h).trans (bound_le_boundForsTight ..)`.
  The resource lemmas are stated for an arbitrary `B`, so they apply to A's adversary verbatim.
  Note `toDspr B`/`toTcr B` still submit one target per committed tweak (all `2^h·k·2^a` leaves
  for `bOpenPre`): they are poly in `B`'s commitments, not in `qs` (A-interface.md explains why
  no SM adversary can be).
- C1 (`Reduction.Guarded.unforgeableAdvantage_le`) is on the left-hand side only:
  `Adv_ext(A) ≤ Adv_int(toInternal A) ≤ boundForsTight … (… (toInternal A))` by
  `slhdsa_euf_cma_fors_tight hS (toInternal A)`.

## Task 2 — splitting `Adv^{SM-TCR}_{Thash}(bTcr A)`

### Generic, unconditional (`TcrSplit.lean`, namespace `Reduction.TcrSplit`)

For `th : TweakableHash PkSeed Tweak (List Y) Y`, a class `P : List Y → Prop` (decidable), cap `N`:

- `classProblem th P N : SM_DT_TCR_Problem Unit PkSeed Tweak {xs // P xs} Y` — SM-TCR
  (rejection-on-arrival, same game family as `tcrProblem`/`wotsTcrProblem`) on `th` restricted to
  `P`, with the whole `th` as collection (`collOf th`), cap `N`. This is EC's `SM_DT_TCR_C`.
- `restrict P d B` for an arbitrary `B` against `.standalone th N`: runs `B.choose` once, keeps
  the list of `B`'s accepted targets, answers `none` itself where `B`'s game would refuse,
  sends accepted class-`P` targets to the challenge oracle and the others to the collection
  oracle, runs `B.forge` once and forwards `(j, m)` with translated index iff `m` and target `j`
  are in `P`. `#print axioms restrict` = `[propext]`.

```lean
theorem choose_coupling …   -- the class game never refuses; its state is a function of B's targets
theorem advantage_eq_raw (B) : SM_DT_TCR_Advantage B = 𝒟[win th <$> raw B] {true}
theorem restrict_advantage_eq (d) (B) :
    SM_DT_TCR_Advantage (restrict P d B) = 𝒟[winIn th P <$> raw B] {true}
theorem prEvent_le_sum_restrict (P : κ → List Y → Prop) (d) (B) (E : Raw … → Bool)
    (hE : ∀ r, E r = true → ∃ i, winIn th (P i) r = true) :
    𝒟[E <$> raw B] {true} ≤ ∑ i, SM_DT_TCR_Advantage (restrict (P i) (d i) B)
theorem advantage_le_sum_add_cross (P) (d) (B) :
    SM_DT_TCR_Advantage B ≤ ∑ i, SM_DT_TCR_Advantage (restrict (P i) (d i) B) +
      𝒟[winCross P th <$> raw B] {true}
theorem advantage_le_sum_of_no_cross …
```

`winIn th P` = "`B` wins and both colliding messages are in `P`" — so the restricted advantage
is an **equality**, and the split is a union bound; `winCross` = "`B` wins by a collision in no
class" is the exact correction term.

### At `bTcr` (`TcrSplitFinal.lean`)

`thashArityProblem vp prims pkSeedDist n := classProblem (thashList …) (·.length = n) (tcrTargets vp)`
(collection `= thashColl vp prims` by `rfl`), `bTcrAr n A := restrict … (bTcr A)`,
`arities vp := ![1, 2, len, k]`, `tcrSplitSum A :=` the four advantages at `n = 1, 2, len, k`.

Unconditional: `bTcrAr_advantage_eq`, `bTcr_advantage_le_split_add_cross`; non-vacuity of the
per-arity games: `thashArity_trivial_adv_zero`, `thashArityCollider_adv_one`, `toy_thashArity`.

Answer to "does `findCollision` always return a same-arity collision?": **not by its
definition** (it compares tweak, inequality and hash value only), and **`Adv(bTcr A) ≤ Σ` is not
true as stated**: when verification of the forgery yields no collision, `bTcr A` outputs the
fixed guess `(0, [])`, which wins its own game whenever `Thash pk t₀ [] = Thash pk t₀ m₀` — a
cross-arity collision that no restricted adversary can use. The split is therefore proved at
the level the headline actually uses, `Pr[G2 ∧ class = tcr]`:

```lean
def VerifyAritySound : Prop :=          -- named hypothesis; not proved in this package, PROVED LATER: Reduction.verifyAritySound
  Structural vp prims → ∀ tbl pkSeed msg sig,
    ∀ c ∈ verifyCalls (idealPk vp prims tbl pkSeed) msg sig, ∀ t ∈ honestCalls tbl pkSeed,
      t.1 = c.1 → c.2.length = t.2.length ∧ ∃ i : Fin 4, t.2.length = arities vp i

theorem stepTCR_split (hS : Structural vp prims) (hAr : VerifyAritySound vp prims) (A) :
    prTrue (g2Class A .tcr) ≤ ∑ i, SM_DT_TCR_Advantage (bTcrAr (arities vp i) A)

theorem final_of_steps_tcr …   -- `final_of_steps` with the tcr branch bounded by any `X`; unconditional

theorem slhdsa_euf_cma_tcr_split (hS) (hAr : VerifyAritySound vp prims) (A) :
    Adv A ≤ PRF + PRF_msg + ITSR + OpenPRE(bOpenPre A) + tcrSplitSum A + (w−2)·UD + PRE + TCR_F(rTcr)

theorem slhdsa_euf_cma_fors_tight_tcr_split [Fintype prims.Y] (hS) (hAr) (A) :
    Adv A ≤ PRF + PRF_msg + ITSR + (DSPR(toDspr (bOpenPre A)) + 3·TCR(toTcr (bOpenPre A)))
            + tcrSplitSum A + (w−2)·UD + PRE + TCR_F(rTcr)
```

**Conditional theorems: `stepTCR_split`, `slhdsa_euf_cma_tcr_split`,
`slhdsa_euf_cma_fors_tight_tcr_split`. Hypothesis: `VerifyAritySound vp prims`.**

What the hypothesis says and what proving it needs. It is deterministic and non-cryptographic:
a hash call made while verifying an arbitrary signature and an honest-structure call at the same
tweak have the same arity, one of `1, 2, len, k`. I believe it is true (tweak = encoding of an
address; type and, for `FORS_TREE`, height 0 vs > 0 fix which of `F/H/T_len/T_k` is called, in
`structureVia` and in `forsPkFromSigWith`/`pkFromSigWith` alike; `hS.keyInj` gives address
equality), but it is **not proved** in this package (proved later, `Reduction/VerifyArity.lean`). Needed: (a) an arity-annotated version of the `mf_*` trace
lemmas of `TCR.lean` (`honestCalls.map (key, length) = (annotated mf_all).map …`, about 100
lines, the combinators `mf_Tr_bind/ofFnM/forM/merkle` are reusable with `K := AdrsKey × ℕ`);
(b) the same for the verification programs of an arbitrary signature (no existing analogue:
`sub_*` covers only the reference signature), including that every verification address
satisfies `AddressFacts` so that `keyInj` applies. Estimate 400–600 lines. Alternative route:
strengthen `col_Coll` (lines 532–985 of `TCR.lean`) with `c.2.length = c'.2.length` and use an
arity-filtered `findCollision`; that needs a copy of the `col_*` block since `TCR.lean` is frozen.

Differences from the paper that remain even with the hypothesis discharged:
- FORS-tree `H` and XMSS-tree `H` share the arity-2 term (same function; separating them needs
  the address type of each target, which `honestCalls` does not record);
- an `F` term (`bTcrAr 1 A`) appears in the collision branch; the paper has none there. Dropping
  it needs "a `tcr`-class forgery never collides at arity 1", not investigated;
- every class game has cap `tcrTargets vp` (all hash calls), not the per-function count; the
  restricted adversary's actual targets are the arity-`n` honest calls (`choose_coupling`:
  state `= gState P (honestCalls …)`), so the caps can be sharpened by a counting lemma only;
- if `len = k` (or either is 1 or 2) two of the four terms coincide and are counted twice.

The split addresses the n = 24/32 concern (F uses SHA-256, H/T_l SHA-512): arity 1 is separated
from arities 2, `len`, `k`.

### Composition

`final_of_steps_tcr` takes the same step hypotheses as `final_of_steps` plus
`h₆ : prTrue (g2Class A .tcr) ≤ X`, so the lead can combine `stepTCR_split` with A's lazy
`bPrfMsgL`/`bItsrL` steps; the FORS term is then tightened by `forsOpenPre_le` (as in
`slhdsa_euf_cma_fors_tight_tcr_split`).

## Not done

- `VerifyAritySound` (above) — done later: `Reduction.verifyAritySound`.
- No 128s instance of the Task 2 theorems (they are conditional) — done later: `Reduction/TcrSplitClosed.lean`, `Reduction/HeadlineSplit.lean`.
