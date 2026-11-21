import Reduction.HeadlineFinal

/-!
# Resources of the adversaries of the final headline (phase 3 integration)

One bundle for the twelve adversaries of `boundFinalTight` as instantiated in the final
theorems (`slhdsa_*_cma_final_memo`, `slhdsa_*bytes*_cma_final`, the linear forms and
`E2E.rust_security`): for a typed forger `A` with at most `qs` signing queries,

* `direct` — package W3's `Resources2.FinalResourcesDirect A qs c`: every adversary other than
  the four class adversaries and the chain SM-TCR adversary is literally the one of the final
  bound, and for those two families see the next items;
* `memo_*` — the class adversaries `bTcrArM n A` (package W5) in the **tight-cap** class games
  `thashArityProblemT`: phase 1 is the program of `bTcrArS n A` (`memo_choose`, by `rfl`), run
  in closed form (`memo_run`), exactly `arityTargets vp n` targets — the cap (`memo_cap`) — and
  `tcrTargets − arityTargets vp n` collection queries (`memo_phase1`); phase 2 is the open
  program `memoForgeOpen A L pk` followed by a hash-free translation (`memo_phase2`), with at
  most `memoP2` hash evaluations (`memo_phase2_hashes`);
* `wtcrT_*` — the chain adversary `rTcrT pkSeedDist (bWotsS A)` in the tight-cap game
  `wotsTcrProblemT`: same two programs as `rTcr pkSeedDist (bWotsS A)` (by `rfl`, so
  `direct.wtcr_phase2`, `direct.wtcr_phase2_hashes` apply), accepted targets `≤` the cap.

## The table (SHA2-128s numerals: `final_resources_final_128s`)

Per SM adversary: (a) oracle queries before the seed is revealed, by kind; (b) own hash
evaluations after the seed is revealed; (c) fresh uniform samples.  **F** = formal (a field of
the bundle), **A** = argued only (counting argument in `status/W3.md` / `status/W5.md`, not a
theorem).  `qs` = signing queries of the forger.

| adversary (game) | (a) pre-seed queries | (b) post-seed own hashes | (c) samples |
|---|---|---|---|
| `toDspr`/`toTcr (bOpenPreS A)` (SM-DSPR(F), SM-TCR(F) at FORS leaves) | targets: exactly `2^h·k·2^a` = `528905046081400263933952`; collection: 0 — **F** | `≤ 269839 + qs·1950028`; `≤ 14·qs` simulated openings — **F**, nothing uncounted | exactly `323449759100660631040 + 528905046081400263933952` — **F** |
| `bTcrArM n A`, `n = 1, 2, len, k` (SM-TCR on `F`, `H`, `T_len`, `T_k`, tight cap) | targets: exactly the cap, `533756792467910173399552` / `528785142244921151848447` / `9241421688590303744` / `9223372036854775808`; targets + collection = `1062560399506556770327551` — **F** | `≤ 269824 + qs·2007385 + 7857` — **F** (includes the verification of the forgery and the collision test) | exactly `529228495840500924564992` — **F** |
| `rUd (bWotsS A)` (SM-UD(F)) | challenges `≤ 323449759100660631040` — **F**; collection `≤ 1062560399506556770328574` — **A** | `≤ qs·121857 + 525` — **F**; plus the pure tail `wotsAnswer` `≤ 129714` — **A** | inner `bWotsS A`: exactly `528905046081400263933952` — **F**; wrapper: one hybrid index and `≤ 323449759100660631040` values — **A** |
| `rPre (bWotsS A)` (SM-PRE(F)) | challenges `≤ 323449759100660631040` — **F**; collection — **A** | `≤ qs·121857 + 560` — **F**; `wotsAnswer` — **A** | as `rUd`, no hybrid index |
| `rTcrT (bWotsS A)` (SM-TCR(F) on chains, tight cap) | targets `≤ 4851746386509909465600` = the cap — **F**; collection `≤ 1058032102879147521494014` — **A** | `≤ qs·121857 + 16800` — **F**; `wotsAnswer` — **A** | inner as above — **F**; wrapper `≤ 323449759100660631040` — **A** |

The PRF, PRF_msg and ITSR adversaries have a single phase (no seed reveal): `≤ 17920 +
qs·182784` PRF queries (`bPrfC`, `bPrfWC`; their own hashing is not modelled), resp. `≤ qs`
game queries, `≤ 17920 + qs·182784` fresh draws and `≤ 269824 + qs·2007385` hash evaluations
(final verification excluded) — **F**.

Argued only, for all rows: that the phase-1 programs do no hashing of their own (inspection:
no `prims.*` evaluation occurs in them; a formal "zero" is not expressible in the open-program
model, which certifies the programs one writes down); list work (lookups in tables of
structure size) and the size of the state carried across the seed reveal; no lower bounds.
The class adversaries store `(tweak, input)` pairs, not hash values, so the signatures for the
forger are still computed by local hashing after the reveal (the `qs·2007385` term).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

section

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

-- as in `Reduction/TightCaps.lean`: never evaluate the caps during unification
attribute [local irreducible] arityTargets tcrTargets

/-- **Resources of the adversaries of the final bound** for a forger `A` with at most `qs`
signing queries; `c` are the closed forms of `Resources2.directCounts`, `memoP2` the bound on
the own post-seed hash evaluations of each class adversary.  See the file header for the table
and for what is formal and what is argued. -/
structure FinalResourcesFinal (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (c : Resources2.DirectCounts) (memoP2 : ℕ) : Prop where
  /-- W3's bundle (PRF, PRF_msg, ITSR, FORS-leaf and chain adversaries; `bTcrArS`). -/
  direct : Resources2.FinalResourcesDirect A qs c
  /-- Phase 1 of `bTcrArM n A` is the program of `bTcrArS n A`. -/
  memo_choose : ∀ n, (bTcrArM n A).choose = (bTcrArS n A).choose
  /-- Phase 1 in the tight-cap game, in closed form: `structCells` uniform samples, then the
  deterministic structure walk. -/
  memo_run : ∀ n pk,
    (simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArM n A).choose).run ([], []) =
      (fun tbl => ((tbl, honestCalls tbl pk),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          ((fun xs => Tables.updateList (fun _ => default) (Lazy.structSecIdx vp) xs) <$>
            Tables.sampleList prims.Y (Lazy.structSecIdx vp).length)
  /-- Exactly `arityTargets vp n` targets; targets + collection queries = `thashTargets`. -/
  memo_phase1 : ∀ n, Resources2.TcrPhase1Counts (bTcrArM n A) (arityTargets vp n) c.thashTargets
  /-- The cap of the tight class game is attained in every run. -/
  memo_cap : ∀ n pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
      (bTcrArM n A).choose).run ([], [])),
    z.2.1.length = (thashArityProblemT vp prims pkSeedDist n).numTargets
  /-- Phase 2 is the open program `memoForgeOpen`, then a hash-free translation. -/
  memo_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (n : ℕ) (tbl : SecretTable vp prims)
      (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed),
    (liftM ((bTcrArM n A).forge (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (Resources2.memoForgeOpen A L pk) >>= fun jm => pure (classOut prims n L jm)
  /-- Own hash evaluations after the seed reveal. -/
  memo_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι)
      (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed),
    IsQueryBoundP (Resources2.memoForgeOpen (gspec := gspec) A L pk)
      (fun t => Lazy.kind t = .hash) memoP2
  /-- `rTcrT` runs the programs of `rTcr`. -/
  wtcrT_choose : (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose =
    (rTcr pkSeedDist (Lazy.bWotsS A)).choose
  wtcrT_forge : (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).forge =
    (rTcr pkSeedDist (Lazy.bWotsS A)).forge
  /-- Accepted targets of `rTcrT (bWotsS A)` in the tight-cap game: at most `wotsSteps`. -/
  wtcrT_cap : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (wotsTcrProblemT vp prims pkSeedDist) pk)
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose).run ([], [])),
    z.2.1.length ≤ c.wotsSteps

/-- **The resource theorem for the final adversaries.** -/
theorem final_resources_final (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResourcesFinal A qs (Resources2.directCounts vp qs)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2)) where
  direct := Resources2.final_resources_direct hS A qs hA
  memo_choose := fun n => bTcrArM_choose n A
  memo_run := fun n pk => bTcrArM_choose_run_samples hS n A pk
  memo_phase1 := fun n => bTcrArM_phase1 hS n A
  memo_cap := fun n pk => bTcrArM_targets_eq_cap hS n A pk
  memo_phase2 := fun _ n tbl L pk => Resources2.bTcrArM_forge_open n A tbl L pk
  memo_phase2_hashes := fun _ L pk => Resources2.memoForgeOpen_hashes A qs hA L pk
  wtcrT_choose := rTcrT_choose _
  wtcrT_forge := rTcrT_forge _
  wtcrT_cap := fun pk => rTcrT_targets_le hS (Lazy.bWotsS A) pk

/-- Resources for an external (pure-interface) forger: `toInternal A` makes at most `qs`
signing queries and the bundle holds for it. -/
theorem final_resources_final_external (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) (qs : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((toInternal A).main pk) (fun i => i.isRight = true) qs) ∧
      FinalResourcesFinal (toInternal A) qs (Resources2.directCounts vp qs)
        (Lazy.keygenHashes vp + qs * Lazy.signHashes vp +
          (1 + Resources2.verifyHashes vp * 2)) :=
  ⟨toInternal_queryBound A qs hq, final_resources_final hS _ qs (toInternal_queryBound A qs hq)⟩

end

/-! ## SLH-DSA-SHA2-128s -/

/-- **Resources of the final adversaries at SLH-DSA-SHA2-128s, as numerals**
(`Resources2.directCounts128s qs`; class adversaries `≤ 269824 + qs·2007385 + 7857` own hash
evaluations after the seed reveal), together with the caps of the five re-capped games:
`533756792467910173399552`, `528785142244921151848447`, `9241421688590303744`,
`9223372036854775808` (`F`, `H`, `T_len`, `T_k`; old cap `1062560399506556770327551` each) and
`4851746386509909465600` (chains; old cap `5175196145610570096640`). -/
theorem final_resources_final_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResourcesFinal A qs (Resources2.directCounts128s qs) (269824 + qs * 2007385 + 7857) ∧
    ((thashArityProblemT Link.vp Link.prims pkSeedDist 1).numTargets =
        533756792467910173399552 ∧
      (thashArityProblemT Link.vp Link.prims pkSeedDist 2).numTargets =
        528785142244921151848447 ∧
      (thashArityProblemT Link.vp Link.prims pkSeedDist Link.vp.params.len).numTargets =
        9241421688590303744 ∧
      (thashArityProblemT Link.vp Link.prims pkSeedDist Link.vp.params.k).numTargets =
        9223372036854775808 ∧
      (thashArityProblem Link.vp Link.prims pkSeedDist 1).numTargets =
        1062560399506556770327551) ∧
    ((wotsTcrProblemT Link.vp Link.prims pkSeedDist).numTargets = 4851746386509909465600 ∧
      (wotsTcrProblem Link.vp Link.prims pkSeedDist).numTargets = 5175196145610570096640) := by
  refine ⟨?_, thashArityProblemT_cap_128s pkSeedDist, wotsTcrProblemT_cap_128s pkSeedDist⟩
  have h := final_resources_final structural_128s A qs hA
  rw [Resources2.directCounts_128s, keygenHashes_128s, signHashes_128s,
    Resources2.verifyHashes_128s] at h
  exact h

#print axioms final_resources_final
#print axioms final_resources_final_external
#print axioms final_resources_final_128s

end Reduction
