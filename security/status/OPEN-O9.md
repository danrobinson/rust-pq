# OPEN-O9 — answer-storing class TCR adversaries `bTcrArA n A` (all four deliverables, unconditional)
New files only (nothing existing touched); all compile without error/warning; oleans written
(`.lake/build/lib/lean/Reduction/Open/TcrStore{,Headline,Count,Cover}.olean`); no `sorry`/`axiom`/
`native_decide`/`bv_decide`. Namespace `Reduction.Open`. Only hypothesis anywhere: `Structural vp prims`.
Files (`Reduction/Open/`): `TcrStore.lean` (419 lines; imports `Open.WithHash`, `TcrMemoHeadline`; §1–2),
`TcrStoreHeadline.lean` (249; + `HeadlineFinal`; §3), `TcrStoreCount.lean` (481; §4 open program, pinning,
count given coverage), `TcrStoreCover.lean` (601; §4 coverage, unconditional count, 128s). Import chain:
`TcrStore ← TcrStoreCount ← TcrStoreCover`, `TcrStore ← TcrStoreHeadline`.
## 1. Adversary (`TcrStore.lean`)
```lean
abbrev Store prims := List ((prims.AdrsKey × List prims.Y) × prims.Y)          -- ((tweak, input), value)
def routeStepA th P N q (s : L × S) := (fun z => (z.1, (z.2, recAns th N q z.1 s.2))) <$> TcrSplit.routeStep th P N q s.1
  -- recAns: append (c, y) iff q is the target query c and the answer is `some y`;  routeA th P N := fun q => StateT.mk (routeStepA th P N q)
def ann th pk L := L.map fun c => (c, th.eval pk c.1 c.2);  def Sound pk S : Prop := ∀ e ∈ S, e.2 = prims.Thash pk e.1.1 e.1.2
def lkT pk S : PkSeed → AdrsKey → List Y → Y := fun pk' key xs =>                -- lookup, hash on a miss
  if pk' = pk then (match S.lookup (key, xs) with | some y => y | none => prims.Thash pk' key xs) else prims.Thash pk' key xs
noncomputable def storeForge n A (s : SecretTable vp prims × (List (AdrsKey × List Y) × Store prims)) pkSeed :=
  memoForge (prims := withTH prims (lkT pkSeed s.2.2) prims.Hmsg) n (castForger (lkT pkSeed s.2.2) prims.Hmsg A) (s.1, s.2.1) pkSeed
noncomputable def bTcrArA (n) (A : Forger vp prims optRand pkSeedDist) : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist n) where
  State := SecretTable vp prims × (List (prims.AdrsKey × List prims.Y) × Store prims)
  choose := (simulateQ (routeA (thashList vp prims pkSeedDist) (·.length = n) (tcrTargets vp)) (Lazy.bTcrS A).choose).run ([], [])
  forge := storeForge n A
```
Phase 1 = phase 1 of `bTcrArM` through `routeA` instead of `TcrSplit.route` (same queries; the state also
keeps one `Y` per accepted call). Phase 2 = `memoForge` (program of `bTcrArM`) with the tweakable hash
`lkT pk S`. Definition-level check (W5's checker, run outside the tree): `bTcrArA, storeForge, lkT, routeA,
routeStepA, recAns, ann, storeForgeOpen, memoImpl, pinImpl, hitB, emb, issue` flagged `[]` (control `bTcrAr` flagged).
## 2. Equal experiment
```lean
theorem choose_couplingA oa L : (simulateQ (oracles (classProblem th P N) pk) ((simulateQ (routeA th P N) oa).run (L, ann th pk L))).run (gState P L) = (simulateQ (oracles (.standalone th N) pk) oa).run (L, []) >>= fun z => pure ((z.1, (z.2.1, ann th pk z.2.1)), gState P z.2.1)
theorem bTcrArA_choose_run (hS) n A pk : (simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk) (bTcrArA n A).choose).run ([], []) =
    (fun tbl => ((tbl, (honestCalls tbl pk, ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk))), TcrSplit.gState (·.length = n) (honestCalls tbl pk))) <$> Lazy.sparseTable vp prims
theorem storeForge_eq n A tbl L S pkSeed (hS : Sound pkSeed S) : storeForge n A (tbl, (L, S)) pkSeed = memoForge n A (tbl, L) pkSeed   -- no coverage needed
theorem bTcrArA_experiment_eq (hS : Structural vp prims) n A : SM_DT_TCR_Experiment (bTcrArA n A) = SM_DT_TCR_Experiment (bTcrArM n A)
theorem bTcrArA_advantage_eq / _eq_tight (hS) n A : Adv (bTcrArA n A) = Adv (bTcrArM n A) / = Adv (bTcrArST n A);  bTcrArA_phase1 (hS) n A : Resources2.TcrPhase1Counts (bTcrArA n A) (arityTargets vp n) (tcrTargets vp)
theorem bTcrArA_state (hS) n A pk : ∀ z ∈ support (run), ∃ tbl, z.1 = (tbl, (honestCalls tbl pk, ann … (honestCalls tbl pk))) ∧ lengths = tcrTargets vp ∧ Sound pk (ann …)
```
## 3. Headline (`TcrStoreHeadline.lean`) — existing theorems rewritten with `boundFinalStore_eq`
`boundFinalStore_eq hS A B₁ B₂ : boundFinalTight … (bTcrArA 1 A) (bTcrArA 2 A) (bTcrArA len A) (bTcrArA k A) … = boundFinalTight … (bTcrArM …) …`;
`betaEuf/SufFinalStore` (`= betaEuf/SufFinalMemo`: `beta*FinalStore_eq`); `slhdsa_{suf,euf}_cma_final_store`
(explicit twelve-term RHS with `bTcrArA`; primed `∀`-forms), `slhdsa_pure_{suf,euf}_cma_final_store`,
`slhdsa_{bytes,pure_bytes}_{suf,euf}_cma_final_store`; 128s: `slhdsa_sha2_128s_{suf,euf,bytes_suf,pure_bytes_suf}_cma_final_store`.
## 4. Open program and count (`TcrStoreCount.lean`, `TcrStoreCover.lean`)
```lean
def memoImpl pk S : QueryImpl (Lazy.OSpec prims gspec) (OracleComp (Lazy.OSpec prims gspec))   -- thash query at pk found in S ↦ pure y (NO query); everything else forwarded
noncomputable def storeForgeOpen A L S pkSeed := simulateQ (memoImpl pkSeed S) (Resources2.memoForgeOpen A L pkSeed)
theorem bTcrArA_forge_open n A tbl L S pk : (liftM ((bTcrArA n A).forge (tbl, (L, S)) pk) : OracleComp (unifSpec + gspec) _) =   -- EVERY state, sound or not
    simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (storeForgeOpen A L S pk) >>= fun jm => pure (classOut prims n L jm)
def pinImpl tbl : QueryImpl OSpec (OracleComp OSpec)   -- sec i ↦ pure (tbl i); hash q ↦ query q >>= fun _ => pure (PublicHash.impl prims q); unif/game forwarded
theorem pinImpl_tbl tbl P : simulateQ (tblImpl (impl prims) tbl) (simulateQ (pinImpl tbl) P) = simulateQ (tblImpl (impl prims) tbl) P
abbrev NH pk S t := Lazy.kind t = .hash ∧ hitB pk S t = false                  -- a hash query not found in the store
theorem pin_memo_bound tbl pk S (hS : Sound pk S) P n : IsQueryBoundP (simulateQ (pinImpl tbl) P) (NH pk S) n → IsQueryBoundP (simulateQ (pinImpl tbl) (simulateQ (memoImpl pk S) P)) (kind = .hash) n
theorem storeForgeOpen_hashes_of_cover … (hS : Sound pk S) (hL : ∀ c ∈ L, (S.lookup c).isSome) (hKeygen : …NH… 0) (hSign : ∀ m root R, …NH… 1) : … ≤ qs + (1 + verifyHashes vp)
theorem cover_keygen tbl pk / cover_sign tbl pk m root R : IsQueryBoundP (simulateQ (pinImpl tbl) (Lazy.openKeygen … pk / Lazy.openSign … m pk root R)) (NH pk (ann … (honestCalls tbl pk))) 0 / 1
theorem storeForgeOpen_hashes A qs (hA : ∀ pk, IsQueryBoundP (A.main pk) (·.isRight = true) qs) tbl pk : IsQueryBoundP (simulateQ (pinImpl tbl)
  (storeForgeOpen A (honestCalls tbl pk) (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk)) pk)) (fun t => Lazy.kind t = .hash) (qs + (1 + Resources2.verifyHashes vp))
theorem storeForgeOpen_hashes_128s … : … (qs + 3929)   -- bTcrArM: 269824 + qs·2007385 + 7857;  bTcrArA_phase2_hashes: the bound at every z ∈ support (phase-1 run)
```
Closed form `qs + 1 + verifyHashes`, `verifyHashes = k·(1+a) + 1 + d·(len·(w-1) + 1 + h')` (3928 at 128s): one
`H_msg` per signing query, one for the forgery, the `Thash` calls of verifying the forgery. Not `2·verifyHashes`
(the comparison value of the collision test is a store hit); `PK.root` costs 0. Coverage (the proof W5 named
missing): `calls_authPathM` (auth path ⊆ subtree root), `calls_wotsSign`, `calls_xmssSign`, `calls_forsSign`,
`calls_signFromPos`; `wSign_subset`, `wRoot_subset` (⊆ `honestCalls tbl pk`, any digest/randomizer/root); `emb`
(writer monad → open programs), `pin_openKeygen_eq`, `pin_openSign_eq`.
## Deviations (stated plainly)
* **The count is for the PINNED program** `simulateQ (pinImpl tbl) (storeForgeOpen …)`, not for
  `storeForgeOpen …` under arbitrary oracle answers: `IsQueryBoundP` quantifies over all answers, and a
  lookup-with-fallback program fed wrong secret/hash answers asks for pairs that are not stored, so no bound
  better than the old one is TRUE there. Pinning = secrets from `tbl`, hash answers the real ones (every hash
  query still issued and counted); uniform bits and game answers stay arbitrary; `pinImpl_tbl`: same
  adversary. Holds for every `prims`; stated at the states phase 1 produces (`bTcrArA_phase2_hashes`).
* The closed second phase is `memoForge` over `withTH prims (lkT pk S) prims.Hmsg` (no new program text);
  `bTcrArA_forge_open` uses two kernel-checked `Eq.refl` steps (tactic `o9_kernel_rfl`: `memoForgeOpen`,
  `classOut` do not depend on `Thash`), as the sibling `Open/Tcr.lean` does. No axiom.
* Not counted / argued: the forger; `List.lookup` in `S`, `findIdx` in `L` (linear scans over `tcrTargets ≈
  2^79.81` entries; a keyed table in practice); secret reads (no new bound). Memory: `S` adds `tcrTargets`
  values of `Y` to the state `bTcrArM` already carries. Phase 1: same queries/targets as `bTcrArM`.
* Not done: linear-form and E2E restatements; EUF 128s byte-level instances; loose-cap twin headline.
Axioms: every `#print axioms` in the four files (11 + 13 + 6 + 11) gives `[propext, Classical.choice, Quot.sound]`
(`choose_couplingA`, `calls_authPathM`: `[propext, Quot.sound]`; `memoImpl`: `[propext]`).
