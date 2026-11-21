# ARITY — `VerifyAritySound` proved; the per-arity TCR split is unconditional

**Result: the split is now unconditional** (generic and at SLH-DSA-SHA2-128s). `VerifyAritySound`
is true exactly as B stated it, and is proved from `Structural vp prims` alone (already its
premise). No extra hypothesis: the arities `1, 2, len, k` need NOT be pairwise distinct, and no
address-type separation beyond `Structural.keyInj` is used. Nothing existing was edited.

## Files (both check with `lake env lean <File>.lean`; no warnings, no `sorry`/`axiom`/`native_decide`)

| file | lines | imports |
|---|---|---|
| `Reduction/VerifyArity.lean` | 448 | `Reduction.TcrSplitFinal` |
| `Reduction/TcrSplitClosed.lean` | 130 | `Reduction.VerifyArity` |

`.olean`s for both were written by hand into `.lake/build/lib/lean/Reduction/`. The lead must add
`import Reduction.VerifyArity` and `import Reduction.TcrSplitClosed` to `Reduction.lean`.
Every `#print axioms` shows `[propext, Classical.choice, Quot.sound]`. No scratch directory was
created; no subagents were used.

## `Reduction/VerifyArity.lean` — exact statements

```lean
def arityOf (vp : ValidatedParams) (a : Adrs) : ℕ :=      -- arity as a function of the ADDRESS
  if a.type = 0 then 1                                     -- WOTS_HASH  : F
  else if a.type = 1 then vp.params.len                    -- WOTS_PK    : T_len
  else if a.type = 2 then 2                                -- TREE       : H
  else if a.type = 3 then (if a.word2 = 0 then 1 else 2)   -- FORS_TREE  : F at height 0, else H
  else vp.params.k                                         -- FORS_ROOTS : T_k

theorem arityOf_mem_arities (a : Adrs) : ∃ i : Fin 4, arityOf vp a = arities vp i

def ArGood vp prims (S : List Adrs) (c : prims.AdrsKey × List prims.Y) : Prop :=
  ∃ a ∈ S, c.1 = prims.adrsToKey a ∧ c.2.length = arityOf vp a

-- honest structure: ordered (tweak, arity) trace = image of the explicit address list `mf_all vp`
theorem honestCalls_map_arity (tbl) (pk : prims.PkSeed) :
    (honestCalls tbl pk).map (arPi prims) = (mf_all vp).map (arF vp prims)
theorem honestCalls_arity (tbl) (pk : prims.PkSeed) :
    ∀ t ∈ honestCalls tbl pk, ArGood vp prims (mf_all vp) t

-- verification of an ARBITRARY signature under an ARBITRARY public key
theorem verifyCalls_arity (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    ∀ c ∈ verifyCalls pk msg sig, ArGood vp prims (mf_all vp) c

theorem mf_all_subset_ledger : ∀ a ∈ mf_all vp, a ∈ constructionAddresses vp

theorem verifyCalls_honestCalls_arity (hS : Structural vp prims) (tbl) (pkSeed : prims.PkSeed)
    (pk : PublicKeyCore prims.core) (msg) (sig) :
    ∀ c ∈ verifyCalls pk msg sig, ∀ t ∈ honestCalls tbl pkSeed,
      t.1 = c.1 → c.2.length = t.2.length ∧ ∃ i : Fin 4, t.2.length = arities vp i

theorem verifyAritySound : VerifyAritySound vp prims       -- B's named hypothesis, closed
```

`honestCalls_arity` and `verifyCalls_arity` need no hypothesis at all (not even `Structural`);
`hS` enters only through `keyInj`/`bounds` to turn "same tweak" into "same address".
`verifyCalls_honestCalls_arity` is slightly more general than `VerifyAritySound` (any public key,
not only `idealPk tbl pkSeed`).

Proof structure.
- Honest side: `ar_Tr` is `mf_Tr` of `TCR.lean` with an arbitrary projection (`arPi c =
  (c.1, c.2.length)`); the combinators and `ar_Tr_chain/wots/xmss/fors/all` are copies of the
  `mf_*` block with the arity recorded at each `logTh`. `ar_Tr_merkle` asks for the node callback
  only at heights `h + 1` (so the FORS node arity `2` is provable: height `0` is the `F` leaf).
- Verify side: in the writer monad `sub_W` via `sub_verifyCalls_eq`. New membership lemmas
  `ar_mem_chain` (calls of a chain segment are at hash addresses `< a + n`), `ar_mem_climb` (calls
  of `climbM` are node calls at heights `1 … auth.length` at the ancestors of `idx`), then
  `ar_wots`, `ar_xmss`, `ar_ht` (induction over `recoverFromPositionWith`), `ar_fors`. Signatures
  carry their FIPS shapes in their types (`Vector`s), digest parts / positions are `Fin`-bounded,
  `chainStepsCore_le` and `forsIdx_lt` bound the rest; membership in `mf_all` by the existing
  `mf_M_leaf_mem`/`mf_M_node_mem`.
- `mf_all vp ~ constructionAddresses vp` (existing `mf_ledger_subset`, `mf_all_length`, ledger
  `Nodup`) ⇒ `AddressFacts` ⇒ `hS.keyInj` gives equal addresses, hence equal `arityOf`.

Was `VerifyAritySound` false in any corner? No. The fallback `(0, [])` of `bTcr` is irrelevant at
the level of `stepTCR_split` (in the `tcr` class `findCollision` returns `some`), and coinciding
arity classes do not matter because the statement only asks for equal lengths lying in the list.

## `Reduction/TcrSplitClosed.lean` — exact statements

```lean
theorem stepTCR_split' (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2Class A .tcr) ≤ ∑ i, SM_DT_TCR_Advantage (bTcrAr (arities vp i) A)

theorem slhdsa_euf_cma_tcr_split' (hS : Structural vp prims) (A) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf vp prims).prfAdvantage (bPrf A) + (msgPrf vp prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) + tcrSplitSum A +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A))

theorem slhdsa_euf_cma_fors_tight_tcr_split' [Fintype prims.Y] (hS : Structural vp prims) (A) :
    … same with `OpenPRE(bOpenPre A)` replaced by
      (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPre A)) +
        3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPre A)))

-- SLH-DSA-SHA2-128s: no hypothesis except the forger
theorem verifyAritySound_128s : VerifyAritySound Link.vp Link.prims
theorem stepTCR_split_128s optRand pkSeedDist A : prTrue (g2Class A .tcr) ≤ ∑ i, …
theorem slhdsa_sha2_128s_euf_cma_tcr_split optRand pkSeedDist A : …
theorem slhdsa_sha2_128s_euf_cma_fors_tight_tcr_split optRand pkSeedDist A : …
theorem arities_injective_128s : Function.Injective (arities Link.vp)   -- 1, 2, 35, 14 distinct
```

The primed theorems are B's theorems applied to `verifyAritySound`; games (`thashArityProblem`),
adversaries (`bTcrAr n A`) and `tcrSplitSum` are B's, unchanged. No new game or adversary, so no
new non-vacuity lemma is needed (B's `thashArity_trivial_adv_zero`, `thashArityCollider_adv_one`,
`toy_thashArity` apply).

## Notes for integration

- For composition with A's lazy adversaries use B's `final_of_steps_tcr` with
  `h₆ := (stepTCR_split' hS A).trans (sum_arities_eq A).le`.
- Remaining differences from the paper are those listed in status/B.md and are untouched: FORS-tree
  and XMSS-tree `H` share the arity-2 term; an `F` (arity-1) term appears in the collision branch;
  every class game has cap `tcrTargets vp`; for parameter sets where two of `1, 2, len, k`
  coincide the coinciding terms are counted twice (not the case at 128s:
  `arities_injective_128s`).
- `honestCalls_map_arity` would support sharpening the per-class caps (count of `a ∈ mf_all vp`
  with `arityOf vp a = n`); not done here (done later: `arityTargets`, `HeadlineSplit.lean`; caps: `TightCaps.lean`).
