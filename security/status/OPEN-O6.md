# OPEN-O6 — phase-1 counts of `rUd` / `rPre` / `rTcr` / `rTcrT` at `Lazy.bWotsS A` as theorems

New files `Reduction/Open/WotsCounts.lean` (generic), `WotsCountsSM.lean` (collection queries),
`WotsCountsSamples.lean` (wrapper samples); oleans written; nothing existing touched; namespace
`Reduction.Open`.  ALL argued counts of the task are theorems now, with no `Structural` hypothesis.

## (a) Collection-oracle queries (style of `Resources2.UdChallengesLe`: predicates generic in `W`)
```lean
def UdCollectionLe (pkSeedDist) (W : WotsGame.Adversary prims) (n : ℕ) : Prop :=
  ∀ (world : SM_DT_UD_World) (pk : prims.PkSeed),
    ∀ z ∈ support ((simulateQ (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
      (rUd pkSeedDist W).pick).run ([], [])), z.2.2.length ≤ n
-- PreCollectionLe (rPre .. .choose in SM_DT_PRE_oracles (wotsPreProblem ..)), WTcrCollectionLe (rTcr,
-- wotsTcrProblem), WTcrTCollectionLe (rTcrT, wotsTcrProblemT): same shape, `∀ pk`.
theorem rUd_collection_le (A : Forger vp prims optRand pkSeedDist) : UdCollectionLe pkSeedDist
  (Lazy.bWotsS A) (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1)))
theorem rPre_collection_le (A) : PreCollectionLe pkSeedDist (Lazy.bWotsS A)  (same bound)
theorem rTcr_collection_le (A) : WTcrCollectionLe pkSeedDist (Lazy.bWotsS A)
  (wotsQc vp + (wotsInsts vp).length * vp.params.len)
theorem rTcrT_collection_le (A) : WTcrTCollectionLe pkSeedDist (Lazy.bWotsS A)  (same bound)
-- also r*_bWotsWith_collection_le (my) (A) at `Lazy.bWotsWith my A`; 128s (A : Forger Link.vp Link.prims ..):
theorem rUd_collection_le_128s / rPre_collection_le_128s : … 1062560399506556770327551
theorem rTcr_collection_le_128s / rTcrT_collection_le_128s : … 1058032102879147521492991
```
`z.2.2` is the game's own record: one entry per ANSWERED collection query (VCVio's
`collectionOracle` does not record a refused one).  `pkSeedDist` is the first explicit argument.  **qc**:
```lean
def forsC vp := vp.params.k * Lazy.merkleB 1 1 vp.params.a + 1     -- = k(2^(a+1)-1)+1 (forsC_eq)
def treeC vp := Lazy.merkleB 1 1 vp.params.hp                      -- = 2^(h'+1)-1     (treeC_eq)
def own vp l := if l = 0 then forsC vp else treeC vp
def wotsQc vp := ((wotsInsts vp).map fun a => own vp a.layer).sum + own vp vp.params.d
theorem wotsQc_closed vp : wotsQc vp + 2 ^ vp.params.h * treeC vp =
  2 ^ vp.params.h * forsC vp + ((wotsInsts vp).length + 1) * treeC vp   -- qc = 2^h·F + #trees·T
theorem wotsQc_128s : wotsQc Link.vp = 1057708653120046860861951   -- forsC 114675, treeC 1023
def WotsCollectionLe (W) (n) : Prop := ∀ (k : ℕ) (pk), ∀ z ∈ support ((simulateQ
  (wotsOraclesC k (wotsInsts vp) pk) W.choose).run ([], 0)), z.2.2 ≤ n
theorem bWotsS_collection_le (A) : WotsCollectionLe (Lazy.bWotsS A) (wotsQc vp)
theorem wotsOraclesC_proj k insts pk oa s : (fun z => (z.1, z.2.1)) <$>
  (simulateQ (wotsOraclesC k insts pk) oa).run s = (simulateQ (WotsGame.oracles k insts pk) oa).run s.1
```
`wotsOraclesC` = `WotsGame.oracles` with a counter bumped on EVERY collection query (the WOTS game
keeps no record).  **Deviation from the argued numerals**: W3/FINAL3 quote
`qc = 1057708653120046860862974`, UD/PRE `…328574`, TCR `…494014`; the proved values are each
`1023 = 2^(h'+1) - 1` SMALLER (the argued count had `(#trees + 1)·T`; the top tree is evaluated
once, for `PK.root`: `#trees·T`).  Proved UD/PRE bound `= tcrTargets Link.vp` (same numeral).

## (b) Wrapper samples (open-program style; for EVERY `W`, so in particular `Lazy.bWotsS A`)
The draws `monadLift ($ᵗ prims.Y)` in `udStart/preStart/tcrStart` are made queries of a one-point
oracle `sampSpec prims := Unit →ₒ prims.Y`; interface `unifSpec + (sampSpec prims + <game spec>)`;
`isSamp` = index `Sum.inr (Sum.inl _)`; `dropS` answers a sampling query by `$ᵗ prims.Y`, `embS`
embeds the old interface; `sampQ` = one sampling query.
```lean
noncomputable def rUdPickS (W) : OracleComp (UdSpecS pkSeedDist) (W.State × List (WotsGame.Entry prims))
  -- embS (monadLift ($ᵗ Fin (w-3+1))) >>= fun k => simChoose W (wotsInsts vp) (udStartS .. k.val) ..
noncomputable def rPreChooseS (W), rTcrChooseS (W)        -- simChoose with preStartS / tcrStartS
theorem rUd_pickS_interp (W) : simulateQ dropS (rUdPickS pkSeedDist W) = (rUd pkSeedDist W).pick
theorem rPre_chooseS_interp (W) : simulateQ dropS (rPreChooseS pkSeedDist W) = (rPre pkSeedDist W).choose
theorem rTcr_chooseS_interp / rTcrT_chooseS_interp (W) :
  simulateQ dropS (rTcrChooseS pkSeedDist W) = (rTcr pkSeedDist W).choose   / (rTcrT pkSeedDist W).choose
theorem rUd_wrapper_samples_le (W) : IsQueryBoundP (rUdPickS pkSeedDist W) isSamp
  ((wotsInsts vp).length * vp.params.len)
theorem rPre_wrapper_samples_le (W) : IsQueryBoundP (rPreChooseS pkSeedDist W) isSamp (same)
theorem rTcr_wrapper_samples_le / rTcrT_wrapper_samples_le (W) : IsQueryBoundP (rTcrChooseS ..) isSamp (same)
theorem wrapper_samples_128s : (wotsInsts Link.vp).length * Link.vp.params.len = 323449759100660631040
```
`IsQueryBoundP` = on every path, whatever the oracles answer.  Deviations: (i) `rTcr`: "exactly one
value per chain of a signed instance" is proved as `≤ #inst·len` only (no exact count);
(ii) `rUd`'s hybrid index is the first step of `rUdPickS` (a lifted `$ᵗ (Fin (w - 3 + 1))`, by
definition; `isSamp` counts `prims.Y` values only); (iii) the samples of `W` itself stay uniform
queries, not sampling queries (for `bWotsS A`: `Lazy.bWotsS_choose_eq`, exactly `2^h·k·2^a`).

## Method (reusable)
`growth_of_qb` (`IsQueryBoundP` + per-query growth ≤ 1 of a counter on the oracle state ⇒ growth
≤ N per run); `CSem`, `CSem.bWotsWith_choose_count` (counter growth `≤ cC·wotsQc vp + #inst·K`: the
memoisation argument as a potential over signed instances); `simChoose_bWotsWith_count` (instance
for `simChoose` in any SM game); `signProg_qb`; samples: `fuse`, `simChooseS_interp/_samples`.

## Check / axioms
`lake env lean Reduction/Open/WotsCounts{,SM,Samples}.lean`: no error (only `if_pos` deprecation
warnings); all 24 `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.
