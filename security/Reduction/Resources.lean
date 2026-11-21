import Reduction.Instance128s

/-!
# Resource accounting for the reduction adversaries

Everything here is a corollary of existing lemmas; no adversary and no game is defined.

* **(A) Closed forms** of the symbolic quantities that the per-adversary count lemmas are stated
  in (`openPreTargets`, `wotsChainTargets`, `wotsStepTargets`, `tcrTargets`, the lengths of
  `forsLeafAddresses`, `wotsInsts`, `allXmssTrees`, `allBottomPositions`, `signReads`), and their
  values at SLH-DSA-SHA2-128s (`Link.vp`: `h = 63`, `d = 7`, `h' = 9`, `a = 12`, `k = 14`,
  `w = 16`, `len = 35`).  Each numeral is obtained by first proving the closed form for every
  parameter set and then evaluating it (`rfl`/`decide`/`norm_num`; no `native_decide`).

* **(B) The three WOTS adversaries** `rUd`, `rPre`, `rTcr`: per-run bounds on the number of
  challenge/target queries, for EVERY `W : WotsGame.Adversary prims`.

* **(C) Hash-evaluation count of one evaluation of the key structure**: `structHashEvals`,
  `structPrfEvals`.  These are counts of a closed-form expression (tied to the length of the
  ledger `constructionAddresses`), NOT theorems about the running time of a program.

## What the statements in (B) are, exactly

For each of the three games the statement is about the game's own bookkeeping: the first
component of the game state (`SM_DT_UD_State`, `SM_DT_PRE_State`, `SM_DT_TCR_State`) is the list
of ACCEPTED challenge/target queries, and the theorems say that in every reachable final state of
phase 1 (`∀ z ∈ support (… .run ([], []))`, for every value `pk` of the seed and, for SM-UD, in
both worlds) this list is no longer than the stated closed form.  They are per-run facts
(support statements), not game caps.  The game cap is the field `numTargets` of the problem
(`wotsChainTargets vp` for SM-UD/SM-PRE, `wotsStepTargets vp` for SM-TCR); `*_le_cap` compare the
two.  For SM-TCR the per-run bound `#inst·len·(w-1)` is strictly below the cap `#inst·len·w`
(a chain has `w - 1` steps; the cap keeps the literature's `w`; the game with cap
`#inst·len·(w-1)` and equal advantage is `wotsTcrProblemT`, `Reduction/TightCaps.lean`).

That no challenge query is REFUSED by the game (so "accepted" = "asked") is not a separate lemma:
it is part of the existing step lemmas `ud_hsign`, `pre_hsign`, `tcr_hsign` (through `udChal_run`,
`preChal_run`, `wtcrChal_run`, whose hypotheses `qs.length < numTargets` and `TweakFresh` are
discharged from the invariant), and it is what makes the simulation equal to the hybrid in
distribution.  It is not restated here.

Hypotheses: `Structural vp prims` only (injective address encoding; proved at 128s).  NO
hypothesis on `W`: `simSignOracle` refuses a signing query locally (without any game query) unless
its instance is in `wotsInsts vp` and has not been signed before, so at most `#inst` signing
queries of `W` reach the game, however many `W` makes.

What is NOT bounded for arbitrary `W` (and cannot be):
* the number of COLLECTION queries of `rUd`/`rPre`/`rTcr`.  Every non-reserved collection query of
  `W` is forwarded one-to-one (`simCollOracle`), so a bound needs a bound `qc` on `W`'s collection
  queries.  With such a bound the counts are (by inspection of `udStart`, `preStart`, `tcrStart`
  and `wotsPkFromSigTopsWith`; not formalised):
  - `rUd`:  `≤ qc + #inst·len·(w-1)`  (per chain with digit `b`: `b - udPos k b` steps for the
    revealed value, then `w-1-b` steps to the chain end; at most `w - 1` together);
  - `rPre`: `≤ qc + #inst·len·(w-1)`  (per chain: `w-1-b` steps to the chain end);
  - `rTcr`: `≤ qc + #inst·len`        (per chain with `b ≠ 0`: the one hidden step `b-1`; the
    steps `b … w-2` are TARGET queries, counted by `rTcr_targets_le`).
* the number of uniform samples.  `W`'s own `unifSpec` queries are forwarded unchanged.  The
  adversaries' OWN draws are, by inspection of the definitions (not formalised, because a draw
  `$ᵗ prims.Y` is a `ProbComp` whose number of underlying `unifSpec` queries depends on the
  `SampleableType` instance):
  - `rUd`:  one draw of the hybrid index from `Fin (w - 2)` (written `Fin (w - 3 + 1)`), and one
    `$ᵗ prims.Y` per chain of a signed instance that is NOT challenged, i.e. with
    `¬ (k + 1 < b)`: at most `#inst·len` draws of `Y`;
  - `rPre`: one `$ᵗ prims.Y` per chain with digit `b = 0`: at most `#inst·len`;
  - `rTcr`: exactly one `$ᵗ prims.Y` per chain of a signed instance: at most `#inst·len`, with
    equality iff all `#inst` instances are signed.
  In phase 2 (`distinguish`/`invert`/`forge`) the three adversaries draw nothing themselves; they
  run `W.forge` once and then compute `WotsGame.win` / `preAnswer` / `tcrAnswer`, which evaluate
  at most `len·(w-1)` (`win`, `preAnswer`) resp. `len·(w-1)·2(w-1)` (`tcrAnswer`, two chain
  recomputations per candidate step) hashes of ONE instance, locally and with the revealed seed.

So with `W = bWots A`: all three make at most `#inst·len` (resp. `#inst·len·(w-1)`) game queries
whatever the forger does, but their total work is at least that of `bWots A`, which signs every
WOTS+ instance of the hypertree (`2^63.003` instances at 128s).  (Later,
`Reduction/Resources2Wots.lean`: at `W = Lazy.bWotsS A` the phase-2 hash evaluations of the three
are formally `≤ qs·wotsSignHistHashes + O(len·w²)`; the collection-query and own-sample counts
above remain counting arguments.)

## (C) Counting local computation in VCVio

VCVio has cost machinery, all under `VCVio/OracleComp/QueryTracking/`:
`CostModel.lean` (`CostModel spec ω`, `costDist`, `WorstCaseCostBound`, `expectedCost`),
`WriterCost.lean` / `QueryCost.lean` (`QueryImpl.withAddCost`, `withUnitCost`, `UsesAtMostQueries`,
`PathwiseCostAtMost`), `QueryBound/*.lean` (`IsQueryBound`, `IsQueryBoundP`, `IsTotalQueryBound`),
`ExpectedQueryCount.lean`, `DeterminedCost.lean` and `MeasuredProgram.lean`
(`MeasuredProgram`, `Realizes`, `CostAtMost`, `BudgetedProgram`).
ALL of it charges declared ORACLE QUERIES only.  Pure Lean code between queries is free; the
module docs say so explicitly (`MeasuredProgram.lean`: "Only the declared instructions are
charged … pure Lean code between instructions … are not", "every function has a budgeted program
with budget zero"; `DeterminedCost.lean`: "A bound on declared query costs does not account for
computation inside the handler").  Hence for an adversary `OracleComp spec α` that computes
`prims.Thash` as a pure function nothing in VCVio can state "evaluates `Thash` at most `N` times":
the evaluations are invisible in the term.  The only way is the one `Reduction/Lazy/Core.lean`
already takes — re-express the adversary as a program over an extended spec in which each hash
evaluation is a query (`hspec`), interpret that oracle deterministically (`QueryImpl hspec Id`),
prove the interpreted program equal to the original, and count the `hspec` queries.  VCVio's
`MeasuredProgram` + `WorstCaseCostBound` + `QueryImpl.run_simulateQ_withAddCost_id` is the same
idea packaged for deterministic FUNCTIONS (input ↦ result, handlers in `Id`); it is not better
for our purpose, since our adversaries are probabilistic and interactive, where `IsQueryBoundP`
on the `hspec` component (a predicate on query indices) is the natural statement.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction
namespace Resources

/-! ## (A) Closed forms, generic in the parameter set -/

/-- Number of WOTS+ instances, layer by layer from the bottom: layer `j` has `2^(h - j·h')`. -/
def wotsInstances (p : Params) : ℕ := ∑ j ∈ Finset.range p.d, 2 ^ (p.h - j * p.hp)

/-- VCVio's `wotsInstanceCount` is `Σ_{j<d} 2^(h - j·h')`. -/
theorem wotsInstanceCount_eq_sum (p : Params) (hv : p.Valid) :
    wotsInstanceCount p = wotsInstances p := by
  rw [wotsInstanceCount_eq_xmssTreeCount_mul, xmssTreeCount_eq_geomSum, Finset.sum_mul,
    wotsInstances, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← pow_mul, ← pow_add, hv.h_eq_layers]
  congr 1
  have h1 : (p.d - 1 - i) * p.hp + (i + 1) * p.hp = p.d * p.hp := by
    rw [← Nat.add_mul]; congr 1; omega
  have h2 : (p.d - 1 - i) * p.hp ≤ p.d * p.hp := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_comm p.hp (p.d - 1 - i)]
  have h3 : (i + 1) * p.hp = i * p.hp + p.hp := Nat.succ_mul _ _
  omega

/-- Division-free closed form: `#inst · (2^h' - 1) = (2^h - 1) · 2^h'`. -/
theorem wotsInstanceCount_mul_pred (p : Params) (hv : p.Valid) :
    wotsInstanceCount p * (2 ^ p.hp - 1) = (2 ^ p.h - 1) * 2 ^ p.hp := by
  rw [wotsInstanceCount_eq_xmssTreeCount_mul, Nat.mul_right_comm, xmssTreeCount_mul_pred p hv]

variable (vp : ValidatedParams)

/-- `2^h` bottom positions (= FORS instances). -/
theorem allBottomPositions_length_eq : (allBottomPositions vp).length = 2 ^ vp.params.h :=
  allBottomPositions_length vp

/-- `Σ_{i<d} 2^(h'·i)` XMSS trees; `(allXmssTrees vp).length · (2^h' - 1) = 2^h - 1`. -/
theorem allXmssTrees_length_eq :
    (allXmssTrees vp).length = ∑ i ∈ Finset.range vp.params.d, (2 ^ vp.params.hp) ^ i := by
  rw [allXmssTrees_length, xmssTreeCount_eq_geomSum]

theorem allXmssTrees_length_mul_pred :
    (allXmssTrees vp).length * (2 ^ vp.params.hp - 1) = 2 ^ vp.params.h - 1 := by
  rw [allXmssTrees_length, xmssTreeCount_mul_pred _ vp.valid]

/-- The allowed instances of the WOTS game are counted by `wotsInstanceCount`. -/
theorem wotsInsts_length : (wotsInsts vp).length = wotsInstanceCount vp.params := by
  simp [wotsInsts]

/-- `#inst = Σ_{j<d} 2^(h - j·h')`. -/
theorem wotsInsts_length_eq_sum :
    (wotsInsts vp).length = ∑ j ∈ Finset.range vp.params.d, 2 ^ (vp.params.h - j * vp.params.hp) :=
  (wotsInsts_length vp).trans (wotsInstanceCount_eq_sum _ vp.valid)

/-- `#inst = #trees · 2^h'`. -/
theorem wotsInsts_length_eq_trees :
    (wotsInsts vp).length = (allXmssTrees vp).length * 2 ^ vp.params.hp := by
  rw [wotsInsts_length, allXmssTrees_length, wotsInstanceCount_eq_xmssTreeCount_mul]

/-- `2^h · k · 2^a` FORS leaves. -/
theorem forsLeafAddresses_length_eq :
    (forsLeafAddresses vp).length = 2 ^ vp.params.h * vp.params.k * 2 ^ vp.params.a :=
  forsLeafAddresses_length vp

theorem openPreTargets_eq :
    openPreTargets vp = 2 ^ vp.params.h * vp.params.k * 2 ^ vp.params.a := rfl

theorem openPreTargets_eq_length : openPreTargets vp = (forsLeafAddresses vp).length :=
  (forsLeafAddresses_length vp).symm

/-- SM-UD / SM-PRE cap: `#inst · len`. -/
theorem wotsChainTargets_eq :
    wotsChainTargets vp = (wotsInsts vp).length * vp.params.len := by
  rw [wotsInsts_length]; rfl

/-- SM-TCR(F) cap: `#inst · len · w` (with `w`, NOT `w - 1`: VCVio's `targetCount .wotsFTcr`
keeps the literature's looser cap; only `w - 1` steps per chain exist). -/
theorem wotsStepTargets_eq :
    wotsStepTargets vp = (wotsInsts vp).length * vp.params.len * vp.params.w := by
  rw [wotsInsts_length]; rfl

theorem wotsStepTargets_eq_chain : wotsStepTargets vp = wotsChainTargets vp * vp.params.w := rfl

/-- **Closed form of `tcrTargets`**: FORS leaves + FORS nodes + FORS roots + executed WOTS+ chain
steps + WOTS+ public-key compressions + XMSS nodes. -/
theorem tcrTargets_eq :
    tcrTargets vp =
      2 ^ vp.params.h * vp.params.k * 2 ^ vp.params.a +
      2 ^ vp.params.h * vp.params.k * (2 ^ vp.params.a - 1) +
      2 ^ vp.params.h +
      (wotsInsts vp).length * vp.params.len * (vp.params.w - 1) +
      (wotsInsts vp).length +
      (2 ^ vp.params.h - 1) := by
  rw [tcrTargets, constructionAddresses_length, targetCount_xmssH_eq _ vp.valid, wotsInsts_length]
  rfl

/-- The same, grouped per FORS instance and per WOTS+ instance. -/
theorem tcrTargets_eq' :
    tcrTargets vp =
      2 ^ vp.params.h * (vp.params.k * (2 ^ (vp.params.a + 1) - 1) + 1) +
      (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1) + 1) +
      (2 ^ vp.params.h - 1) := by
  have h1 : 2 ^ (vp.params.a + 1) - 1 = 2 ^ vp.params.a + (2 ^ vp.params.a - 1) := by
    have := Nat.one_le_two_pow (n := vp.params.a)
    rw [pow_succ]; omega
  rw [tcrTargets_eq, h1]
  ring

theorem signReads_eq :
    signReads vp =
      vp.params.k * 2 ^ vp.params.a + vp.params.d * (2 ^ vp.params.hp * vp.params.len) := rfl

/-! ## (C) Hash evaluations of one evaluation of the whole key structure

Counting argument (FIPS 205 Alg. 5–8, 14–16; `Thash` = any of `F`, `H`, `T_len`, `T_k`):

* one FORS instance (there are `2^h`, one per bottom position): `k` trees, each with `2^a` leaves
  (`F`) and `2^a - 1` internal nodes (`H`), and one root compression (`T_k`):
  `k·(2^(a+1) - 1) + 1` evaluations;
* one WOTS+ instance (there are `#inst = Σ_{j<d} 2^(h - j·h')`): `len` chains of `w - 1` steps
  (`F`) and one public-key compression (`T_len`): `len·(w - 1) + 1` evaluations;
* XMSS internal nodes (`H`): `2^h' - 1` per tree, `2^h - 1` over all trees;
* secret values (`PRF`, not `Thash`): one per FORS leaf and one per WOTS+ chain.

`structHashEvals` and `structPrfEvals` are these closed forms.  `structHashEvals_eq_tcrTargets`
ties the first to the length of the duplicate-free ledger `constructionAddresses` of all honest
`Thash` calls.  They are NOT statements about a program: no adversary in this development is
proved to make this many (or this few) hash evaluations. -/

/-- `Thash` evaluations of one evaluation of the key structure (closed form). -/
def structHashEvals (p : Params) : ℕ :=
  2 ^ p.h * (p.k * (2 ^ (p.a + 1) - 1) + 1) +
    wotsInstances p * (p.len * (p.w - 1) + 1) + (2 ^ p.h - 1)

/-- `PRF` evaluations (secret values) of one evaluation of the key structure (closed form). -/
def structPrfEvals (p : Params) : ℕ :=
  2 ^ p.h * p.k * 2 ^ p.a + wotsInstances p * p.len

/-- The closed form counts exactly the entries of the union ledger of honest `Thash` calls. -/
theorem structHashEvals_eq_tcrTargets : structHashEvals vp.params = tcrTargets vp := by
  rw [tcrTargets_eq', wotsInsts_length, wotsInstanceCount_eq_sum _ vp.valid]; rfl

theorem structPrfEvals_eq :
    structPrfEvals vp.params = openPreTargets vp + wotsChainTargets vp := by
  rw [wotsChainTargets_eq, wotsInsts_length, wotsInstanceCount_eq_sum _ vp.valid]; rfl

/-! ## (A) Numerals at SLH-DSA-SHA2-128s -/

section S128

/-- The parameters of `Link.vp`. -/
theorem params_128s :
    Link.vp.params.n = 16 ∧ Link.vp.params.h = 63 ∧ Link.vp.params.d = 7 ∧
    Link.vp.params.hp = 9 ∧ Link.vp.params.a = 12 ∧ Link.vp.params.k = 14 ∧
    Link.vp.params.w = 16 ∧ Link.vp.params.len = 35 ∧ Link.vp.params.m = 30 := by decide

theorem xmssTreeCount_128s : xmssTreeCount Link.vp.params = 18049651735527937 := by
  rw [xmssTreeCount_eq_geomSum]
  show ∑ i ∈ Finset.range 7, (2 ^ 9) ^ i = _
  simp [Finset.sum_range_succ]

theorem wotsInstanceCount_128s : wotsInstanceCount Link.vp.params = 9241421688590303744 := by
  rw [wotsInstanceCount_eq_xmssTreeCount_mul, xmssTreeCount_128s]
  decide

/-- `2^63` bottom positions. -/
theorem allBottomPositions_length_128s : (allBottomPositions Link.vp).length = 2 ^ 63 :=
  allBottomPositions_length Link.vp

/-- `(2^63 - 1)/511 = 18049651735527937 ≈ 2^54.003` XMSS trees. -/
theorem allXmssTrees_length_128s : (allXmssTrees Link.vp).length = 18049651735527937 :=
  (allXmssTrees_length Link.vp).trans xmssTreeCount_128s

theorem allXmssTrees_length_128s_bounds :
    2 ^ 54 < (allXmssTrees Link.vp).length ∧ (allXmssTrees Link.vp).length < 2 ^ 55 := by
  rw [allXmssTrees_length_128s]; decide

/-- `2^63 + 2^54 + 2^45 + 2^36 + 2^27 + 2^18 + 2^9 = 9241421688590303744 ≈ 2^63.003` WOTS+
instances. -/
theorem wotsInsts_length_128s : (wotsInsts Link.vp).length = 9241421688590303744 :=
  (wotsInsts_length Link.vp).trans wotsInstanceCount_128s

theorem wotsInsts_length_128s_sum :
    (wotsInsts Link.vp).length = 2 ^ 63 + 2 ^ 54 + 2 ^ 45 + 2 ^ 36 + 2 ^ 27 + 2 ^ 18 + 2 ^ 9 := by
  rw [wotsInsts_length_128s]; decide

theorem wotsInsts_length_128s_bounds :
    2 ^ 63 < (wotsInsts Link.vp).length ∧ (wotsInsts Link.vp).length < 2 ^ 64 := by
  rw [wotsInsts_length_128s]; decide

/-- `2^63 · 14 · 2^12 = 14 · 2^75 ≈ 2^78.81` FORS leaves. -/
theorem openPreTargets_128s : openPreTargets Link.vp = 2 ^ 63 * 14 * 2 ^ 12 := rfl

theorem openPreTargets_128s_val : openPreTargets Link.vp = 528905046081400263933952 := by decide

theorem openPreTargets_128s_bounds :
    2 ^ 78 < openPreTargets Link.vp ∧ openPreTargets Link.vp < 2 ^ 79 := by decide

theorem forsLeafAddresses_length_128s :
    (forsLeafAddresses Link.vp).length = 2 ^ 63 * 14 * 2 ^ 12 :=
  forsLeafAddresses_length Link.vp

/-- `#inst · 35 ≈ 2^68.13`. -/
theorem wotsChainTargets_128s : wotsChainTargets Link.vp = 9241421688590303744 * 35 := by
  rw [wotsChainTargets_eq, wotsInsts_length_128s]; rfl

theorem wotsChainTargets_128s_val : wotsChainTargets Link.vp = 323449759100660631040 := by
  rw [wotsChainTargets_128s]

theorem wotsChainTargets_128s_bounds :
    2 ^ 68 < wotsChainTargets Link.vp ∧ wotsChainTargets Link.vp < 2 ^ 69 := by
  rw [wotsChainTargets_128s]; decide

/-- `#inst · 35 · 16 ≈ 2^72.13` (the cap; with `w = 16`). -/
theorem wotsStepTargets_128s : wotsStepTargets Link.vp = 9241421688590303744 * 35 * 16 := by
  rw [wotsStepTargets_eq, wotsInsts_length_128s]; rfl

theorem wotsStepTargets_128s_val : wotsStepTargets Link.vp = 5175196145610570096640 := by
  rw [wotsStepTargets_128s]

theorem wotsStepTargets_128s_bounds :
    2 ^ 72 < wotsStepTargets Link.vp ∧ wotsStepTargets Link.vp < 2 ^ 73 := by
  rw [wotsStepTargets_128s]; decide

/-- Executed chain steps, the per-run bound of `rTcr`: `#inst · 35 · 15 ≈ 2^72.04`. -/
theorem wotsExecutedSteps_128s :
    (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1)) =
      4851746386509909465600 := by
  rw [wotsInsts_length_128s]; decide

/-- `tcrTargets` at 128s, component by component. -/
theorem tcrTargets_128s :
    tcrTargets Link.vp =
      2 ^ 63 * 14 * 2 ^ 12 + 2 ^ 63 * 14 * (2 ^ 12 - 1) + 2 ^ 63 +
        9241421688590303744 * 35 * 15 + 9241421688590303744 + (2 ^ 63 - 1) := by
  rw [tcrTargets_eq, wotsInsts_length_128s]; rfl

/-- `tcrTargets ≈ 2^79.81` at 128s. -/
theorem tcrTargets_128s_val : tcrTargets Link.vp = 1062560399506556770327551 := by
  rw [tcrTargets_128s]; decide

theorem tcrTargets_128s_bounds :
    2 ^ 79 < tcrTargets Link.vp ∧ tcrTargets Link.vp < 2 ^ 80 := by
  rw [tcrTargets_128s]; decide

/-- Secret values read by one signature at 128s: `14·2^12 + 7·(2^9·35)`. -/
theorem signReads_128s : signReads Link.vp = 182784 := by decide

/-- Secret values read by key generation at 128s: `2^9 · 35`. -/
theorem keygenReads_128s : 2 ^ Link.vp.params.hp * Link.vp.params.len = 17920 := by decide

/-- `Thash` evaluations of one key-structure evaluation at 128s (closed form): `≈ 2^79.81`. -/
theorem structHashEvals_128s : structHashEvals Link.vp.params = 1062560399506556770327551 :=
  (structHashEvals_eq_tcrTargets Link.vp).trans tcrTargets_128s_val

theorem structHashEvals_128s_bounds :
    2 ^ 79 < structHashEvals Link.vp.params ∧ structHashEvals Link.vp.params < 2 ^ 80 := by
  rw [structHashEvals_128s]; decide

/-- `PRF` evaluations of one key-structure evaluation at 128s (closed form): `≈ 2^78.81`. -/
theorem structPrfEvals_128s : structPrfEvals Link.vp.params = 529228495840500924564992 := by
  rw [structPrfEvals_eq, openPreTargets_128s_val, wotsChainTargets_128s_val]

end S128

/-! ## (B) Challenge/target counts of `rUd`, `rPre`, `rTcr` -/

section Wots

set_option linter.unusedSectionVars false

variable {vp} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

open WotsFinal WotsUD

/-- A duplicate-free signing history over allowed instances has at most `#inst` entries. -/
theorem hist_length_le {hist : List (WotsGame.Entry prims)} (hnodup : (hist.map (·.1)).Nodup)
    (hmem : ∀ e ∈ hist, e.1 ∈ wotsInsts vp) : hist.length ≤ (wotsInsts vp).length := by
  have h2 : hist.map (·.1) ⊆ wotsInsts vp := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hmem e he
  simpa using (List.subperm_of_subset hnodup h2).length_le

variable (pkSeedDist : ProbComp prims.PkSeed)

/-- **`rUd`, hybrid index fixed.**  In every run of phase 1 against the SM-UD oracles (either
world, any seed, any `W`), the mirrored history has at most `#inst` entries and the game has
accepted at most `#inst · len` challenges. -/
theorem udFixed_challenges_le (hS : Structural vp prims) (world : SM_DT_UD_World) (k : ℕ)
    (W : WotsGame.Adversary prims) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (outer (udO₂ pkSeedDist world pk))
        (WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist k) (udChainHash pkSeedDist)
          (udColl pkSeedDist))).run ([], [])),
      z.1.2.length ≤ (wotsInsts vp).length ∧
        z.2.1.length ≤ (wotsInsts vp).length * vp.params.len := by
  intro z hz
  have hI : UdInv k z.1.2 z.2 :=
    (nested_run _ (outer (udO₂ pkSeedDist world pk))
      (WotsGame.oracles (hidx world k) (wotsInsts vp) pk) (UdInv k)
      (WotsFinal.sim_step (udO₂ pkSeedDist world pk) (hidx world k) (wotsInsts vp) pk
        (udStart pkSeedDist k) (udChainHash pkSeedDist) (udColl pkSeedDist) (UdInv k)
        (ud_hcoll pkSeedDist world k pk) (ud_hsign pkSeedDist hS world k pk)) W.choose [] ([], [])
      ⟨by simp, by simp, by simp, by simp, by simp⟩).2 z hz
  have hl := hist_length_le hI.nodup hI.mem
  exact ⟨hl, hI.len.trans (Nat.mul_le_mul_right _ hl)⟩

/-- **`rUd`.**  In every run of `(rUd pkSeedDist W).pick` inside the SM-UD game (either world,
any seed, any `W`), the game has accepted at most `#inst · len` challenges. -/
theorem rUd_challenges_le (hS : Structural vp prims) (world : SM_DT_UD_World)
    (W : WotsGame.Adversary prims) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
        (rUd pkSeedDist W).pick).run ([], [])),
      z.1.2.length ≤ (wotsInsts vp).length ∧
        z.2.1.length ≤ (wotsInsts vp).length * vp.params.len := by
  have h1 : (simulateQ (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
        (rUd pkSeedDist W).pick).run ([], []) =
      (($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp _) >>= fun kf =>
        (simulateQ (outer (udO₂ pkSeedDist world pk))
          (WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist kf.val)
            (udChainHash pkSeedDist) (udColl pkSeedDist))).run ([], [])) := by
    show (simulateQ (outer (udO₂ pkSeedDist world pk))
      ((monadLift ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp (Fin (vp.params.w - 3 + 1))) :
        OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) _) >>= fun kf =>
          WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist kf.val)
            (udChainHash pkSeedDist) (udColl pkSeedDist))).run ([], []) = _
    rw [simulateQ_bind, StateT.run_bind, outer_lift, bind_map_left]
  intro z hz
  rw [h1] at hz
  obtain ⟨kf, -, hz⟩ := (mem_support_bind_iff ..).mp hz
  exact udFixed_challenges_le pkSeedDist hS world kf.val W pk z hz

/-- The per-run bound of `rUd` is the cap of its game. -/
theorem rUd_challenges_le_cap (hS : Structural vp prims) (world : SM_DT_UD_World)
    (W : WotsGame.Adversary prims) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
        (rUd pkSeedDist W).pick).run ([], [])),
      z.2.1.length ≤ (wotsUdProblem vp prims pkSeedDist).numTargets := fun z hz =>
  ((rUd_challenges_le pkSeedDist hS world W pk z hz).2).trans (wotsChainTargets_eq vp).ge

/-- **`rPre`.**  In every run of `(rPre pkSeedDist W).choose` inside the SM-PRE game (any seed,
any `W`), the history has at most `#inst` entries and the game has accepted at most
`#inst · len` challenges; exactly one per chain with nonzero digit of a signed instance. -/
theorem rPre_challenges_le (hS : Structural vp prims) (W : WotsGame.Adversary prims)
    (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_PRE_oracles (wotsPreProblem vp prims pkSeedDist) pk)
        (rPre pkSeedDist W).choose).run ([], [])),
      z.1.2.length ≤ (wotsInsts vp).length ∧
        z.2.1.length = (z.1.2.map fun e => preCount e.2.1 vp.params.len).sum ∧
        z.2.1.length ≤ (wotsInsts vp).length * vp.params.len := by
  intro z hz
  have hI : PreInv pk z.1.2 z.2 :=
    (nested_run _ (outer (preO₂ pkSeedDist pk))
      (WotsGame.oracles (vp.params.w - 2) (wotsInsts vp) pk) (PreInv pk)
      (WotsFinal.sim_step (preO₂ pkSeedDist pk) (vp.params.w - 2) (wotsInsts vp) pk
        (preStart pkSeedDist) (preChainHash pkSeedDist) (preColl pkSeedDist) (PreInv pk)
        (pre_hcoll pkSeedDist pk) (pre_hsign pkSeedDist hS pk)) W.choose [] ([], [])
      ⟨by simp, by simp, by simp, by simp, by intro j e h; simp at h, by simp, by simp⟩).2 z hz
  have hl := hist_length_le hI.nodup hI.mem
  refine ⟨hl, hI.len, ?_⟩
  rw [hI.len]
  exact (sum_preCount_le _).trans (Nat.mul_le_mul_right _ hl)

/-- The per-run bound of `rPre` is the cap of its game. -/
theorem rPre_challenges_le_cap (hS : Structural vp prims) (W : WotsGame.Adversary prims)
    (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_PRE_oracles (wotsPreProblem vp prims pkSeedDist) pk)
        (rPre pkSeedDist W).choose).run ([], [])),
      z.2.1.length ≤ (wotsPreProblem vp prims pkSeedDist).numTargets := fun z hz =>
  ((rPre_challenges_le pkSeedDist hS W pk z hz).2.2).trans (wotsChainTargets_eq vp).ge

/-- **`rTcr`.**  In every run of `(rTcr pkSeedDist W).choose` inside the SM-TCR game (any seed,
any `W`), the history has at most `#inst` entries and the game has accepted at most
`#inst · len · (w - 1)` targets; exactly `w - 1 - b` per chain with digit `b` of a signed
instance. -/
theorem rTcr_targets_le (hS : Structural vp prims) (W : WotsGame.Adversary prims)
    (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
        (rTcr pkSeedDist W).choose).run ([], [])),
      z.1.2.length ≤ (wotsInsts vp).length ∧
        z.2.1.length = (z.1.2.map fun e => tcrCount (vp := vp) e.2.1 vp.params.len).sum ∧
        z.2.1.length ≤ (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1)) := by
  intro z hz
  have hI : TcrInv pk z.1.2 z.2 :=
    (nested_run _ (outer (tcrO₂ pkSeedDist pk))
      (WotsGame.oracles (vp.params.w - 2) (wotsInsts vp) pk) (TcrInv pk)
      (WotsFinal.sim_step (tcrO₂ pkSeedDist pk) (vp.params.w - 2) (wotsInsts vp) pk
        (tcrStart pkSeedDist) (tcrChainHash pkSeedDist) (wtcrColl pkSeedDist) (TcrInv pk)
        (tcr_hcoll pkSeedDist pk) (tcr_hsign pkSeedDist hS pk)) W.choose [] ([], [])
      ⟨by simp, by simp, by simp, by simp, by intro j e h; simp at h, by simp, by simp⟩).2 z hz
  have hl := hist_length_le hI.nodup hI.mem
  refine ⟨hl, hI.len, ?_⟩
  rw [hI.len]
  exact (sum_tcrCount_le _).trans (Nat.mul_le_mul_right _ hl)

/-- The per-run bound of `rTcr` is below the cap of its game (`w - 1` versus `w` per chain). -/
theorem rTcr_targets_le_cap (hS : Structural vp prims) (W : WotsGame.Adversary prims)
    (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
        (rTcr pkSeedDist W).choose).run ([], [])),
      z.2.1.length ≤ (wotsTcrProblem vp prims pkSeedDist).numTargets := by
  intro z hz
  refine ((rTcr_targets_le pkSeedDist hS W pk z hz).2.2).trans ?_
  show _ ≤ wotsStepTargets vp
  rw [wotsStepTargets_eq, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

end Wots

/-! ## (B) at SLH-DSA-SHA2-128s -/

section Wots128

variable (pkSeedDist : ProbComp Link.prims.PkSeed)

/-- `rUd` at 128s: at most `323449759100660631040 < 2^69` challenges in every run. -/
theorem rUd_challenges_128s (world : SM_DT_UD_World) (W : WotsGame.Adversary Link.prims)
    (pk : Link.prims.PkSeed) :
    ∀ z ∈ support ((simulateQ
        (SM_DT_UD_oracles world (wotsUdProblem Link.vp Link.prims pkSeedDist) pk)
        (rUd pkSeedDist W).pick).run ([], [])),
      z.2.1.length ≤ 323449759100660631040 := fun z hz =>
  (rUd_challenges_le_cap pkSeedDist structural_128s world W pk z hz).trans
    wotsChainTargets_128s_val.le

/-- `rPre` at 128s: at most `323449759100660631040 < 2^69` challenges in every run. -/
theorem rPre_challenges_128s (W : WotsGame.Adversary Link.prims) (pk : Link.prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_PRE_oracles (wotsPreProblem Link.vp Link.prims pkSeedDist) pk)
        (rPre pkSeedDist W).choose).run ([], [])),
      z.2.1.length ≤ 323449759100660631040 := fun z hz =>
  (rPre_challenges_le_cap pkSeedDist structural_128s W pk z hz).trans wotsChainTargets_128s_val.le

/-- `rTcr` at 128s: at most `4851746386509909465600 < 2^73` targets in every run. -/
theorem rTcr_targets_128s (W : WotsGame.Adversary Link.prims) (pk : Link.prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblem Link.vp Link.prims pkSeedDist) pk)
        (rTcr pkSeedDist W).choose).run ([], [])),
      z.2.1.length ≤ 4851746386509909465600 := fun z hz =>
  ((rTcr_targets_le pkSeedDist structural_128s W pk z hz).2.2).trans wotsExecutedSteps_128s.le

end Wots128

#print axioms tcrTargets_eq
#print axioms wotsInsts_length_eq_sum
#print axioms tcrTargets_128s_val
#print axioms wotsStepTargets_128s_val
#print axioms openPreTargets_128s_val
#print axioms signReads_128s
#print axioms structHashEvals_128s
#print axioms structPrfEvals_128s
#print axioms rUd_challenges_le
#print axioms rPre_challenges_le
#print axioms rTcr_targets_le
#print axioms rTcr_targets_le_cap
#print axioms rUd_challenges_128s
#print axioms rPre_challenges_128s
#print axioms rTcr_targets_128s

end Resources
end Reduction
