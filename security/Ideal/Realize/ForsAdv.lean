import Ideal.Realize.ForsGuess
import Ideal.Realize.Phase1
import Ideal.Transport.AdvFors
import Ideal.ComposeFinal

/-!
# The ideal-model FORS-leaf adversaries and the adversary equalities (FORS-leaf realisers, part 3)

For an ideal-model forger `S`, a table-independent `opt_rand` sampler `oR` and a seed
distribution `pkSeedDist`:

* `dsprAdvI S oR pkSeedDist : ForsDsprAdv128 pkSeedDist`, `tcrAdvI S oR pkSeedDist :
  ForsTcrAdv128 pkSeedDist` — ONE oracle program each: first phase `forsPhase1` (no compression
  query, embedded by `embImpl`), second phase `phase2C` (the port program of the forger
  `typedP codec₀ S.main`, hash queries as compression chains, openings answered inside);
* **equalities** `dspr_eq_S`, `dspr_eq_E`, `tcr_eq_S`, `tcr_eq_E`: for every table `g`, the
  Reduction's adversary at `g` (SUF forger `S.typedS`, resp. EUF forger `S.typedE`, at
  `optRandU oR`) IS `instForsDspr (dsprAdvI …) g`, resp. `instFors (tcrAdvI …) g`.

Route: `Transport.toDspr_setPrf(_S)` moves the adversary from `primsG (liftC g) =
setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g)` to `R₀ (thG g) (hmG g)` (core `core₀`, no `g`);
there `forsDspr_phase2_open_eq` gives the open program, `forsFindOpen_withTH` moves it to
`P₀ = R₀ dT dH`, `typedP_inst` exposes the forger's port, and `phase2C_inst` closes the loop.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Fors

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000

/-- The wire codec over `core₀` (that of `codecC`). -/
def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

theorem primsG_eq (g : CF St Blk) :
    primsG (liftC g) = setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) := rfl

theorem codecG_eq (g : CF St Blk) : codecG g = trCodec core₀ (prfG g) (pmG g) codec₀ := rfl

/-- The `opt_rand` sampler over a bundle with core `core₀`. -/
def optRand₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) :
    PublicKeyCore (R₀ T H).core → ProbComp (R₀ T H).Y := fun pk => oR pk.pkSeed pk.pkRoot

/-- The typed port forger over `P₀`. -/
noncomputable def mainP (S : ForgerI) : PortForgerProg Link.vp P₀ := typedP codec₀ S.main

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

/-- The typed forger over `R₀ T H` built from the forger with its port answered by `g`. -/
noncomputable abbrev A₀ (g : CF St Blk) (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) :=
  bytesToTyped (prims := R₀ T H) (codec := codec₀) (optRand := optRand₀ oR T H)
    (pkSeedDist := pkSeedDist) ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩

/-! ## Transport to the reference core -/

theorem toDspr_S_eq (g : CF St Blk) :
    toDspr (Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)) =
      toDspr (Lazy.bOpenPreS (A₀ S oR pkSeedDist g (thG g) (hmG g))) :=
  toDspr_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR (thG g) (hmG g))
    (optRandU oR g) (fun _ => rfl) pkSeedDist _

theorem toDspr_E_eq (g : CF St Blk) :
    toDspr (Lazy.bOpenPreS (S.typedE (optRandU oR) pkSeedDist g)) =
      toDspr (Lazy.bOpenPreS (A₀ S oR pkSeedDist g (thG g) (hmG g))) :=
  toDspr_setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR (thG g) (hmG g))
    (optRandU oR g) (fun _ => rfl) pkSeedDist _

theorem toTcr_S_eq (g : CF St Blk) :
    toTcr (Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)) =
      toTcr (Lazy.bOpenPreS (A₀ S oR pkSeedDist g (thG g) (hmG g))) :=
  toTcr_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR (thG g) (hmG g))
    (optRandU oR g) (fun _ => rfl) pkSeedDist _

theorem toTcr_E_eq (g : CF St Blk) :
    toTcr (Lazy.bOpenPreS (S.typedE (optRandU oR) pkSeedDist g)) =
      toTcr (Lazy.bOpenPreS (A₀ S oR pkSeedDist g (thG g) (hmG g))) :=
  toTcr_setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR (thG g) (hmG g))
    (optRandU oR g) (fun _ => rfl) pkSeedDist _

/-! ## The forger program over the reference core -/

theorem A₀_main (g : CF St Blk) :
    (A₀ S oR pkSeedDist g (thG g) (hmG g)).main =
      fun pk => simulateQ (instImpl g) (mainP S pk) := by
  funext pk
  exact (typedP_inst (prims := R₀ (thG g) (hmG g)) codec₀ (optRand₀ oR (thG g) (hmG g))
    pkSeedDist g S.main pk).symm

/-- The second phase of the Reduction's open program at `g`, over the reference bundle. -/
theorem phase2_open (g : CF St Blk) {β : Type}
    (post : List (P₀.AdrsKey × P₀.Y) → (ℕ × P₀.Y) × List ℕ → β)
    (tbl : SecIdx → P₀.Y) (tg : List (P₀.AdrsKey × P₀.Y)) (ys : List P₀.Y) (pk : P₀.PkSeed) :
    (forsRun (prims := R₀ (thG g) (hmG g)) (PublicHash.impl (R₀ (thG g) (hmG g))) tbl tg
        (forsFindOpen (prims := R₀ (thG g) (hmG g)) (optRand₀ oR (thG g) (hmG g))
          (A₀ S oR pkSeedDist g (thG g) (hmG g)).main pk ys) >>= fun z => pure (post tg z)) =
      simulateQ (instImpl₀ g) (phase2C post (optRand₀ oR dT dH) (mainP S) tbl tg ys pk) := by
  rw [phase2C_inst, A₀_main, impl_R₀]
  have h := forsFindOpen_withTH (prims := P₀) (optRand := optRand₀ oR dT dH) (thG g) (hmG g)
    (fun pk => simulateQ (instImpl g) (mainP S pk)) pk ys
  exact congrArg (fun P => forsRun (prims := P₀) (implTH (thG g) (hmG g)) tbl tg P >>=
    fun z => pure (post tg z)) h

/-! ## The ideal-model adversaries -/

/-- The first phase `forsPhase1` at the reference bundle, as an irreducible constant (a closed
program: elaboration must never try to evaluate it — its head constructor needs the length of
the WOTS+ index list). -/
noncomputable irreducible_def phase1P : OracleComp (ForsP1Spec P₀) (ForsP1State Link.vp P₀) :=
  forsPhase1 Link.vp P₀

/-- **The ideal-model FORS-leaf SM-DSPR adversary.** -/
noncomputable def dsprAdvI : ForsDsprAdv128 pkSeedDist where
  State := ForsP1State Link.vp P₀
  choose := simulateQ embImpl phase1P
  guess st pk := phase2C (fun tg z => forsDsprPost tg z) (optRand₀ oR dT dH) (mainP S)
    st.1 st.2.1 st.2.2 pk

/-- **The ideal-model FORS-leaf SM-TCR adversary.** -/
noncomputable def tcrAdvI : ForsTcrAdv128 pkSeedDist where
  State := ForsP1State Link.vp P₀
  choose := simulateQ embImpl phase1P
  forge st pk := phase2C (fun _ z => forsTcrPost z) (optRand₀ oR dT dH) (mainP S)
    st.1 st.2.1 st.2.2 pk

end Ideal.Realize.Fors
