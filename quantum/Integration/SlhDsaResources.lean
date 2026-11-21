import PQ.Interactive.Resources
import Integration.SlhDsaApprox

/-!
# SLH-DSA against quantum forgers: resources of the nine reduction machines (integration)

NOT part of the default target.  Imports `Integration.SlhDsaApprox` / `Integration.SlhDsaQuantum`
(not built by lake) and the compiled `Reduction.Headline` of `security/` (read-only).  Check:

```
cd quantum
LP="$(lake env printenv LEAN_PATH):$PWD/../security/.lake/build/lib/lean:\
$PWD/../.tools/aeneas/backends/lean/.lake/build/lib/lean"
mkdir -p /tmp/slhq/Integration
LEAN_PATH="$LP" lean -o /tmp/slhq/Integration/SlhDsaQuantum.olean Integration/SlhDsaQuantum.lean
LEAN_PATH="$LP:/tmp/slhq" lean -o /tmp/slhq/Integration/SlhDsaApprox.olean \
  Integration/SlhDsaApprox.lean
LEAN_PATH="$LP:/tmp/slhq" lean Integration/SlhDsaResources.lean
```

The model has no cost notion and classical code embeds into quantum machines, so the existence of
quantum machines with the advantages of `slhdsa_euf_cma_final_quantum_machines(_all)` is, as a
bare proposition, no stronger than the classical statement.  This file states what the nine
machines ARE:

## (i) Quantum resources: instrument traces

For each of the nine machines, along every root-to-leaf path the sequence of instrument indices
is the sequence of instrument indices of a path of `Q.main pk` for a single public key `pk`
(`instrTraces … ⊆ ⋃ pk, instrTraces (Q.main pk)`; `QuantumResources`, `quantum_resources`); the
workspace and the initial state are those of `Q` (`ρ₀ := Q.ρ₀` by definition of the machines).

PRECISELY (audit F5): this bounds the number, identity and order of the quantum operations on
every path — no path carries more instruments than a single path of `Q` does.  It does NOT show
that the machine follows the path of `Q` selected by the outcomes actually obtained, and it does
not exclude classical simulation of quantum behaviour (classical code is uncounted and may carry
a density matrix).  The statement that the machines ARE the reduction's classical code wrapped
around the program of `Q` is the sampler-generic syntactic certificate
`Reduction.reduction_certificate` (`Integration/SlhDsaAllCertificate.lean`): for every sampler
`s`, `toProbCompWith s (qb Q) Q.ρ₀ = b (Q.toClassicalWith s)`.  The trace inclusions are an
additional, sampler-free fact about the machine terms.

* `qbPrfC Q`, `qbPrfMsgL Q`, `qbItsrL Q` are single machines;
* the six two-phase machines `qToDspr Q`, `qToTcr Q`, `qbTcrS Q`, `qrUd Q`, `qrPre Q`, `qrTcr Q`
  have a FIRST phase (`choose` / `pick`) that is a classical program **by typing**: its type is
  `OracleComp (unifSpec + …) State` — there is no workspace and no instrument node in that type —
  and their SECOND phase (`forge` / `invert` / `distinguish` / `guess`, a closed machine) has its
  instrument traces contained in those of the runs `Q.main pk`.

## (ii) Classical query counts

`QFinalResources Q qs c` is the port of `Reduction.FinalResources` (`Headline.lean`) to the
machines, for a quantum forger with at most `qs` classical signing queries on every path
(`ClassicalQueryBound (Q.main pk) (·.isRight) qs`); `qfinal_resources` proves it with the closed
forms `counts vp qs`.  The counts of the single machines are transferred with
`classicalQueryBound_of_eq` (uniform-sampler classicalisation = the classical reduction applied to
`Q.toClassicalWith unifSamp`); the counts of the classical first phases are the classical
statements themselves (the first phases are the classical programs of `Reduction`).

## Inherited caveat (see `security/REDUCTION_STATUS.md` §5 and the header of `Headline.lean`)

The instrument traces are those of single runs of `Q`.  The CLASSICAL resources are those of the classical
reductions and are not small: the first phases of `qbTcrS`, `qrUd`/`qrPre`/`qrTcr` (from `bWotsS`)
and `qToDspr`/`qToTcr` (from `bOpenPreS`) walk the whole key structure and register
`2^68`–`2^80` targets at SLH-DSA-SHA2-128s (`thashTargets ≈ 2^79.81`, `forsLeaves ≈ 2^78.81`,
`wotsSteps ≈ 2^72.04`, `wotsChains ≈ 2^68.13`), and their second phases carry sparse tables of the
structure.  Local classical computation is not counted (VCVio has no cost model for it).

## Not ported

* the SUF-CMA fields of `FinalResources` (`prfSuf`, `msgSuf*`): their machines are not defined in
  `SlhDsaQuantum.lean`;
* `Resources2*` (`FinalResourcesDirect`: hash evaluations of the SM adversaries after the seed
  reveal) and the split / tight / memo headline variants (`final_split_resources`, `TightCaps`,
  `TcrMemo`): the second phases here are closed machines (`close … (Q.main pk)`), whose only
  classical nodes are uniform queries; the classical hash-evaluation counts of those phases are
  statements about `simulateQ` of a `HasQuery` instance in `Reduction` and were not transported.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

/-! ## (i) Instrument traces -/

/-- The instrument-index sequences of the paths of `Q.main pk`, over all public keys `pk`. -/
def forgerTraces (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    Set (List (InstrIdx W)) :=
  ⋃ pk, instrTraces (Q.main pk)

lemma instrTraces_main_subset (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (pk : PublicKeyCore prims.core) : instrTraces (Q.main pk) ⊆ forgerTraces Q :=
  Set.subset_iUnion (fun pk ↦ instrTraces (Q.main pk)) pk

theorem instrTraces_qbPrf (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qbPrf Q) ⊆ forgerTraces Q :=
  instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_liftQ_bind_subset_of _ _ fun _ ↦
    instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_bind_liftQ_subset_of _ _
      ((instrTraces_qRunForger_subset _ _).trans (instrTraces_main_subset Q _))

/-- Every instrument trace of `qbPrfC Q` is an instrument trace of `Q.main pk` for some `pk`. -/
theorem instrTraces_qbPrfC (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qbPrfC Q) ⊆ forgerTraces Q :=
  (instrTraces_wrap0_subset _ _).trans (instrTraces_qbPrf Q)

section lazy

open Lazy

variable {ι κ : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κ} {D V α : Type}

/-- The resource-explicit lazy cache around a quantum open program (`Lazy.lazyRes`): secret
queries are answered from the cache, with ONE draw query on each miss. -/
noncomputable def qLazyRes [DecidableEq D] (X : QOC W (RSpec gspec D V hspec) α) :
    QOC W (RSpec gspec Unit V hspec) α :=
  Prod.fst <$> wrap lazyImplR X []

lemma qLazyRun_eq [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id)
    (X : QOC W (RSpec gspec D V hspec) α) : qLazyRun hI X = wrap0 (interp hI) (qLazyRes X) := rfl

theorem toProbCompWith_qLazyRes (s : Sampler W) [DecidableEq D]
    (X : QOC W (RSpec gspec D V hspec) α) (ρ : Matrix W W ℂ) :
    toProbCompWith s (qLazyRes X) ρ = lazyRes (toProbCompWith s X ρ) := by
  rw [qLazyRes, toProbCompWith_map, toProbCompWith_wrap _ _ forwardsUnifB_lazyImplR]
  rfl

theorem instrTraces_qLazyRes [DecidableEq D] (X : QOC W (RSpec gspec D V hspec) α) :
    instrTraces (qLazyRes X) ⊆ instrTraces X :=
  (instrTraces_map_subset _ _).trans (instrTraces_wrap_subset _ _ _)

theorem instrTraces_qLazyRun [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id)
    (X : QOC W (RSpec gspec D V hspec) α) : instrTraces (qLazyRun hI X) ⊆ instrTraces X :=
  (instrTraces_wrap0_subset _ _).trans (instrTraces_qLazyRes X)

theorem toProbCompWith_qMsgOpen (s : Sampler W)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qMsgOpen Q) Q.ρ₀ = msgOpen (Q.toClassicalWith s) := by
  unfold qMsgOpen
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForger]
  rfl

theorem toProbCompWith_qItsrOpen (s : Sampler W)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qItsrOpen Q) Q.ρ₀ = itsrOpen (Q.toClassicalWith s) := by
  unfold qItsrOpen
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerLog]
  rfl

theorem instrTraces_qMsgOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qMsgOpen Q) ⊆ forgerTraces Q :=
  instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_liftQ_bind_subset_of _ _ fun _ ↦
    instrTraces_bind_liftQ_subset_of _ _
      ((instrTraces_qRunForger_subset _ _).trans (instrTraces_main_subset Q _))

/-- Every instrument trace of `qbPrfMsgL Q` is an instrument trace of `Q.main pk` for some `pk`. -/
theorem instrTraces_qbPrfMsgL (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qbPrfMsgL Q) ⊆ forgerTraces Q :=
  (instrTraces_qLazyRun _ _).trans (instrTraces_qMsgOpen Q)

theorem instrTraces_qItsrOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qItsrOpen Q) ⊆ forgerTraces Q :=
  instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_liftQ_bind_subset_of _ _ fun _ ↦
    instrTraces_bind_liftQ_subset_of _ _
      ((instrTraces_wrap_subset _ _ _).trans (instrTraces_main_subset Q _))

/-- Every instrument trace of `qbItsrL Q` is an instrument trace of `Q.main pk` for some `pk`. -/
theorem instrTraces_qbItsrL (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qbItsrL Q) ⊆ forgerTraces Q :=
  (instrTraces_qLazyRun _ _).trans (instrTraces_qItsrOpen Q)

end lazy

/-- Second phase of `qbTcrS Q`: every instrument trace is an instrument trace of some `Q.main pk`. -/
theorem instrTraces_qbTcrS_forge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    instrTraces ((qbTcrS Q).forge tbl pkSeed) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _
    ((instrTraces_close_subset _ _ _).trans (instrTraces_main_subset Q _))

theorem instrTraces_qWotsForge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) (pkSeed : prims.PkSeed) :
    instrTraces (qWotsForge Q st pkSeed) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _
    ((instrTraces_close_subset _ _ _).trans (instrTraces_main_subset Q _))

/-- Second phase of `qrTcr Q`: every instrument trace is an instrument trace of some `Q.main pk`. -/
theorem instrTraces_qrTcr_forge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
      List (WotsGame.Entry prims)) (pk : prims.PkSeed) :
    instrTraces ((qrTcr Q).forge st pk) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _ (instrTraces_qWotsForge Q st.1 pk)

/-- Second phase of `qrPre Q`: every instrument trace is an instrument trace of some `Q.main pk`. -/
theorem instrTraces_qrPre_invert (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
      List (WotsGame.Entry prims)) (pk : prims.PkSeed) :
    instrTraces ((qrPre Q).invert st pk) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _ (instrTraces_qWotsForge Q st.1 pk)

/-- Second phase of `qrUd Q`: every instrument trace is an instrument trace of some `Q.main pk`. -/
theorem instrTraces_qrUd_distinguish (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
      List (WotsGame.Entry prims)) (pk : prims.PkSeed) :
    instrTraces ((qrUd Q).distinguish st pk) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _ (instrTraces_qWotsForge Q st.1 pk)

theorem instrTraces_qOpenPreFind (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    instrTraces (qOpenPreFind Q tbl pkSeed ys) ⊆ forgerTraces Q :=
  instrTraces_bind_liftQ_subset_of _ _
    ((instrTraces_wrap_subset _ _ _).trans (instrTraces_main_subset Q _))

theorem instrTraces_qFindRun (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pkSeed : prims.PkSeed) : instrTraces (qFindRun Q st pkSeed) ⊆ forgerTraces Q :=
  (instrTraces_close_subset _ _ _).trans (instrTraces_qOpenPreFind Q _ _ _)

/-- Second phase of `qToTcr Q`: every instrument trace is an instrument trace of some `Q.main pk`. -/
theorem instrTraces_qToTcr_forge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pk : prims.PkSeed) : instrTraces ((qToTcr Q).forge st pk) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _ (instrTraces_qFindRun Q st pk)

/-- Second phase of `qToDspr Q`: every instrument trace is an instrument trace of some `Q.main pk`. -/
theorem instrTraces_qToDspr_guess (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pk : prims.PkSeed) : instrTraces ((qToDspr Q).guess st pk) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _ (instrTraces_qFindRun Q st pk)

/-- **Instrument traces of the nine reduction machines.**  Along every path of each machine the
sequence of instrument indices is that of a path of `Q.main pk` for one public key `pk` (an
inclusion of trace sets; it bounds number, identity and order of the quantum operations, and does
not by itself exclude following a different outcome branch or classical simulation — see the file
header and `reduction_certificate`).  For the six two-phase machines this is the statement for the second
phase; their first phase (`choose` / `pick`) has type `OracleComp (unifSpec + …) State`, i.e. is a
classical program by typing (no workspace, no instrument node). -/
structure QuantumResources (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : Prop where
  prf : instrTraces (qbPrfC Q) ⊆ forgerTraces Q
  msg : instrTraces (qbPrfMsgL Q) ⊆ forgerTraces Q
  itsr : instrTraces (qbItsrL Q) ⊆ forgerTraces Q
  dspr : ∀ st pk, instrTraces ((qToDspr Q).guess st pk) ⊆ forgerTraces Q
  tcrF : ∀ st pk, instrTraces ((qToTcr Q).forge st pk) ⊆ forgerTraces Q
  tcr : ∀ st pk, instrTraces ((qbTcrS Q).forge st pk) ⊆ forgerTraces Q
  ud : ∀ st pk, instrTraces ((qrUd Q).distinguish st pk) ⊆ forgerTraces Q
  pre : ∀ st pk, instrTraces ((qrPre Q).invert st pk) ⊆ forgerTraces Q
  tcrW : ∀ st pk, instrTraces ((qrTcr Q).forge st pk) ⊆ forgerTraces Q
  /-- The workspace state of every machine is the initial state of `Q`. -/
  rho : (qToDspr Q).ρ₀ = Q.ρ₀ ∧ (qToTcr Q).ρ₀ = Q.ρ₀ ∧ (qbTcrS Q).ρ₀ = Q.ρ₀ ∧
    (qrUd Q).ρ₀ = Q.ρ₀ ∧ (qrPre Q).ρ₀ = Q.ρ₀ ∧ (qrTcr Q).ρ₀ = Q.ρ₀

/-- **Every instrument trace of the nine machines is an instrument trace of a single run of
`Q`.**  No hypothesis. -/
theorem quantum_resources (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QuantumResources Q where
  prf := instrTraces_qbPrfC Q
  msg := instrTraces_qbPrfMsgL Q
  itsr := instrTraces_qbItsrL Q
  dspr := instrTraces_qToDspr_guess Q
  tcrF := instrTraces_qToTcr_forge Q
  tcr := instrTraces_qbTcrS_forge Q
  ud := instrTraces_qrUd_distinguish Q
  pre := instrTraces_qrPre_invert Q
  tcrW := instrTraces_qrTcr_forge Q
  rho := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Consequences for the derived measures: a bound on the number of instruments per run of `Q`,
or a restriction of its instrument set, is inherited by all nine machines (shown for the three
single machines; the same one-liner applies to the second phases). -/
theorem instrPathBound_machines (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (n : ℕ)
    (hQ : ∀ pk, InstrPathBound (Q.main pk) n) :
    InstrPathBound (qbPrfC Q) n ∧ InstrPathBound (qbPrfMsgL Q) n ∧ InstrPathBound (qbItsrL Q) n := by
  have key : ∀ l ∈ forgerTraces Q, l.length ≤ n := fun l hl ↦ by
    obtain ⟨pk, hpk⟩ := Set.mem_iUnion.1 hl
    exact hQ pk l hpk
  exact ⟨fun l hl ↦ key l (instrTraces_qbPrfC Q hl), fun l hl ↦ key l (instrTraces_qbPrfMsgL Q hl),
    fun l hl ↦ key l (instrTraces_qbItsrL Q hl)⟩

theorem instrOnly_machines (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (P : InstrIdx W → Prop) (hQ : ∀ pk, InstrOnly P (Q.main pk)) :
    InstrOnly P (qbPrfC Q) ∧ InstrOnly P (qbPrfMsgL Q) ∧ InstrOnly P (qbItsrL Q) := by
  have key : ∀ l ∈ forgerTraces Q, ∀ j ∈ l, P j := fun l hl ↦ by
    obtain ⟨pk, hpk⟩ := Set.mem_iUnion.1 hl
    exact hQ pk l hpk
  exact ⟨fun l hl ↦ key l (instrTraces_qbPrfC Q hl), fun l hl ↦ key l (instrTraces_qbPrfMsgL Q hl),
    fun l hl ↦ key l (instrTraces_qbItsrL Q hl)⟩

/-! ## (ii) Classical query counts -/

/-- **Classical resources of the nine reduction machines** for a quantum forger `Q` with at most
`qs` classical signing queries per run and the counts `c` — the port of `Reduction.FinalResources`
(EUF-CMA fields).

Machines (classical queries counted on the machine's own control tree, `ClassicalQueryBound`):
* `prf` — function queries of the PRF distinguisher `qbPrfC Q`;
* `msg`, `msg_draws`, `msg_hashes`, `itsr`, `itsr_draws`, `itsr_hashes` — game queries (`≤ qs`),
  fresh draws and hash evaluations of the lazy machines `qbPrfMsgL Q`, `qbItsrL Q`, the latter two
  stated on the resource-explicit machines `qLazyRes _` of which they are the interpretation
  (`qLazyRun_eq`);
* `open_find` — opening queries of the open machine `qOpenPreFind Q …` run inside the second
  phases of `qToDspr Q` and `qToTcr Q`.

Classical first phases (classical programs by typing; the counts are those of the classical
reductions, whole key structure, `2^68`–`2^80` at SHA2-128s):
* `dspr_targets`, `tcrF_targets` — targets registered by `(qToDspr Q).choose`, `(qToTcr Q).choose`;
* `tcr_choose`, `tcr_targets` — `(qbTcrS Q).choose` registers exactly the hash calls of the key
  structure of a sampled sparse table;
* `ud`, `pre`, `tcrW` — challenges/targets of `(qrUd Q).pick`, `(qrPre Q).choose`,
  `(qrTcr Q).choose`;
* `open_commit`, `open_samples`, `tcr_samples`, `wots_insts`, `wots_samples` — sizes of the key
  structure (independent of the forger). -/
structure QFinalResources (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (c : Counts) : Prop where
  prf : ClassicalQueryBound (qbPrfC Q) (fun i => i.isRight = true) c.secretReads
  msg : ClassicalQueryBound (qbPrfMsgL Q) (fun i => i.isRight = true) qs
  msg_draws : ClassicalQueryBound (qLazyRes (qMsgOpen Q)) (fun t => Lazy.kind t = .sec)
    c.secretReads
  msg_hashes : ClassicalQueryBound (qLazyRes (qMsgOpen Q)) (fun t => Lazy.kind t = .hash)
    c.hashEvals
  itsr : ClassicalQueryBound (qbItsrL Q) (fun i => i.isRight = true) qs
  itsr_draws : ClassicalQueryBound (qLazyRes (qItsrOpen Q)) (fun t => Lazy.kind t = .sec)
    c.secretReads
  itsr_hashes : ClassicalQueryBound (qLazyRes (qItsrOpen Q)) (fun t => Lazy.kind t = .hash)
    c.hashEvals
  open_find : ∀ st pkSeed ys, ClassicalQueryBound (qOpenPreFind Q st pkSeed ys)
    (fun i => i.isRight = true) c.openings
  open_commit : (forsLeafKeys vp prims).Nodup ∧ (forsLeafKeys vp prims).length = c.forsLeaves
  open_samples : (Lazy.wotsSkIdx vp).length = c.wotsChains
  dspr_targets : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
      (qToDspr Q).choose).run .initial), z.2.challenges.length ≤ c.forsLeaves
  tcrF_targets : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
      (qToTcr Q).choose).run .initial), z.2.challenges.length ≤ c.forsLeaves
  tcr_choose : ∀ pk, (simulateQ (SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
      (qbTcrS Q).choose).run ([], []) =
    (fun tbl => (tbl, (honestCalls tbl pk, []))) <$> Lazy.sparseTable vp prims
  tcr_targets : ∀ (tbl : SecretTable vp prims) (pk : prims.PkSeed),
    ((honestCalls tbl pk).map (·.1)).Nodup ∧ (honestCalls tbl pk).length = c.thashTargets
  tcr_samples : (Lazy.structSecIdx vp).length = c.structCells
  wots_insts : (wotsInsts vp).length = c.wotsInst
  wots_samples : (forsSkIdx vp).length = c.forsLeaves
  ud : ∀ world pk, ∀ z ∈ support ((simulateQ
      (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
      (qrUd Q).pick).run ([], [])), z.2.1.length ≤ c.wotsChains
  pre : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_PRE_oracles (wotsPreProblem vp prims pkSeedDist) pk)
      (qrPre Q).choose).run ([], [])), z.2.1.length ≤ c.wotsChains
  tcrW : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
      (qrTcr Q).choose).run ([], [])), z.2.1.length ≤ c.wotsSteps

/-! The first phases of the six two-phase machines are, by definition, the first phases of the
classical reduction adversaries at `Q.toClassical`.  The following lemmas transport the classical
count statements to the fields of the machines; they are definitional unfoldings (the elaborator
needs a larger budget for some of them: VCVio's `toTCR` is stated for `prob.toTCR`). -/

set_option maxHeartbeats 4000000 in
theorem qToDspr_targets_of {n : ℕ} (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (h : ∀ (B : ForsOpenPreAdv vp prims pkSeedDist) pk, ∀ z ∈ support ((simulateQ
      (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
      (toDspr B).choose).run .initial), z.2.challenges.length ≤ n) :
    ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
      (qToDspr Q).choose).run .initial), z.2.challenges.length ≤ n :=
  fun pk ↦ h (Lazy.bOpenPreS Q.toClassical) pk

set_option maxHeartbeats 4000000 in
theorem qToTcr_targets_of {n : ℕ} (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (h : ∀ (B : ForsOpenPreAdv vp prims pkSeedDist) pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
      (toTcr B).choose).run .initial), z.2.challenges.length ≤ n) :
    ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
      (qToTcr Q).choose).run .initial), z.2.challenges.length ≤ n :=
  fun pk ↦ h (Lazy.bOpenPreS Q.toClassical) pk

set_option maxHeartbeats 4000000 in
theorem qbTcrS_choose_of (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (h : ∀ pk, (simulateQ (SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
      (Lazy.bTcrS Q.toClassical).choose).run ([], []) =
    (fun tbl => (tbl, (honestCalls tbl pk, []))) <$> Lazy.sparseTable vp prims) :
    ∀ pk, (simulateQ (SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
      (qbTcrS Q).choose).run ([], []) =
    (fun tbl => (tbl, (honestCalls tbl pk, []))) <$> Lazy.sparseTable vp prims :=
  h

set_option maxHeartbeats 4000000 in
theorem qrUd_challenges_of {n : ℕ} (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (h : ∀ (W' : WotsGame.Adversary prims) world pk, ∀ z ∈ support ((simulateQ
      (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
      (rUd pkSeedDist W').pick).run ([], [])), z.2.1.length ≤ n) :
    ∀ world pk, ∀ z ∈ support ((simulateQ
      (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
      (qrUd Q).pick).run ([], [])), z.2.1.length ≤ n :=
  fun world pk ↦ h (Lazy.bWotsS Q.toClassical) world pk

set_option maxHeartbeats 4000000 in
theorem qrPre_challenges_of {n : ℕ} (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (h : ∀ (W' : WotsGame.Adversary prims) pk, ∀ z ∈ support ((simulateQ
      (SM_DT_PRE_oracles (wotsPreProblem vp prims pkSeedDist) pk)
      (rPre pkSeedDist W').choose).run ([], [])), z.2.1.length ≤ n) :
    ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_PRE_oracles (wotsPreProblem vp prims pkSeedDist) pk)
      (qrPre Q).choose).run ([], [])), z.2.1.length ≤ n :=
  fun pk ↦ h (Lazy.bWotsS Q.toClassical) pk

set_option maxHeartbeats 4000000 in
theorem qrTcr_targets_of {n : ℕ} (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (h : ∀ (W' : WotsGame.Adversary prims) pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
      (rTcr pkSeedDist W').choose).run ([], [])), z.2.1.length ≤ n) :
    ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
      (qrTcr Q).choose).run ([], [])), z.2.1.length ≤ n :=
  fun pk ↦ h (Lazy.bWotsS Q.toClassical) pk

/-- For every sampler, the classical strategy of a forger with at most `qs` classical signing
queries per run makes at most `qs` signing queries. -/
theorem toClassicalWith_queryBound (s : Sampler W)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((Q.toClassicalWith s).main pk) (fun i => i.isRight = true) qs :=
  fun pk ↦ isQueryBoundP_toProbCompWith s _ (fun _ h ↦ by simp at h) _ _ _ (hQ pk)

/-- **The resource theorem for the machines.**  For every quantum forger `Q` with at most `qs`
classical signing queries on every path, every count of `QFinalResources` holds with the closed
forms `counts vp qs` of the classical theorem `Reduction.final_resources`. -/
theorem qfinal_resources (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    QFinalResources Q qs (counts vp qs) := by
  have hU := final_resources hS (Q.toClassicalWith unifSamp) qs
    (toClassicalWith_queryBound unifSamp Q qs hQ)
  have hA : ∀ pk, IsQueryBoundP (Q.toClassical.main pk) (fun i => i.isRight = true) qs := by
    intro pk
    have h := toClassicalWith_queryBound exactSamp Q qs hQ pk
    have e : Q.toClassical.main pk = (Q.toClassicalWith exactSamp).main pk :=
      toProbComp_eq_toProbCompWith _ _
    rw [e]
    exact h
  have hC := final_resources hS Q.toClassical qs hA
  have hr : ∀ {κ : Type} (m : ℕ), ¬ ((Sum.inl m : ℕ ⊕ κ).isRight = true) := fun m h ↦ by
    simp at h
  generalize counts vp qs = c at hU hC ⊢
  have hk : ∀ (k : Lazy.Kind), k ≠ .unif → ∀ {ι κ D : Type} (m : ℕ),
      ¬ (Lazy.kind (Sum.inl m : ℕ ⊕ (ι ⊕ (D ⊕ κ))) = k) :=
    fun k hk {_ _ _} m h ↦ hk h.symm
  have prf : ClassicalQueryBound (qbPrfC Q) (fun i => i.isRight = true) c.secretReads :=
    classicalQueryBound_of_eq (fun i => i.isRight = true) (fun m ↦ hr m) _ Q.ρ₀
      (toProbCompWith_qbPrfC unifSamp Q) hU.prf
  have msg : ClassicalQueryBound (qbPrfMsgL Q) (fun i => i.isRight = true) qs :=
    classicalQueryBound_of_eq (fun i => i.isRight = true) (fun m ↦ hr m) _ Q.ρ₀
      (toProbCompWith_qbPrfMsgL unifSamp Q) hU.msg
  have emsg : toProbCompWith unifSamp (qLazyRes (qMsgOpen Q)) Q.ρ₀ =
      Lazy.lazyRes (Lazy.msgOpen (Q.toClassicalWith unifSamp)) :=
    (toProbCompWith_qLazyRes unifSamp _ _).trans
      (congrArg Lazy.lazyRes (toProbCompWith_qMsgOpen unifSamp Q))
  have eitsr : toProbCompWith unifSamp (qLazyRes (qItsrOpen Q)) Q.ρ₀ =
      Lazy.lazyRes (Lazy.itsrOpen (Q.toClassicalWith unifSamp)) :=
    (toProbCompWith_qLazyRes unifSamp _ _).trans
      (congrArg Lazy.lazyRes (toProbCompWith_qItsrOpen unifSamp Q))
  have msg_draws : ClassicalQueryBound (qLazyRes (qMsgOpen Q)) (fun t => Lazy.kind t = .sec)
      c.secretReads :=
    classicalQueryBound_of_eq (fun t => Lazy.kind t = .sec) (fun m ↦ hk _ (by decide) m) _ Q.ρ₀
      emsg hU.msg_draws
  have msg_hashes : ClassicalQueryBound (qLazyRes (qMsgOpen Q)) (fun t => Lazy.kind t = .hash)
      c.hashEvals :=
    classicalQueryBound_of_eq (fun t => Lazy.kind t = .hash) (fun m ↦ hk _ (by decide) m) _ Q.ρ₀
      emsg hU.msg_hashes
  have itsr : ClassicalQueryBound (qbItsrL Q) (fun i => i.isRight = true) qs :=
    classicalQueryBound_of_eq (fun i => i.isRight = true) (fun m ↦ hr m) _ Q.ρ₀
      (toProbCompWith_qbItsrL unifSamp Q) hU.itsr
  have itsr_draws : ClassicalQueryBound (qLazyRes (qItsrOpen Q)) (fun t => Lazy.kind t = .sec)
      c.secretReads :=
    classicalQueryBound_of_eq (fun t => Lazy.kind t = .sec) (fun m ↦ hk _ (by decide) m) _ Q.ρ₀
      eitsr hU.itsr_draws
  have itsr_hashes : ClassicalQueryBound (qLazyRes (qItsrOpen Q)) (fun t => Lazy.kind t = .hash)
      c.hashEvals :=
    classicalQueryBound_of_eq (fun t => Lazy.kind t = .hash) (fun m ↦ hk _ (by decide) m) _ Q.ρ₀
      eitsr hU.itsr_hashes
  have open_find : ∀ st pkSeed ys, ClassicalQueryBound (qOpenPreFind Q st pkSeed ys)
      (fun i => i.isRight = true) c.openings := fun st pkSeed ys ↦
    classicalQueryBound_of_eq (fun i => i.isRight = true) (fun m ↦ hr m) _ Q.ρ₀
      (toProbCompWith_qOpenPreFind unifSamp Q st pkSeed ys) (hU.open_find st pkSeed ys)
  refine { prf := prf, msg := msg, msg_draws := msg_draws, msg_hashes := msg_hashes,
           itsr := itsr, itsr_draws := itsr_draws, itsr_hashes := itsr_hashes,
           open_find := open_find, open_commit := hC.open_commit,
           open_samples := hC.open_samples, dspr_targets := ?d, tcrF_targets := ?t,
           tcr_choose := ?tc, tcr_targets := hC.tcr_targets, tcr_samples := hC.tcr_samples,
           wots_insts := hC.wots_insts, wots_samples := hC.wots_samples, ud := ?ud, pre := ?pre,
           tcrW := ?tcrW }
  case d => exact qToDspr_targets_of Q hC.dspr_targets
  case t => exact qToTcr_targets_of Q hC.tcrF_targets
  case tc => exact qbTcrS_choose_of Q hC.tcr_choose
  case ud => exact qrUd_challenges_of Q hC.ud
  case pre => exact qrPre_challenges_of Q hC.pre
  case tcrW => exact qrTcr_targets_of Q hC.tcrW

/-- **Bound and resources together, for every quantum forger.**  The quantum EUF-CMA advantage is
bounded by the nine quantum advantages of the reduction machines; the instrument traces of each
machine are instrument traces of single runs of `Q` (`QuantumResources`), and its classical query counts are those
of the classical reduction (`QFinalResources`, closed forms `counts vp qs`). -/
theorem slhdsa_euf_cma_final_quantum_machines_resources (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qUnforgeableAdvantage Q ≤
      qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀ +
        qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀ +
        qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
        (qDsprFV_Advantage (qToDspr Q) + 3 * qTcrFV_Advantage (qToTcr Q)) +
        qSM_DT_TCR_Advantage (qbTcrS Q) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_Advantage (qrUd Q) +
        qSM_DT_PRE_Advantage (qrPre Q) +
        qSM_DT_TCR_Advantage (qrTcr Q) ∧
      QuantumResources Q ∧ QFinalResources Q qs (counts vp qs) :=
  ⟨slhdsa_euf_cma_final_quantum_machines_all hS Q, quantum_resources Q, qfinal_resources hS Q qs hQ⟩

end Reduction

#print axioms Reduction.quantum_resources
#print axioms Reduction.instrPathBound_machines
#print axioms Reduction.instrOnly_machines
#print axioms Reduction.qfinal_resources
#print axioms Reduction.slhdsa_euf_cma_final_quantum_machines_resources
