import Integration.SlhDsaAllResources
import Reduction.ResourcesFinal

/-!
# Classical resource counts of the machines of the final unconditional headlines (integration)

NOT part of the default target; checked by `scripts/check-integration.sh`.

Port of `Reduction.FinalResourcesFinal` / `final_resources_final`
(`security/Reduction/ResourcesFinal.lean`, with `Resources2.FinalResourcesDirect`) to the quantum
machines on the right-hand sides of the `…_quantum_all` headlines of `Integration/SlhDsaAll.lean`
(EUF and SUF distinguishers, memoising class adversaries `qbTcrArM n`, tight-cap chain adversary
`qrTcrT`, FORS-leaf adversaries, byte-level and context-string wrappers), in the
`ClassicalQueryBound` style of `PQ/Interactive/Resources.lean`.

`QFinalResourcesFinal Q qs c memoP2` (theorem `qfinal_resources_final`, for a quantum forger with
at most `qs` classical signing queries on every path) has four groups of fields.

1. **Single-phase machines** (`qbPrfC`, `qbPrfWC sufCheck`, `qbPrfMsgL`, `qbPrfMsgWL sufCheck`,
   `qbItsrL`): classical game queries, fresh draws and hash evaluations, counted on the control
   tree of the machine itself (`ClassicalQueryBound`), the draws and hashes on the
   resource-explicit machines `qLazyRes _` of which the lazy machines are the interpretation
   (`qLazyRun_eq`).

2. **Own hash evaluations after the seed reveal** (`*_phase2_hashes`, `fors_phase2_openings`).
   PRECISE STATUS.  In the current definitions the second phase of every two-phase machine is a
   closed machine `close (… g2SignOracle …) (Q.main pk) [] >>= liftU (pure …)`: its signing
   simulation and its answer extraction evaluate `prims.Thash` / `prims.Hmsg` *inside pure
   classical code*; these evaluations are NOT oracle queries of the machine, so they cannot be
   counted on its control tree.  As in the classical development (`Resources2`), they are counted
   on *open machines* — `qFindOpenFull Q pk ys`, `qMemoForgeOpen Q L pk`,
   `qWotsPhase2O Q tbl hist root pk tail` — which are the classical open programs
   `findOpenFull`, `memoForgeOpen`, `wotsPhase2O` around ONE run of `Q`, and in which every hash
   evaluation is a classical query of kind `.hash`.  The bounds on these are theorems about the
   open machines' own control trees.

3. **Link between the open machines and the actual second phases** (`*_phase2`).  The classical
   theorems say "phase 2 = interpretation (`Lazy.tblImpl`) of the open program", as an equality of
   classical programs.  For the machines this is proved AT THE LEVEL OF CLASSICALISATIONS, FOR
   EVERY SAMPLER `s`: the `s`-classicalisation of the machine's second phase is the
   interpretation of the `s`-classicalisation of the open machine.  It is not proved as an
   equality of machine terms (that would need the classical interpretation lemmas
   `*_tbl` re-proved for machines, or the second phases *defined* as
   `wrap0 (Lazy.tblImpl …) (open machine)` followed by `close`).

4. **Classical first phases and all classical counts, for every sampler**
   (`classical : ∀ s, FinalResourcesFinal (Q.toClassicalWith s) qs c memoP2`: the complete
   classical bundle holds for the classical reduction adversaries at EVERY classical approximant
   `Q.toClassicalWith s` of the forger — in particular at the rational approximants
   `Q.toClassicalN n` used in the limit argument, and at the uniform-sampler relabelling; the
   signing-query bound of `Q.toClassicalWith s` is `QForger_toClassicalWith_queryBound`.  Nothing
   is stated about `Q.toClassical` as a forger: for irrational Born probabilities its instrument
   sampling is a junk default.  `Q.toClassical` occurs only inside the FIRST phases of the
   machines, which are defined as the first phases of the classical adversaries and do not depend
   on the forger argument: `bTcrArM_choose_eq`, `first_phase_*`; with
   `first_phase_*` identifying the first phases of the machines with those of the classical
   adversaries at `Q.toClassical`, and the caps restated on the machines' own `choose` fields:
   `memo_run`, `memo_cap`, `wtcrT_cap`).  These are classical programs by typing; the counts are
   those of the classical reductions: whole key structure, `2^63`–`2^80` targets at SHA2-128s.

Wrappers: `qToInternal_queryBound`, `qBytesToTyped_queryBound`,
`qPureBytesToInternal_queryBound` — the interface translations make one typed signing query per
signing query of the forger.

Combined theorems: `slhdsa_{,pure_,bytes_,pure_bytes_}{euf,suf}_cma_final_quantum_all_resources_counts`.

Not ported / inherited limits: everything marked **A** (argued only) in the table of
`ResourcesFinal.lean` (collection queries and own samples of `rUd`/`rPre`/`rTcrT`, the pure tails
`wotsAnswer`, absence of hashing in the first phases, list work, state size); the own hashing of
the PRF distinguishers `qbPrfC`/`qbPrfWC` (not modelled classically either); local classical
computation in general (no cost model in VCVio).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive
open scoped ComplexOrder

namespace Reduction

open TweakableHash Resources2

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

attribute [local irreducible] arityTargets tcrTargets
attribute [local instance] Lazy.openQ Lazy.closedQ

/-! ## Open machines of the second phases -/

section openMachines

variable {ι : Type} {gspec : OracleSpec ι}

/-- `Resources2.findOpenFull` around the quantum forger: key generation, ONE run of `Q` with open
signing, the answer extraction — every hash evaluation is a classical query of kind `.hash`,
every simulated opening a query of kind `.game`. -/
noncomputable def qFindOpenFull (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    QOC W (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y) :=
  liftQ (Lazy.openKeygen prims (forsG prims) pkSeed) >>= fun root =>
  qRunForgerLog Q ⟨pkSeed, root⟩ lazyRandomizerLift (forsSignOpen ⟨pkSeed, root⟩ ys) >>= fun z =>
  liftQ (findAnswerO ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2)

theorem toProbCompWith_qFindOpenFull (s : Sampler W)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) :
    toProbCompWith s (qFindOpenFull Q pkSeed ys) Q.ρ₀ =
      findOpenFull (Q.toClassicalWith s) pkSeed ys := by
  unfold qFindOpenFull
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerLog]
  rfl

/-- `Resources2.memoForgeOpen` around the quantum forger: key generation, ONE run of `Q` with
open signing, verification of the forgery with the collision search against the stored list. -/
noncomputable def qMemoForgeOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    QOC W (Lazy.OSpec prims gspec) (ℕ × List prims.Y) :=
  liftQ (Lazy.openKeygen prims gspec pkSeed) >>= fun root =>
  qRunForgerLog Q ⟨pkSeed, root⟩ lazyRandomizerLift
    (fun m R => Lazy.openSign prims gspec m pkSeed root R) >>= fun z =>
  liftQ (do
    let dg ← (PublicHash.hmsg prims.core z.1.2.randomness pkSeed root z.1.1 :
      OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m))
    let c ← (simulateQ (collO (gspec := gspec) pkSeed L)
      (verifyFree pkSeed (splitDigest vp.params dg) z.1.2)).run none
    return c.2.getD (0, []))

theorem toProbCompWith_qMemoForgeOpen (s : Sampler W)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    toProbCompWith s (qMemoForgeOpen (gspec := gspec) Q L pkSeed) Q.ρ₀ =
      memoForgeOpen (Q.toClassicalWith s) L pkSeed := by
  unfold qMemoForgeOpen
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerLog]
  rfl

/-- `Resources2.wotsPhase2O` around the quantum forger: ONE run of `Q` with signing from the
recorded history, the pure extraction `wotsAnswer`, then the open tail `tail`. -/
noncomputable def qWotsPhase2O (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    QOC W (Lazy.OSpec prims gspec) β :=
  qRunForgerLog Q ⟨pk, root⟩ lazyRandomizerLift (wotsSignFromHistO hist ⟨pk, root⟩) >>= fun r =>
  liftQ (tail (wotsAnswer tbl hist ⟨pk, root⟩ r.1.1 r.1.2))

theorem toProbCompWith_qWotsPhase2O (s : Sampler W)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    toProbCompWith s (qWotsPhase2O Q tbl hist root pk tail) Q.ρ₀ =
      wotsPhase2O (Q.toClassicalWith s) tbl hist root pk tail := by
  unfold qWotsPhase2O
  simp only [toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerLog]
  rfl

/-- Every instrument trace of the open machines is an instrument trace of some `Q.main pk`. -/
theorem instrTraces_qFindOpenFull (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    instrTraces (qFindOpenFull Q pkSeed ys) ⊆ forgerTraces Q :=
  instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_bind_liftQ_subset_of _ _
    ((instrTraces_wrap_subset _ _ _).trans (instrTraces_main_subset Q _))

theorem instrTraces_qMemoForgeOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    instrTraces (qMemoForgeOpen (gspec := gspec) Q L pkSeed) ⊆ forgerTraces Q :=
  instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_bind_liftQ_subset_of _ _
    ((instrTraces_wrap_subset _ _ _).trans (instrTraces_main_subset Q _))

theorem instrTraces_qWotsPhase2O (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    instrTraces (qWotsPhase2O Q tbl hist root pk tail) ⊆ forgerTraces Q :=
  instrTraces_bind_liftQ_subset_of _ _
    ((instrTraces_wrap_subset _ _ _).trans (instrTraces_main_subset Q _))

end openMachines

/-! ## Transfer helpers -/

section helpers

variable {ι' : Type} {spec' : OracleSpec ι'} {α : Type}

/-- Transfer for the predicate "is not a uniform-sampling query". -/
theorem cqb_right (X : QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ)
    {B : OracleComp (unifSpec + spec') α} (hB : toProbCompWith unifSamp X ρ = B) {n : ℕ}
    (h : IsQueryBoundP B (fun i => i.isRight = true) n) :
    ClassicalQueryBound X (fun i => i.isRight = true) n :=
  classicalQueryBound_of_eq (fun i => i.isRight = true) (fun m h ↦ by simp at h) X ρ hB h

/-- Transfer for the query kinds of open programs (`.game`, `.sec`, `.hash`). -/
theorem cqb_kind {ι κ D V : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κ} (k : Lazy.Kind)
    (hk : k ≠ .unif) (X : QOC W (Lazy.RSpec gspec D V hspec) α) (ρ : Matrix W W ℂ)
    {B : OracleComp (Lazy.RSpec gspec D V hspec) α} (hB : toProbCompWith unifSamp X ρ = B) {n : ℕ}
    (h : IsQueryBoundP B (fun t => Lazy.kind t = k) n) :
    ClassicalQueryBound X (fun t => Lazy.kind t = k) n :=
  classicalQueryBound_of_eq (fun t => Lazy.kind t = k) (fun _ h ↦ hk h.symm) X ρ hB h

variable {M PK SK S : Type} {alg : SignatureAlg ProbComp M PK SK S}

/-- For every sampler, the classical strategy of a quantum forger with at most `qs` classical
signing queries per run makes at most `qs` signing queries (any signature scheme). -/
theorem QForger_toClassicalWith_queryBound (s : Sampler W) (Q : QForger W alg) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((Q.toClassicalWith s).main pk) (fun i => i.isRight = true) qs :=
  fun pk ↦ isQueryBoundP_toProbCompWith s _ (fun _ h ↦ by simp at h) _ _ _ (hQ pk)

theorem QForger_toClassical_queryBound (Q : QForger W alg) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP (Q.toClassical.main pk) (fun i => i.isRight = true) qs := by
  intro pk
  have h := QForger_toClassicalWith_queryBound exactSamp Q qs hQ pk
  have e : Q.toClassical.main pk = (Q.toClassicalWith exactSamp).main pk :=
    toProbComp_eq_toProbCompWith _ _
  rw [e]
  exact h

end helpers

/-! ## Interface translations: signing-query counts -/

/-- `qToInternal Q` makes at most as many classical signing queries as `Q`. -/
theorem qToInternal_queryBound (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, ClassicalQueryBound ((qToInternal Q).main pk) (fun i => i.isRight = true) qs :=
  fun pk ↦ cqb_right _ Q.ρ₀
    (congrArg (fun A : Forger vp prims optRand pkSeedDist => A.main pk)
      (toClassicalWith_qToInternal unifSamp Q))
    (toInternal_queryBound _ qs (QForger_toClassicalWith_queryBound unifSamp Q qs hQ) pk)

/-- `qBytesToTyped Q` makes at most as many classical signing queries as `Q`. -/
theorem qBytesToTyped_queryBound (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist))
    (qs : ℕ) (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, ClassicalQueryBound ((qBytesToTyped Q).main pk) (fun i => i.isRight = true) qs :=
  fun pk ↦ cqb_right _ Q.ρ₀
    (congrArg (fun A : Forger vp prims optRand pkSeedDist => A.main pk)
      (toClassicalWith_qBytesToTyped unifSamp Q))
    (bytesToTyped_queryBound _ qs (QForger_toClassicalWith_queryBound unifSamp Q qs hQ) pk)

/-- `qPureBytesToInternal Q` makes at most as many classical signing queries as `Q`. -/
theorem qPureBytesToInternal_queryBound
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, ClassicalQueryBound ((qPureBytesToInternal Q).main pk) (fun i => i.isRight = true) qs :=
  fun pk ↦ cqb_right _ Q.ρ₀
    (congrArg (fun A : Forger vp prims optRand pkSeedDist => A.main pk)
      (toClassicalWith_qPureBytesToInternal unifSamp Q))
    (toInternal_pureBytesToTyped_queryBound _ qs
      (QForger_toClassicalWith_queryBound unifSamp Q qs hQ) pk)

/-! ## Links: second phases and open machines, for every sampler -/

section links

variable (s : Sampler W) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity in
/-- The `s`-classicalisation of the second phase of `qToTcr Q` is the interpretation of the
`s`-classicalisation of the open machine `qFindOpenFull Q pk ys` (opening simulation, table
reads, hashes by `prims`). -/
theorem qToTcr_forge_open (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
    (ys : List prims.Y) (pk : prims.PkSeed) :
    toProbCompCWith s ((qToTcr Q).forge (tbl, tg, ys) pk) Q.ρ₀ =
      (simulateQ (findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (toProbCompWith s (qFindOpenFull Q pk ys) Q.ρ₀))).run [] >>= fun z => pure z.1 := by
  rw [toProbCompWith_qFindOpenFull, ← toTcr_bOpenPreS_forge_full]
  change toProbCompCWith s (_ >>= fun r => liftU _) Q.ρ₀ = _
  rw [toProbCompCWith_bind_liftU, toProbCompCWith_qFindRun]
  rfl

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity in
theorem qToDspr_guess_open (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
    (ys : List prims.Y) (pk : prims.PkSeed) :
    toProbCompCWith s ((qToDspr Q).guess (tbl, tg, ys) pk) Q.ρ₀ =
      (simulateQ (findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (toProbCompWith s (qFindOpenFull Q pk ys) Q.ρ₀))).run [] >>= fun z => pure (z.1.1,
            decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2)) := by
  rw [toProbCompWith_qFindOpenFull, ← toDspr_bOpenPreS_guess_full]
  change toProbCompCWith s (_ >>= fun r => liftU _) Q.ρ₀ = _
  rw [toProbCompCWith_bind_liftU, toProbCompCWith_qFindRun]
  rfl

/-- The `s`-classicalisation of the second phase of `qbTcrArM n Q` is the interpretation of the
`s`-classicalisation of the open machine `qMemoForgeOpen Q L pk`, then the hash-free output
translation. -/
theorem qMemoForge_open {ι : Type} (gspec : OracleSpec ι) (n : ℕ) (tbl : SecretTable vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (liftM (toProbCompCWith s (qMemoForge n Q (tbl, L) pk) Q.ρ₀) :
        OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (toProbCompWith s (qMemoForgeOpen Q L pk) Q.ρ₀) >>= fun jm =>
          pure (classOut prims n L jm) := by
  rw [toProbCompCWith_qMemoForge, toProbCompWith_qMemoForgeOpen]
  exact bTcrArM_forge_open n _ tbl L pk

theorem qrUd_distinguish_open {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    (liftM (toProbCompCWith s ((qrUd Q).distinguish ((tbl, hist, root), hist2) pk) Q.ρ₀) :
        OracleComp (unifSpec + gspec) Bool) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (toProbCompWith s (qWotsPhase2O Q tbl hist root pk
          fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2) Q.ρ₀) := by
  rw [toProbCompWith_qWotsPhase2O, ← wots_rUd_bWotsS_phase2_eq]
  congr 1
  change toProbCompCWith s (_ >>= fun x => liftU _) Q.ρ₀ = _
  rw [toProbCompCWith_bind_liftU, toProbCompCWith_qWotsForge]
  rfl

theorem qrPre_invert_open {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    (liftM (toProbCompCWith s ((qrPre Q).invert ((tbl, hist, root), hist2) pk) Q.ρ₀) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (toProbCompWith s (qWotsPhase2O Q tbl hist root pk
          fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) Q.ρ₀) := by
  rw [toProbCompWith_qWotsPhase2O, ← wots_rPre_bWotsS_phase2_eq]
  congr 1
  change toProbCompCWith s (_ >>= fun x => liftU _) Q.ρ₀ = _
  rw [toProbCompCWith_bind_liftU, toProbCompCWith_qWotsForge]
  rfl

theorem qrTcrT_forge_open {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    (liftM (toProbCompCWith s ((qrTcrT Q).forge ((tbl, hist, root), hist2) pk) Q.ρ₀) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (toProbCompWith s (qWotsPhase2O Q tbl hist root pk
          fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) Q.ρ₀) := by
  rw [toProbCompWith_qWotsPhase2O, ← wots_rTcr_bWotsS_phase2_eq]
  congr 1
  change toProbCompCWith s (_ >>= fun x => liftU _) Q.ρ₀ = _
  rw [toProbCompCWith_bind_liftU, toProbCompCWith_qWotsForge]
  rfl

end links

/-! ## First phases: the classical programs of the reduction -/

section firstPhases

variable (Q : QForger W (internalAlg vp prims optRand pkSeedDist))

omit [Fintype prims.Y] in
/-- The first phase of a machine built by `qTcrOfClassical B …` is the first phase of the
classical adversary `B`. -/
theorem qTcrOfClassical_choose {ι PkSeed Tweak M Y : Type}
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (B : SM_DT_TCR_Adversary P)
    (qf : B.State → PkSeed → Closed W (ℕ × M)) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef)
    (h₂ : ρ₀.trace = 1) : (qTcrOfClassical B qf ρ₀ h₁ h₂).choose = B.choose := rfl

/-- `qbTcrArM n Q` is built on the classical phases of `bTcrArM n Q.toClassical`; with
`qTcrOfClassical_choose`: its first phase is the first phase of the classical `bTcrArM n` (which
does not depend on the forger, `bTcrArM_choose_eq`), i.e. the program of `bTcrArS n`. -/
theorem first_phase_qbTcrArM (n : ℕ) :
    qbTcrArM n Q = qTcrOfClassical (bTcrArM n Q.toClassical) (fun s pk => qMemoForge n Q s pk)
      Q.ρ₀ Q.posSemidef Q.trace_eq_one := rfl

theorem first_phase_qrTcrT_state :
    (qrTcrT Q).State = (rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical)).State := rfl

theorem first_phase_qrTcrT :
    HEq (qrTcrT Q).choose (rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical)).choose := HEq.rfl

theorem first_phase_qrUd_state :
    (qrUd Q).State = (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)).State := rfl

theorem first_phase_qrUd :
    HEq (qrUd Q).pick (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)).pick := HEq.rfl

theorem first_phase_qrPre_state :
    (qrPre Q).State = (rPre pkSeedDist (Lazy.bWotsS Q.toClassical)).State := rfl

theorem first_phase_qrPre :
    HEq (qrPre Q).choose (rPre pkSeedDist (Lazy.bWotsS Q.toClassical)).choose := HEq.rfl

set_option maxHeartbeats 4000000 in
theorem first_phase_qToTcr_state :
    (qToTcr Q).State = (toTcr (Lazy.bOpenPreS Q.toClassical)).State := rfl

set_option maxHeartbeats 4000000 in
theorem first_phase_qToTcr :
    HEq (qToTcr Q).choose (toTcr (Lazy.bOpenPreS Q.toClassical)).choose := HEq.rfl

set_option maxHeartbeats 4000000 in
theorem first_phase_qToDspr_state :
    (qToDspr Q).State = (toDspr (Lazy.bOpenPreS Q.toClassical)).State := rfl

set_option maxHeartbeats 4000000 in
theorem first_phase_qToDspr :
    HEq (qToDspr Q).choose (toDspr (Lazy.bOpenPreS Q.toClassical)).choose := HEq.rfl

set_option maxHeartbeats 4000000 in
/-- Accepted targets of the first phase of `qrTcrT Q` in the tight-cap game. -/
theorem qrTcrT_cap_of {n : ℕ}
    (h : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (wotsTcrProblemT vp prims pkSeedDist) pk)
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS Q.toClassical)).choose).run ([], [])),
      z.2.1.length ≤ n) :
    ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (wotsTcrProblemT vp prims pkSeedDist) pk)
      (qrTcrT Q).choose).run ([], [])), z.2.1.length ≤ n :=
  h

end firstPhases

/-! ## The bundle -/

/-- The bound on the own post-seed hash evaluations of each class adversary. -/
abbrev finalMemoP2 (vp : ValidatedParams) (qs : ℕ) : ℕ :=
  Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2)

/-- **Classical resources of the machines of the final headlines**, for a quantum forger `Q` with
at most `qs` classical signing queries per run; `c` are the closed forms of
`Resources2.directCounts`, `memoP2` bounds the own post-seed hash evaluations of each class
adversary.  See the file header for the four groups of fields and their exact status. -/
structure QFinalResourcesFinal (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (c : Resources2.DirectCounts) (memoP2 : ℕ) : Prop where
  -- 1. single-phase machines
  prf : ClassicalQueryBound (qbPrfC Q) (fun i => i.isRight = true) c.secretReads
  prfSuf : ClassicalQueryBound (qbPrfWC sufCheck Q) (fun i => i.isRight = true) c.secretReads
  msg : ClassicalQueryBound (qbPrfMsgL Q) (fun i => i.isRight = true) qs
  msg_draws : ClassicalQueryBound (qLazyRes (qMsgOpen Q)) (fun t => Lazy.kind t = .sec)
    c.secretReads
  msg_hashes : ClassicalQueryBound (qLazyRes (qMsgOpen Q)) (fun t => Lazy.kind t = .hash)
    c.lazyHashes
  msgSuf : ClassicalQueryBound (qbPrfMsgWL sufCheck Q) (fun i => i.isRight = true) qs
  msgSuf_draws : ClassicalQueryBound (qLazyRes (qMsgOpenW sufCheck Q))
    (fun t => Lazy.kind t = .sec) c.secretReads
  msgSuf_hashes : ClassicalQueryBound (qLazyRes (qMsgOpenW sufCheck Q))
    (fun t => Lazy.kind t = .hash) c.lazyHashes
  itsr : ClassicalQueryBound (qbItsrL Q) (fun i => i.isRight = true) qs
  itsr_draws : ClassicalQueryBound (qLazyRes (qItsrOpen Q)) (fun t => Lazy.kind t = .sec)
    c.secretReads
  itsr_hashes : ClassicalQueryBound (qLazyRes (qItsrOpen Q)) (fun t => Lazy.kind t = .hash)
    c.lazyHashes
  -- 2. own hash evaluations after the seed reveal, on the open machines
  fors_phase2_hashes : ∀ pk ys, ClassicalQueryBound (qFindOpenFull Q pk ys)
    (fun t => Lazy.kind t = .hash) c.forsP2
  fors_phase2_openings : ∀ pk ys, ClassicalQueryBound (qFindOpenFull Q pk ys)
    (fun t => Lazy.kind t = .game) c.openings
  memo_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι)
      (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed),
    ClassicalQueryBound (qMemoForgeOpen (gspec := gspec) Q L pk)
      (fun t => Lazy.kind t = .hash) memoP2
  ud_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    ClassicalQueryBound (qWotsPhase2O (gspec := gspec) Q tbl hist root pk
      fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash) c.udP2
  pre_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    ClassicalQueryBound (qWotsPhase2O (gspec := gspec) Q tbl hist root pk
      fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash) c.preP2
  wtcr_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    ClassicalQueryBound (qWotsPhase2O (gspec := gspec) Q tbl hist root pk
      fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash) c.wtcrP2
  -- 4. classical first phases
  /-- Phase 1 of `qbTcrArM n Q` in the tight-cap game, in closed form. -/
  memo_run : ∀ n pk,
    (simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (qbTcrArM n Q).choose).run ([], []) =
      (fun tbl => ((tbl, honestCalls tbl pk),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          ((fun xs => Tables.updateList (fun _ => default) (Lazy.structSecIdx vp) xs) <$>
            Tables.sampleList prims.Y (Lazy.structSecIdx vp).length)
  /-- The cap of the tight class game is attained in every run. -/
  memo_cap : ∀ n pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
      (qbTcrArM n Q).choose).run ([], [])),
    z.2.1.length = (thashArityProblemT vp prims pkSeedDist n).numTargets
  /-- Accepted targets of `qrTcrT Q` in the tight-cap game: at most `wotsSteps`. -/
  wtcrT_cap : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (wotsTcrProblemT vp prims pkSeedDist) pk)
      (qrTcrT Q).choose).run ([], [])), z.2.1.length ≤ c.wotsSteps
  /-- All classical counts of `Reduction.FinalResourcesFinal`, for the classical reduction
  adversaries at the classical approximant `Q.toClassicalWith s` of the forger, for EVERY sampler
  `s` (by `reduction_certificate` these adversaries are the `s`-classicalisations of the
  machines). -/
  classical : ∀ s : Sampler W, FinalResourcesFinal (Q.toClassicalWith s) qs c memoP2

/-- **The resource theorem for the machines of the final headlines.** -/
theorem qfinal_resources_final (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    QFinalResourcesFinal Q qs (Resources2.directCounts vp qs) (finalMemoP2 vp qs) := by
  have hU := final_resources_final hS (Q.toClassicalWith unifSamp) qs
    (QForger_toClassicalWith_queryBound unifSamp Q qs hQ)
  have hC := final_resources_final hS Q.toClassical qs (QForger_toClassical_queryBound Q qs hQ)
  have hAll : ∀ s : Sampler W, FinalResourcesFinal (Q.toClassicalWith s) qs
      (Resources2.directCounts vp qs) (finalMemoP2 vp qs) := fun s ↦
    final_resources_final hS (Q.toClassicalWith s) qs
      (QForger_toClassicalWith_queryBound s Q qs hQ)
  generalize Resources2.directCounts vp qs = c at hU hC hAll ⊢
  have hD := hU.direct
  have emsg : toProbCompWith unifSamp (qLazyRes (qMsgOpen Q)) Q.ρ₀ =
      Lazy.lazyRes (Lazy.msgOpen (Q.toClassicalWith unifSamp)) :=
    (toProbCompWith_qLazyRes unifSamp _ _).trans
      (congrArg Lazy.lazyRes (toProbCompWith_qMsgOpen unifSamp Q))
  have emsgW : toProbCompWith unifSamp (qLazyRes (qMsgOpenW sufCheck Q)) Q.ρ₀ =
      Lazy.lazyRes (Lazy.msgOpenW sufCheck (Q.toClassicalWith unifSamp)) := by
    rw [toProbCompWith_qLazyRes]
    congr 1
    unfold qMsgOpenW
    simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerSig]
    rfl
  have eitsr : toProbCompWith unifSamp (qLazyRes (qItsrOpen Q)) Q.ρ₀ =
      Lazy.lazyRes (Lazy.itsrOpen (Q.toClassicalWith unifSamp)) :=
    (toProbCompWith_qLazyRes unifSamp _ _).trans
      (congrArg Lazy.lazyRes (toProbCompWith_qItsrOpen unifSamp Q))
  refine
    { prf := cqb_right _ Q.ρ₀ (toProbCompWith_qbPrfC unifSamp Q) hD.prf
      prfSuf := cqb_right _ Q.ρ₀ (toProbCompWith_qbPrfWC unifSamp sufCheck Q) hD.prfSuf
      msg := cqb_right _ Q.ρ₀ (toProbCompWith_qbPrfMsgL unifSamp Q) hD.msg
      msg_draws := cqb_kind .sec (by decide) _ Q.ρ₀ emsg hD.msg_draws
      msg_hashes := cqb_kind .hash (by decide) _ Q.ρ₀ emsg hD.msg_hashes
      msgSuf := cqb_right _ Q.ρ₀ (toProbCompWith_qbPrfMsgWL unifSamp sufCheck Q) hD.msgSuf
      msgSuf_draws := cqb_kind .sec (by decide) _ Q.ρ₀ emsgW hD.msgSuf_draws
      msgSuf_hashes := cqb_kind .hash (by decide) _ Q.ρ₀ emsgW hD.msgSuf_hashes
      itsr := cqb_right _ Q.ρ₀ (toProbCompWith_qbItsrL unifSamp Q) hD.itsr
      itsr_draws := cqb_kind .sec (by decide) _ Q.ρ₀ eitsr hD.itsr_draws
      itsr_hashes := cqb_kind .hash (by decide) _ Q.ρ₀ eitsr hD.itsr_hashes
      fors_phase2_hashes := fun pk ys ↦ cqb_kind .hash (by decide) _ Q.ρ₀
        (toProbCompWith_qFindOpenFull unifSamp Q pk ys) (hD.fors_phase2_hashes pk ys)
      fors_phase2_openings := fun pk ys ↦ cqb_kind .game (by decide) _ Q.ρ₀
        (toProbCompWith_qFindOpenFull unifSamp Q pk ys) (hD.fors_phase2_openings pk ys)
      memo_phase2_hashes := fun gspec L pk ↦ cqb_kind .hash (by decide) _ Q.ρ₀
        (toProbCompWith_qMemoForgeOpen unifSamp Q L pk) (hU.memo_phase2_hashes gspec L pk)
      ud_phase2_hashes := fun gspec tbl hist hist2 root pk ↦ cqb_kind .hash (by decide) _ Q.ρ₀
        (toProbCompWith_qWotsPhase2O unifSamp Q tbl hist root pk _)
        (hD.ud_phase2_hashes gspec tbl hist hist2 root pk)
      pre_phase2_hashes := fun gspec tbl hist hist2 root pk ↦ cqb_kind .hash (by decide) _ Q.ρ₀
        (toProbCompWith_qWotsPhase2O unifSamp Q tbl hist root pk _)
        (hD.pre_phase2_hashes gspec tbl hist hist2 root pk)
      wtcr_phase2_hashes := fun gspec tbl hist hist2 root pk ↦ cqb_kind .hash (by decide) _ Q.ρ₀
        (toProbCompWith_qWotsPhase2O unifSamp Q tbl hist root pk _)
        (hD.wtcr_phase2_hashes gspec tbl hist hist2 root pk)
      memo_run := ?mr
      memo_cap := ?mc
      wtcrT_cap := qrTcrT_cap_of Q hC.wtcrT_cap
      classical := hAll }
  case mr =>
    intro n pk
    dsimp only [qbTcrArM, qTcrOfClassical]
    exact hC.memo_run n pk
  case mc =>
    intro n pk
    dsimp only [qbTcrArM, qTcrOfClassical]
    exact hC.memo_cap n pk

/-- The machines' resources at SLH-DSA-SHA2-128s, as numerals
(`Resources2.directCounts128s qs`; class adversaries: `≤ 269824 + qs·2007385 + 7857` own hash
evaluations after the seed reveal, as hash queries of `qMemoForgeOpen`). -/
theorem qfinal_resources_final_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (Q : QForger W (internalAlg Link.vp Link.prims optRand pkSeedDist)) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    QFinalResourcesFinal Q qs (Resources2.directCounts128s qs) (269824 + qs * 2007385 + 7857) := by
  have h := qfinal_resources_final structural_128s Q qs hQ
  rw [finalMemoP2, Resources2.directCounts_128s, keygenHashes_128s, signHashes_128s,
    Resources2.verifyHashes_128s] at h
  exact h

/-! ## The headlines with quantum resources and classical counts -/

section headlines

/-- Resources of the machines built on a typed internal quantum forger `qT` with at most `qs`
classical signing queries: instrument-trace inclusions and the classical counts. -/
theorem resources_counts (hS : Structural vp prims)
    (qT : QForger W (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (h : ∀ pk, ClassicalQueryBound (qT.main pk) (fun i => i.isRight = true) qs) :
    QuantumResourcesFinal qT ∧
      QFinalResourcesFinal qT qs (Resources2.directCounts vp qs) (finalMemoP2 vp qs) :=
  ⟨quantum_resources_final qT, qfinal_resources_final hS qT qs h⟩


theorem slhdsa_euf_cma_final_quantum_all_resources_counts (hS : Structural vp prims) (qs : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo Q ∧ QuantumResourcesFinal Q ∧
      QFinalResourcesFinal Q qs (Resources2.directCounts vp qs) (finalMemoP2 vp qs) :=
  ⟨slhdsa_euf_cma_final_quantum_all hS Q, resources_counts hS Q qs hQ⟩

theorem slhdsa_suf_cma_final_quantum_all_resources_counts (hS : Structural vp prims) (qs : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo Q ∧ QuantumResourcesFinal Q ∧
      QFinalResourcesFinal Q qs (Resources2.directCounts vp qs) (finalMemoP2 vp qs) :=
  ⟨slhdsa_suf_cma_final_quantum_all hS Q, resources_counts hS Q qs hQ⟩

theorem slhdsa_pure_euf_cma_final_quantum_all_resources_counts (hS : Structural vp prims) (qs : ℕ)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qToInternal Q) ∧
      forgerTraces (qToInternal Q) ⊆ Q.traces ∧
      (∀ pk, ClassicalQueryBound ((qToInternal Q).main pk) (fun i => i.isRight = true) qs) ∧
      QuantumResourcesFinal (qToInternal Q) ∧
      QFinalResourcesFinal (qToInternal Q) qs (Resources2.directCounts vp qs)
        (finalMemoP2 vp qs) :=
  ⟨slhdsa_pure_euf_cma_final_quantum_all hS Q, traces_qToInternal Q,
    qToInternal_queryBound Q qs hQ, resources_counts hS _ qs (qToInternal_queryBound Q qs hQ)⟩

theorem slhdsa_pure_suf_cma_final_quantum_all_resources_counts (hS : Structural vp prims) (qs : ℕ)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qToInternal Q) ∧
      forgerTraces (qToInternal Q) ⊆ Q.traces ∧
      (∀ pk, ClassicalQueryBound ((qToInternal Q).main pk) (fun i => i.isRight = true) qs) ∧
      QuantumResourcesFinal (qToInternal Q) ∧
      QFinalResourcesFinal (qToInternal Q) qs (Resources2.directCounts vp qs)
        (finalMemoP2 vp qs) :=
  ⟨slhdsa_pure_suf_cma_final_quantum_all hS Q, traces_qToInternal Q,
    qToInternal_queryBound Q qs hQ, resources_counts hS _ qs (qToInternal_queryBound Q qs hQ)⟩

theorem slhdsa_bytes_euf_cma_final_quantum_all_resources_counts (hS : Structural vp prims) (qs : ℕ)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist))
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qBytesToTyped Q) ∧
      forgerTraces (qBytesToTyped Q) ⊆ Q.traces ∧
      (∀ pk, ClassicalQueryBound ((qBytesToTyped Q).main pk) (fun i => i.isRight = true) qs) ∧
      QuantumResourcesFinal (qBytesToTyped Q) ∧
      QFinalResourcesFinal (qBytesToTyped Q) qs (Resources2.directCounts vp qs)
        (finalMemoP2 vp qs) :=
  ⟨slhdsa_bytes_euf_cma_final_quantum_all hS Q, traces_qBytesToTyped Q,
    qBytesToTyped_queryBound Q qs hQ, resources_counts hS _ qs (qBytesToTyped_queryBound Q qs hQ)⟩

theorem slhdsa_bytes_suf_cma_final_quantum_all_resources_counts (hS : Structural vp prims) (qs : ℕ)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist))
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qBytesToTyped Q) ∧
      forgerTraces (qBytesToTyped Q) ⊆ Q.traces ∧
      (∀ pk, ClassicalQueryBound ((qBytesToTyped Q).main pk) (fun i => i.isRight = true) qs) ∧
      QuantumResourcesFinal (qBytesToTyped Q) ∧
      QFinalResourcesFinal (qBytesToTyped Q) qs (Resources2.directCounts vp qs)
        (finalMemoP2 vp qs) :=
  ⟨slhdsa_bytes_suf_cma_final_quantum_all hS Q, traces_qBytesToTyped Q,
    qBytesToTyped_queryBound Q qs hQ, resources_counts hS _ qs (qBytesToTyped_queryBound Q qs hQ)⟩

theorem slhdsa_pure_bytes_euf_cma_final_quantum_all_resources_counts (hS : Structural vp prims) (qs : ℕ)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qPureBytesToInternal Q) ∧
      forgerTraces (qPureBytesToInternal Q) ⊆ Q.traces ∧
      (∀ pk, ClassicalQueryBound ((qPureBytesToInternal Q).main pk)
        (fun i => i.isRight = true) qs) ∧
      QuantumResourcesFinal (qPureBytesToInternal Q) ∧
      QFinalResourcesFinal (qPureBytesToInternal Q) qs (Resources2.directCounts vp qs)
        (finalMemoP2 vp qs) :=
  ⟨slhdsa_pure_bytes_euf_cma_final_quantum_all hS Q, traces_qPureBytesToInternal Q,
    qPureBytesToInternal_queryBound Q qs hQ,
    resources_counts hS _ qs (qPureBytesToInternal_queryBound Q qs hQ)⟩

theorem slhdsa_pure_bytes_suf_cma_final_quantum_all_resources_counts (hS : Structural vp prims) (qs : ℕ)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qPureBytesToInternal Q) ∧
      forgerTraces (qPureBytesToInternal Q) ⊆ Q.traces ∧
      (∀ pk, ClassicalQueryBound ((qPureBytesToInternal Q).main pk)
        (fun i => i.isRight = true) qs) ∧
      QuantumResourcesFinal (qPureBytesToInternal Q) ∧
      QFinalResourcesFinal (qPureBytesToInternal Q) qs (Resources2.directCounts vp qs)
        (finalMemoP2 vp qs) :=
  ⟨slhdsa_pure_bytes_suf_cma_final_quantum_all hS Q, traces_qPureBytesToInternal Q,
    qPureBytesToInternal_queryBound Q qs hQ,
    resources_counts hS _ qs (qPureBytesToInternal_queryBound Q qs hQ)⟩

end headlines

end Reduction

#print axioms Reduction.toProbCompWith_qMemoForgeOpen
#print axioms Reduction.qToInternal_queryBound
#print axioms Reduction.qBytesToTyped_queryBound
#print axioms Reduction.qPureBytesToInternal_queryBound
#print axioms Reduction.qToTcr_forge_open
#print axioms Reduction.qToDspr_guess_open
#print axioms Reduction.qMemoForge_open
#print axioms Reduction.qrUd_distinguish_open
#print axioms Reduction.qrPre_invert_open
#print axioms Reduction.qrTcrT_forge_open
#print axioms Reduction.first_phase_qToTcr
#print axioms Reduction.first_phase_qToDspr
#print axioms Reduction.qfinal_resources_final
#print axioms Reduction.qfinal_resources_final_128s
#print axioms Reduction.slhdsa_euf_cma_final_quantum_all_resources_counts
#print axioms Reduction.slhdsa_suf_cma_final_quantum_all_resources_counts
#print axioms Reduction.slhdsa_pure_euf_cma_final_quantum_all_resources_counts
#print axioms Reduction.slhdsa_pure_suf_cma_final_quantum_all_resources_counts
#print axioms Reduction.slhdsa_bytes_euf_cma_final_quantum_all_resources_counts
#print axioms Reduction.slhdsa_bytes_suf_cma_final_quantum_all_resources_counts
#print axioms Reduction.slhdsa_pure_bytes_euf_cma_final_quantum_all_resources_counts
#print axioms Reduction.slhdsa_pure_bytes_suf_cma_final_quantum_all_resources_counts
