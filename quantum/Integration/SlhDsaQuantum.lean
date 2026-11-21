import PQ.Interactive.Games
import PQ.Interactive.EUFCMA
import Reduction.Headline

/-!
# SLH-DSA against quantum forgers: reduction adversaries as quantum machines (integration)

NOT part of the default target; checked like `Integration/SlhDsa.lean` (same `LEAN_PATH`).

For a quantum forger `Q` (rational Born probabilities) this file builds explicit quantum machines
that run `Q` once inside the classical code of the reduction adversaries, and proves that their
quantum advantages are the corresponding terms of `Reduction.boundFinal`:

| term of `boundFinal`            | quantum machine | status |
|---------------------------------|-----------------|--------|
| PRF (`skPrfC`), `bPrfC`         | `qbPrfC Q`      | quantum advantage `qPrfAdvantage` |
| PRF_msg (`msgPrf`), `bPrfMsgL`  | `qbPrfMsgL Q`   | quantum advantage `qPrfAdvantage` |
| ITSR, `bItsrL`                  | `qbItsrL Q`     | quantum advantage `qItsrAdvantage` |
| SM-TCR(`Thash`), `bTcrS`        | `qbTcrS Q`      | quantum advantage `qSM_DT_TCR_Advantage` |
| SM-UD(F), `rUd (bWotsS ·)`      | `qrUd Q`        | quantum advantage `qSM_DT_UD_Advantage` |
| SM-PRE(F), `rPre (bWotsS ·)`    | `qrPre Q`       | quantum advantage `qSM_DT_PRE_Advantage` |
| SM-TCR(F), `rTcr (bWotsS ·)`    | `qrTcr Q`       | quantum advantage `qSM_DT_TCR_Advantage` |
| SM-DSPR(F), `toDspr (bOpenPreS ·)` | `qToDspr Q`  | quantum advantage `qDsprFV_Advantage` |
| SM-TCR(F), `toTcr (bOpenPreS ·)`  | `qToTcr Q`   | quantum advantage `qTcrFV_Advantage` |

`slhdsa_euf_cma_final_quantum_machines` is the resulting statement.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

/-! ## `bPrfC` -/

/-- The quantum machine "`bPrf`'s code around `Q`": the program text of `Reduction.bPrf` with the
harness around the quantum forger in place of `runForger A`. -/
noncomputable def qbPrf (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool :=
  letI : HasQuery (publicHashSpec prims.core)
      (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
    ⟨fun q => pure (PublicHash.impl prims q)⟩
  let secret (pkSeed : prims.PkSeed) (a : Adrs) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y :=
    PRFScheme.functionQuery (pkSeed, a)
  liftQ (monadLift pkSeedDist :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.PkSeed) >>=
    fun pkSeed =>
  liftQ (monadLift ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.SkPrf) >>=
    fun skPrf =>
  liftQ (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core (secret pkSeed)
      pkSeed : OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) >>=
    fun root =>
  qRunForger (Q.main ⟨pkSeed, root⟩) (fun m => do
      let addrnd ← (monadLift (optRand ⟨pkSeed, root⟩) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
      (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core (secret pkSeed) m
        pkSeed root (prims.PRFmsg skPrf addrnd m) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
          (GeneralScheme.SignatureCore vp prims.core))) >>=
    fun r => liftQ (pure (harnessValid (⟨pkSeed, root⟩ : PublicKeyCore prims.core) r.2 r.1.1 r.1.2))

theorem toProbComp_qbPrf (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbComp (qbPrf Q) Q.ρ₀ = bPrf Q.toClassical := by
  unfold qbPrf
  simp only [toProbComp_liftQ_bind, toProbComp_bind_liftQ, toProbComp_qRunForger]
  rfl

theorem rationalBorn_qbPrf (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) : RationalBorn (qbPrf Q) Q.ρ₀ :=
  rationalBorn_liftQ_bind _ _ _ fun _ ↦ rationalBorn_liftQ_bind _ _ _ fun _ ↦
    rationalBorn_liftQ_bind _ _ _ fun _ ↦
      rationalBorn_bind_liftQ _ _ _ (rationalBorn_qRunForger _ _ _ (hQ _))

lemma forwardsUnif0_restrictImpl {D D' V : Type} [Inhabited V] (r : D → Option D') :
    ForwardsUnif0 (Restrict.restrictImpl (V := V) r) := by
  intro n
  change (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (unifSpec + (D' →ₒ V)) _) = _
  rfl

/-- The quantum PRF distinguisher on the secret-key address domain: `qbPrf Q` behind the
domain-restricting wrapper of `bPrfC`. -/
noncomputable def qbPrfC (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) Bool :=
  wrap0 (Restrict.restrictImpl (skRestrict vp prims)) (qbPrf Q)

theorem toProbComp_qbPrfC (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbComp (qbPrfC Q) Q.ρ₀ = bPrfC Q.toClassical := by
  rw [qbPrfC, toProbComp_wrap0 _ (forwardsUnif0_restrictImpl _), toProbComp_qbPrf]
  rfl

theorem rationalBorn_qbPrfC (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) : RationalBorn (qbPrfC Q) Q.ρ₀ :=
  rationalBorn_wrap0 _ _ _ (rationalBorn_qbPrf Q hQ)

/-- The PRF term of the bound is the quantum PRF advantage of the quantum machine `qbPrfC Q`. -/
theorem qPrfAdvantage_qbPrfC (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀ =
      (skPrfC vp prims).prfAdvantage (bPrfC Q.toClassical) := by
  rw [qPrfAdvantage_eq _ _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfC Q hQ),
    toProbComp_qbPrfC]

/-! ## The lazy-cache wrapper `Lazy.lazyRun` -/

section lazy

open Lazy

variable {ι κ : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κ} {D V α : Type}

lemma forwardsUnifB_lazyImplR [DecidableEq D] :
    ForwardsUnifB (lazyImplR (gspec := gspec) (hspec := hspec) (D := D) (V := V)) := by
  intro n t
  simp [lazyImplR]

lemma forwardsUnif0_interp [SampleableType V] (hI : QueryImpl hspec Id) :
    ForwardsUnif0 (interp (gspec := gspec) (V := V) hI) := fun _ ↦ rfl

/-- `Lazy.lazyRun` around a quantum open program: the lazy secret cache and the interpretation of
draws and hash evaluations are classical code around the machine. -/
noncomputable def qLazyRun [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id)
    (X : QOC W (RSpec gspec D V hspec) α) : QOC W (unifSpec + gspec) α :=
  wrap0 (interp hI) (Prod.fst <$> wrap lazyImplR X [])

theorem toProbComp_qLazyRun [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id)
    (X : QOC W (RSpec gspec D V hspec) α) (ρ : Matrix W W ℂ) :
    toProbComp (qLazyRun hI X) ρ = lazyRun hI (toProbComp X ρ) := by
  rw [qLazyRun, toProbComp_wrap0 _ (forwardsUnif0_interp hI), toProbComp_map,
    toProbComp_wrap _ forwardsUnifB_lazyImplR]
  rfl

theorem rationalBorn_qLazyRun [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id)
    (X : QOC W (RSpec gspec D V hspec) α) (ρ : Matrix W W ℂ) (hX : RationalBorn X ρ) :
    RationalBorn (qLazyRun hI X) ρ :=
  rationalBorn_wrap0 _ _ _ (rationalBorn_map _ _ _ (rationalBorn_wrap _ _ _ _ hX))

/-! ## `Lazy.bPrfMsgL` -/

/-- The open program of the `PRF_msg` distinguisher around the quantum forger (`Lazy.msgOpen`). -/
noncomputable def qMsgOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (OSpec prims (msgG prims)) Bool :=
  liftQ (liftM pkSeedDist : OracleComp (OSpec prims (msgG prims)) prims.PkSeed) >>= fun pkSeed =>
  liftQ (openKeygen prims (msgG prims) pkSeed) >>= fun root =>
  qRunForger (Q.main ⟨pkSeed, root⟩) (msgSignO optRand ⟨pkSeed, root⟩) >>= fun z =>
  liftQ (pure (harnessValid (⟨pkSeed, root⟩ : PublicKeyCore prims.core) z.2 z.1.1 z.1.2))

/-- The quantum `PRF_msg` distinguisher "`bPrfMsgL`'s code around `Q`". -/
noncomputable def qbPrfMsgL (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool :=
  qLazyRun (PublicHash.impl prims) (qMsgOpen Q)

theorem toProbComp_qbPrfMsgL (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbComp (qbPrfMsgL Q) Q.ρ₀ = bPrfMsgL Q.toClassical := by
  rw [qbPrfMsgL, toProbComp_qLazyRun]
  unfold qMsgOpen
  simp only [toProbComp_liftQ_bind, toProbComp_bind_liftQ, toProbComp_qRunForger]
  rfl

theorem rationalBorn_qbPrfMsgL (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) : RationalBorn (qbPrfMsgL Q) Q.ρ₀ :=
  rationalBorn_qLazyRun _ _ _ <|
    rationalBorn_liftQ_bind _ _ _ fun _ ↦ rationalBorn_liftQ_bind _ _ _ fun _ ↦
      rationalBorn_bind_liftQ _ _ _ (rationalBorn_qRunForger _ _ _ (hQ _))

/-- The `PRF_msg` term of the bound is the quantum PRF advantage of `qbPrfMsgL Q`. -/
theorem qPrfAdvantage_qbPrfMsgL (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀ =
      (msgPrf vp prims).prfAdvantage (bPrfMsgL Q.toClassical) := by
  rw [qPrfAdvantage_eq _ _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfMsgL Q hQ),
    toProbComp_qbPrfMsgL]

/-! ## `Lazy.bItsrL` -/

/-- The transcript-recording harness (`Reduction.runForgerLog`) around a quantum forger. -/
noncomputable def qRunForgerLog {ι : Type} {spec : OracleSpec ι}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pk : PublicKeyCore prims.core)
    (randomizer : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    QOC W (unifSpec + spec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  wrap ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (G2Log prims) (OracleComp (unifSpec + spec))) +
      logSignOracle optRand pk randomizer signR) (Q.main pk) []

theorem toProbComp_qRunForgerLog {ι : Type} {spec : OracleSpec ι}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pk : PublicKeyCore prims.core)
    (randomizer : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    toProbComp (qRunForgerLog Q pk randomizer signR) Q.ρ₀ =
      runForgerLog Q.toClassical pk randomizer signR :=
  toProbComp_wrap _ (forwardsUnifB_ofLift_add _) _ _ _

/-- The open program of the ITSR adversary around the quantum forger (`Lazy.itsrOpen`). -/
noncomputable def qItsrOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (OSpec prims (itsrG prims)) (prims.Y × ItsrIn prims) :=
  liftQ (liftM pkSeedDist : OracleComp (OSpec prims (itsrG prims)) prims.PkSeed) >>= fun pkSeed =>
  liftQ (openKeygen prims (itsrG prims) pkSeed) >>= fun root =>
  qRunForgerLog Q ⟨pkSeed, root⟩ (itsrRandomizerO pkSeed root)
    (fun m R => Lazy.openSign prims (itsrG prims) m pkSeed root R) >>= fun z =>
  liftQ (pure (z.1.2.randomness, (pkSeed, root, z.1.1)))

/-- The quantum ITSR adversary "`bItsrL`'s code around `Q`". -/
noncomputable def qbItsrL (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (unifSpec + KeyedHash.ITSRTargetSpec (ItsrIn prims) prims.Y) (prims.Y × ItsrIn prims) :=
  qLazyRun (PublicHash.impl prims) (qItsrOpen Q)

theorem toProbComp_qbItsrL (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbComp (qbItsrL Q) Q.ρ₀ = (bItsrL Q.toClassical).main := by
  rw [qbItsrL, toProbComp_qLazyRun]
  unfold qItsrOpen
  simp only [toProbComp_liftQ_bind, toProbComp_bind_liftQ, toProbComp_qRunForgerLog]
  rfl

theorem rationalBorn_qbItsrL (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) : RationalBorn (qbItsrL Q) Q.ρ₀ :=
  rationalBorn_qLazyRun _ _ _ <|
    rationalBorn_liftQ_bind _ _ _ fun _ ↦ rationalBorn_liftQ_bind _ _ _ fun _ ↦
      rationalBorn_bind_liftQ _ _ _ (rationalBorn_wrap _ _ _ _ (hQ _))

/-- The ITSR term of the bound is the quantum ITSR advantage of `qbItsrL Q`. -/
theorem qItsrAdvantage_qbItsrL (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ =
      KeyedHash.ITSRAdvantage (bItsrL Q.toClassical) := by
  rw [qItsrAdvantage_eq _ _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbItsrL Q hQ),
    toProbComp_qbItsrL]

end lazy

/-! ## `Lazy.bTcrS` (two-phase SM-DT-TCR game) -/

/-- The quantum SM-DT-TCR adversary "`bTcrS`'s code around `Q`".  The `choose` phase of `bTcrS`
does not run the forger (it registers the hash calls of the key structure of a sampled sparse
table); the quantum forger runs once, in the `forge` phase, against the `G2` signing oracle of the
table, and the collision is extracted classically from its forgery.  The state carried across the
phases is the classical table. -/
noncomputable def qbTcrS (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QSM_DT_TCR_Adversary W (tcrProblem vp prims pkSeedDist) where
  State := SecretTable vp prims
  choose := (Lazy.bTcrS Q.toClassical).choose
  forge tbl pkSeed :=
    close ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
        g2SignOracle optRand (idealPk vp prims tbl pkSeed)
          (fun m R => idealSign vp prims tbl m (idealPk vp prims tbl pkSeed) R))
      (Q.main (idealPk vp prims tbl pkSeed)) [] >>= fun r =>
    liftU (pure ((findCollision pkSeed (honestCalls tbl pkSeed)
      (verifyCalls (idealPk vp prims tbl pkSeed) r.1.1 r.1.2)).getD (0, [])))
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

theorem toClassical_qbTcrS (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qbTcrS Q).toClassical = Lazy.bTcrS Q.toClassical := by
  have hforge : ∀ tbl pkSeed, (qbTcrS Q).toClassical.forge tbl pkSeed =
      (Lazy.bTcrS Q.toClassical).forge tbl pkSeed := by
    intro tbl pkSeed
    change toProbCompC (_ >>= fun r => liftU _) Q.ρ₀ = _
    rw [toProbCompC_bind_liftU, toProbCompC_close _ (forwardsUnif_ofLift_add _)]
    rfl
  change TweakableHash.SM_DT_TCR_Adversary.mk _ _ _ = TweakableHash.SM_DT_TCR_Adversary.mk _ _ _
  congr 1
  funext tbl pkSeed
  exact hforge tbl pkSeed

theorem rationalBorn_qbTcrS (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) : RationalBorn ((qbTcrS Q).forge tbl pkSeed) (qbTcrS Q).ρ₀ :=
  rationalBorn_bind_liftU _ _ _ (rationalBorn_close _ _ _ _ (hQ _))

/-- The SM-TCR(`Thash`) term of the bound is the quantum SM-DT-TCR advantage of `qbTcrS Q`. -/
theorem qSM_DT_TCR_Advantage_qbTcrS (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qSM_DT_TCR_Advantage (qbTcrS Q) = TweakableHash.SM_DT_TCR_Advantage (Lazy.bTcrS Q.toClassical) := by
  rw [qSM_DT_TCR_Advantage_eq _ (rationalBorn_qbTcrS Q hQ), toClassical_qbTcrS]

/-! ## The WOTS reductions `rUd`, `rPre`, `rTcr` of `Lazy.bWotsS` -/

/-- The `forge` phase of `Lazy.bWotsS` around the quantum forger: `Q` is run once against the `G2`
signing oracle that signs from the recorded history, and the WOTS forgery is extracted
classically. -/
noncomputable def qWotsForge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) (pkSeed : prims.PkSeed) :
    Closed W (ℕ × prims.Y × WotsSig vp.params prims.core) :=
  close ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
      g2SignOracle optRand ⟨pkSeed, st.2.2⟩ (signFromHist st.1 st.2.1 ⟨pkSeed, st.2.2⟩))
    (Q.main ⟨pkSeed, st.2.2⟩) [] >>= fun r =>
  liftU (pure (wotsAnswer st.1 st.2.1 ⟨pkSeed, st.2.2⟩ r.1.1 r.1.2))

theorem toProbCompC_qWotsForge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) (pkSeed : prims.PkSeed) :
    toProbCompC (qWotsForge Q st pkSeed) Q.ρ₀ = (Lazy.bWotsS Q.toClassical).forge st pkSeed := by
  rw [qWotsForge, toProbCompC_bind_liftU, toProbCompC_close _ (forwardsUnif_ofLift_add _)]
  rfl

theorem rationalBorn_qWotsForge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀)
    (st : SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) (pkSeed : prims.PkSeed) :
    RationalBorn (qWotsForge Q st pkSeed) Q.ρ₀ :=
  rationalBorn_bind_liftU _ _ _ (rationalBorn_close _ _ _ _ (hQ _))

/-- The quantum SM-TCR(F) adversary "`rTcr (bWotsS ·)`'s code around `Q`". -/
noncomputable def qrTcr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QSM_DT_TCR_Adversary W (wotsTcrProblem vp prims pkSeedDist) where
  State := (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
    List (WotsGame.Entry prims)
  choose := (rTcr pkSeedDist (Lazy.bWotsS Q.toClassical)).choose
  forge st pk := qWotsForge Q st.1 pk >>= fun x => liftU (pure (tcrAnswer pk st.2 x.1 x.2.1 x.2.2))
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

theorem toClassical_qrTcr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qrTcr Q).toClassical = rTcr pkSeedDist (Lazy.bWotsS Q.toClassical) := by
  have hforge : ∀ st pk, (qrTcr Q).toClassical.forge st pk =
      (rTcr pkSeedDist (Lazy.bWotsS Q.toClassical)).forge st pk := by
    intro st pk
    change toProbCompC (_ >>= fun x => liftU _) Q.ρ₀ = _
    rw [toProbCompC_bind_liftU, toProbCompC_qWotsForge]
    rfl
  change TweakableHash.SM_DT_TCR_Adversary.mk _ _ _ = TweakableHash.SM_DT_TCR_Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hforge st pk

theorem qSM_DT_TCR_Advantage_qrTcr (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qSM_DT_TCR_Advantage (qrTcr Q) =
      TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (Lazy.bWotsS Q.toClassical)) := by
  rw [qSM_DT_TCR_Advantage_eq (qrTcr Q) fun (st : (SecretTable vp prims ×
        List (WotsGame.Entry prims) × prims.Y) × List (WotsGame.Entry prims)) pk ↦
      rationalBorn_bind_liftU _ _ _ (rationalBorn_qWotsForge Q hQ st.1 pk),
    toClassical_qrTcr]

/-- The quantum SM-PRE(F) adversary "`rPre (bWotsS ·)`'s code around `Q`". -/
noncomputable def qrPre (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QSM_DT_PRE_Adversary W (wotsPreProblem vp prims pkSeedDist) where
  State := (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
    List (WotsGame.Entry prims)
  choose := (rPre pkSeedDist (Lazy.bWotsS Q.toClassical)).choose
  invert st pk := qWotsForge Q st.1 pk >>= fun x => liftU (pure (preAnswer pk st.2 x.1 x.2.1 x.2.2))
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

theorem toClassical_qrPre (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qrPre Q).toClassical = rPre pkSeedDist (Lazy.bWotsS Q.toClassical) := by
  have hinv : ∀ st pk, (qrPre Q).toClassical.invert st pk =
      (rPre pkSeedDist (Lazy.bWotsS Q.toClassical)).invert st pk := by
    intro st pk
    change toProbCompC (_ >>= fun x => liftU _) Q.ρ₀ = _
    rw [toProbCompC_bind_liftU, toProbCompC_qWotsForge]
    rfl
  change TweakableHash.SM_DT_PRE_Adversary.mk _ _ _ = TweakableHash.SM_DT_PRE_Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hinv st pk

theorem qSM_DT_PRE_Advantage_qrPre (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qSM_DT_PRE_Advantage (qrPre Q) =
      TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS Q.toClassical)) := by
  rw [qSM_DT_PRE_Advantage_eq (qrPre Q) fun (st : (SecretTable vp prims ×
        List (WotsGame.Entry prims) × prims.Y) × List (WotsGame.Entry prims)) pk ↦
      rationalBorn_bind_liftU _ _ _ (rationalBorn_qWotsForge Q hQ st.1 pk),
    toClassical_qrPre]

/-- The quantum SM-UD(F) adversary "`rUd (bWotsS ·)`'s code around `Q`". -/
noncomputable def qrUd (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QSM_DT_UD_Adversary W (wotsUdProblem vp prims pkSeedDist) where
  State := (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
    List (WotsGame.Entry prims)
  pick := (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)).pick
  distinguish st pk :=
    qWotsForge Q st.1 pk >>= fun x => liftU (pure (WotsGame.win pk st.2 x.1 x.2.1 x.2.2))
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

theorem toClassical_qrUd (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qrUd Q).toClassical = rUd pkSeedDist (Lazy.bWotsS Q.toClassical) := by
  have hd : ∀ st pk, (qrUd Q).toClassical.distinguish st pk =
      (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)).distinguish st pk := by
    intro st pk
    change toProbCompC (_ >>= fun x => liftU _) Q.ρ₀ = _
    rw [toProbCompC_bind_liftU, toProbCompC_qWotsForge]
    rfl
  change TweakableHash.SM_DT_UD_Adversary.mk _ _ _ = TweakableHash.SM_DT_UD_Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hd st pk

theorem qSM_DT_UD_Advantage_qrUd (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qSM_DT_UD_Advantage (qrUd Q) =
      TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)) := by
  rw [qSM_DT_UD_Advantage_eq (qrUd Q) fun (st : (SecretTable vp prims ×
        List (WotsGame.Entry prims) × prims.Y) × List (WotsGame.Entry prims)) pk ↦
      rationalBorn_bind_liftU _ _ _ (rationalBorn_qWotsForge Q hQ st.1 pk),
    toClassical_qrUd]

/-! ## The FORS reductions `toDspr`, `toTcr` of `Lazy.bOpenPreS` -/

open TweakableHash in
/-- The `find` phase of `Lazy.bOpenPreS` around the quantum forger. -/
noncomputable def qOpenPreFind (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    QOC W (unifSpec + SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y) (ℕ × prims.Y) :=
  qRunForgerLog Q (idealPk vp prims tbl pkSeed) lazyRandomizerLift
      (openSign (idealPk vp prims tbl pkSeed) tbl ys) >>= fun z =>
    liftQ (pure (openPreAnswer (idealPk vp prims tbl pkSeed) ys z.2 z.1.1 z.1.2))

theorem toProbComp_qOpenPreFind (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    toProbComp (qOpenPreFind Q tbl pkSeed ys) Q.ρ₀ =
      (Lazy.bOpenPreS Q.toClassical).find tbl pkSeed ys := by
  rw [qOpenPreFind, toProbComp_bind_liftQ, toProbComp_qRunForgerLog]
  rfl

open TweakableHash in
/-- The second phase shared by `toDspr` and `toTcr`: the `find` phase run against the simulated
opening oracle (answers from the sampled targets, opened indices recorded). -/
noncomputable def qFindRun (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pkSeed : prims.PkSeed) : Closed W ((ℕ × prims.Y) × List ℕ) :=
  close (SM_DT_OpenPRE_SourceFinalValidity.findOracles st.2.1)
    (qOpenPreFind Q st.1 pkSeed st.2.2) []

open TweakableHash in
theorem toProbCompC_qFindRun (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pkSeed : prims.PkSeed) :
    toProbCompC (qFindRun Q st pkSeed) Q.ρ₀ =
      (simulateQ (SM_DT_OpenPRE_SourceFinalValidity.findOracles st.2.1)
        ((Lazy.bOpenPreS Q.toClassical).find st.1 pkSeed st.2.2)).run [] := by
  have hf : ForwardsUnif (SM_DT_OpenPRE_SourceFinalValidity.findOracles (M := prims.Y) st.2.1) :=
    forwardsUnif_ofLift_add _
  rw [qFindRun, toProbCompC_close _ hf, toProbComp_qOpenPreFind]

theorem rationalBorn_qFindRun (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀)
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pkSeed : prims.PkSeed) : RationalBorn (qFindRun Q st pkSeed) Q.ρ₀ :=
  rationalBorn_close _ _ _ _
    (rationalBorn_bind_liftQ _ _ _ (rationalBorn_wrap _ _ _ _ (hQ _)))

/-- The quantum SM-TCR(F) adversary "`toTcr (bOpenPreS ·)`'s code around `Q`". -/
noncomputable def qToTcr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QTcrFV_Adversary W (forsTcrProblem vp prims pkSeedDist) where
  State := SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y
  choose := (toTcr (Lazy.bOpenPreS Q.toClassical)).choose
  forge st pk := qFindRun Q st pk >>= fun r => liftU (pure (r.1.1, r.1.2))
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

theorem toClassical_qToTcr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qToTcr Q).toClassical = toTcr (Lazy.bOpenPreS Q.toClassical) := by
  have hforge : ∀ (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y) pk, (qToTcr Q).toClassical.forge st pk =
      (toTcr (Lazy.bOpenPreS Q.toClassical)).forge st pk := by
    intro st pk
    change toProbCompC (_ >>= fun r => liftU _) Q.ρ₀ = _
    rw [toProbCompC_bind_liftU, toProbCompC_qFindRun]
    rfl
  change TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary.mk _ _ _ =
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hforge st pk

theorem qTcrFV_Advantage_qToTcr (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qTcrFV_Advantage (qToTcr Q) =
      TweakableHash.SM_DT_TCR_SourceFinalValidity.advantage
        (toTcr (Lazy.bOpenPreS Q.toClassical)) := by
  rw [qTcrFV_Advantage_eq (qToTcr Q) fun (st : SecretTable vp prims ×
        List (prims.AdrsKey × prims.Y) × List prims.Y) pk ↦
      rationalBorn_bind_liftU _ _ _ (rationalBorn_qFindRun Q hQ st pk),
    toClassical_qToTcr]

/-- The quantum SM-DSPR(F) adversary "`toDspr (bOpenPreS ·)`'s code around `Q`". -/
noncomputable def qToDspr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QDsprFV_Adversary W (forsDsprProblem vp prims pkSeedDist) where
  State := SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y
  choose := (toDspr (Lazy.bOpenPreS Q.toClassical)).choose
  guess st pk := qFindRun Q st pk >>= fun r =>
    liftU (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨
      r.1.1 ∈ r.2)))
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

theorem toClassical_qToDspr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qToDspr Q).toClassical = toDspr (Lazy.bOpenPreS Q.toClassical) := by
  have hguess : ∀ (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y) pk, (qToDspr Q).toClassical.guess st pk =
      (toDspr (Lazy.bOpenPreS Q.toClassical)).guess st pk := by
    intro st pk
    change toProbCompC (_ >>= fun r => liftU _) Q.ρ₀ = _
    rw [toProbCompC_bind_liftU, toProbCompC_qFindRun]
    rfl
  change TweakableHash.SM_DT_DSPR_SourceFinalValidity.Adversary.mk _ _ _ =
    TweakableHash.SM_DT_DSPR_SourceFinalValidity.Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hguess st pk

theorem qDsprFV_Advantage_qToDspr (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qDsprFV_Advantage (qToDspr Q) =
      TweakableHash.SM_DT_DSPR_SourceFinalValidity.advantage
        (toDspr (Lazy.bOpenPreS Q.toClassical)) := by
  rw [qDsprFV_Advantage_eq (qToDspr Q) fun (st : SecretTable vp prims ×
        List (prims.AdrsKey × prims.Y) × List prims.Y) pk ↦
      rationalBorn_bind_liftU _ _ _ (rationalBorn_qFindRun Q hQ st pk),
    toClassical_qToDspr]

/-! ## The bound with quantum advantages -/

/-- **Standard-model EUF-CMA security of SLH-DSA against quantum forgers, with every reduction
adversary a quantum machine.**  For every quantum forger `Q` with classical signing queries and
rational Born probabilities, the quantum EUF-CMA advantage is bounded by the nine terms of
`Reduction.boundFinal`, each of them the QUANTUM advantage (Born probabilities, `qWeight`) of an
explicit quantum machine that runs `Q` once inside the classical code of the corresponding
reduction adversary:

`qbPrfC Q` (PRF on `SkAdrs`), `qbPrfMsgL Q` (PRF_msg), `qbItsrL Q` (ITSR), `qToDspr Q` (SM-DSPR(F)),
`qToTcr Q` (SM-TCR(F), FORS leaves), `qbTcrS Q` (SM-TCR(`Thash`)), `qrUd Q` (SM-UD(F)), `qrPre Q`
(SM-PRE(F)), `qrTcr Q` (SM-TCR(F), WOTS chains). -/
theorem slhdsa_euf_cma_final_quantum_machines (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q ≤
      qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀ +
        qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀ +
        qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
        (qDsprFV_Advantage (qToDspr Q) + 3 * qTcrFV_Advantage (qToTcr Q)) +
        qSM_DT_TCR_Advantage (qbTcrS Q) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_Advantage (qrUd Q) +
        qSM_DT_PRE_Advantage (qrPre Q) +
        qSM_DT_TCR_Advantage (qrTcr Q) := by
  have h := qUnforgeableAdvantage_le_of_forall Q hQ betaEufFinal (slhdsa_euf_cma_final' hS)
  rw [qPrfAdvantage_qbPrfC Q hQ, qPrfAdvantage_qbPrfMsgL Q hQ, qItsrAdvantage_qbItsrL Q hQ,
    qDsprFV_Advantage_qToDspr Q hQ, qTcrFV_Advantage_qToTcr Q hQ,
    qSM_DT_TCR_Advantage_qbTcrS Q hQ, qSM_DT_UD_Advantage_qrUd Q hQ,
    qSM_DT_PRE_Advantage_qrPre Q hQ, qSM_DT_TCR_Advantage_qrTcr Q hQ]
  exact h

end Reduction

#print axioms Reduction.toProbComp_qbPrfC
#print axioms Reduction.qPrfAdvantage_qbPrfC
#print axioms Reduction.qPrfAdvantage_qbPrfMsgL
#print axioms Reduction.qItsrAdvantage_qbItsrL
#print axioms Reduction.qSM_DT_TCR_Advantage_qbTcrS
#print axioms Reduction.slhdsa_euf_cma_final_quantum_machines
#print axioms Reduction.qSM_DT_UD_Advantage_qrUd
#print axioms Reduction.qSM_DT_PRE_Advantage_qrPre
#print axioms Reduction.qSM_DT_TCR_Advantage_qrTcr
#print axioms Reduction.qDsprFV_Advantage_qToDspr
#print axioms Reduction.qTcrFV_Advantage_qToTcr
