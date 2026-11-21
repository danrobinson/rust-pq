import Integration.SlhDsaQuantum
import Reduction.TightCapsHeadline

/-!
# SLH-DSA against quantum forgers: the tight-cap headlines with quantum reduction adversaries

NOT part of the default target; checked by `scripts/check-integration.sh`.

Quantum-machine versions of the four tight-cap headline theorems of
`security/Reduction/TightCapsHeadline.lean`:

* `slhdsa_euf_cma_final_tight_quantum` (internal scheme, EUF-CMA),
* `slhdsa_suf_cma_final_tight_quantum` (internal scheme, SUF-CMA),
* `slhdsa_pure_euf_cma_final_tight_quantum`, `slhdsa_pure_suf_cma_final_tight_quantum`
  (external pure interface with context strings).

In each of them every one of the twelve right-hand terms is the quantum advantage (Born weights,
`qWeight`) of an explicit quantum machine that runs the quantum forger once inside the classical
code of the corresponding reduction adversary (`qBoundTight`).  Hypothesis: the Born
probabilities of the forger are rational (`RationalBorn`).

New machines of this file (the others are in `Integration/SlhDsaQuantum.lean`):

* `qbPrfWC w Q`, `qbPrfMsgWL w Q` — the PRF distinguishers of the SUF-CMA proof (final check
  `w`, signature-logging harness `runForgerSig`);
* `qbTcrArST n Q` — the arity-`n` SM-TCR adversary at the tight cap (`bTcrArST n`);
* `qrTcrT Q` — the WOTS-chain SM-TCR adversary at the tight cap (`rTcrT`);
* `qToInternal Q` — the external-to-internal wrapper `toInternal` around a quantum forger
  against the external scheme (a quantum forger against the internal scheme).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive
open scoped ComplexOrder

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

/-! ## The PRF distinguishers of the SUF-CMA proof -/

/-- The signature-logging harness (`Reduction.runForgerSig`) around a quantum forger. -/
noncomputable def qRunForgerSig {ι : Type} {spec : OracleSpec ι}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    QOC W (unifSpec + spec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × SigLog vp prims) :=
  wrap ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (SigLog vp prims) (OracleComp (unifSpec + spec))) +
      sigSignOracle sign) (Q.main pk) []

theorem toProbComp_qRunForgerSig {ι : Type} {spec : OracleSpec ι}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    toProbComp (qRunForgerSig Q pk sign) Q.ρ₀ = runForgerSig Q.toClassical pk sign :=
  toProbComp_wrap _ (forwardsUnifB_ofLift_add _) _ _ _

/-- The quantum machine "`bPrfW w`'s code around `Q`". -/
noncomputable def qbPrfW (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
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
  qRunForgerSig Q ⟨pkSeed, root⟩ (fun m => do
      let addrnd ← (monadLift (optRand ⟨pkSeed, root⟩) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
      (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core (secret pkSeed) m
        pkSeed root (prims.PRFmsg skPrf addrnd m) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
          (GeneralScheme.SignatureCore vp prims.core))) >>=
    fun z => liftQ (pure (w (⟨pkSeed, root⟩ : PublicKeyCore prims.core) z.1 z.2))

theorem toProbComp_qbPrfW (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbComp (qbPrfW w Q) Q.ρ₀ = bPrfW w Q.toClassical := by
  unfold qbPrfW
  simp only [toProbComp_liftQ_bind, toProbComp_bind_liftQ, toProbComp_qRunForgerSig]
  rfl

theorem rationalBorn_qbPrfW (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) : RationalBorn (qbPrfW w Q) Q.ρ₀ :=
  rationalBorn_liftQ_bind _ _ _ fun _ ↦ rationalBorn_liftQ_bind _ _ _ fun _ ↦
    rationalBorn_liftQ_bind _ _ _ fun _ ↦
      rationalBorn_bind_liftQ _ _ _ (rationalBorn_wrap _ _ _ _ (hQ _))

/-- The quantum PRF distinguisher of the SUF-CMA proof on the secret-key address domain. -/
noncomputable def qbPrfWC (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) Bool :=
  wrap0 (Restrict.restrictImpl (skRestrict vp prims)) (qbPrfW w Q)

theorem toProbComp_qbPrfWC (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbComp (qbPrfWC w Q) Q.ρ₀ = bPrfWC w Q.toClassical := by
  rw [qbPrfWC, toProbComp_wrap0 _ (forwardsUnif0_restrictImpl _), toProbComp_qbPrfW]
  rfl

theorem qPrfAdvantage_qbPrfWC (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qPrfAdvantage (skPrfC vp prims) (qbPrfWC w Q) Q.ρ₀ =
      (skPrfC vp prims).prfAdvantage (bPrfWC w Q.toClassical) := by
  have hR : RationalBorn (qbPrfWC w Q) Q.ρ₀ :=
    rationalBorn_wrap0 _ _ _ (rationalBorn_qbPrfW w Q hQ)
  rw [qPrfAdvantage_eq _ _ _ Q.posSemidef Q.trace_eq_one hR, toProbComp_qbPrfWC]

section lazy

open Lazy

/-- The open program of the `PRF_msg` distinguisher of the SUF-CMA proof around the quantum
forger (`Lazy.msgOpenW`). -/
noncomputable def qMsgOpenW (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (OSpec prims (msgG prims)) Bool :=
  liftQ (liftM pkSeedDist : OracleComp (OSpec prims (msgG prims)) prims.PkSeed) >>= fun pkSeed =>
  liftQ (openKeygen prims (msgG prims) pkSeed) >>= fun root =>
  qRunForgerSig Q ⟨pkSeed, root⟩ (msgSignO optRand ⟨pkSeed, root⟩) >>= fun z =>
  liftQ (pure (w (⟨pkSeed, root⟩ : PublicKeyCore prims.core) z.1 z.2))

/-- The quantum `PRF_msg` distinguisher of the SUF-CMA proof. -/
noncomputable def qbPrfMsgWL (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QOC W (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool :=
  qLazyRun (PublicHash.impl prims) (qMsgOpenW w Q)

theorem toProbComp_qbPrfMsgWL (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbComp (qbPrfMsgWL w Q) Q.ρ₀ = bPrfMsgWL w Q.toClassical := by
  rw [qbPrfMsgWL, toProbComp_qLazyRun]
  unfold qMsgOpenW
  simp only [toProbComp_liftQ_bind, toProbComp_bind_liftQ, toProbComp_qRunForgerSig]
  rfl

theorem qPrfAdvantage_qbPrfMsgWL (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qPrfAdvantage (msgPrf vp prims) (qbPrfMsgWL w Q) Q.ρ₀ =
      (msgPrf vp prims).prfAdvantage (bPrfMsgWL w Q.toClassical) := by
  have hR : RationalBorn (qbPrfMsgWL w Q) Q.ρ₀ :=
    rationalBorn_qLazyRun _ _ _ <|
      rationalBorn_liftQ_bind _ _ _ fun _ ↦ rationalBorn_liftQ_bind _ _ _ fun _ ↦
        rationalBorn_bind_liftQ _ _ _ (rationalBorn_wrap _ _ _ _ (hQ _))
  rw [qPrfAdvantage_eq _ _ _ Q.posSemidef Q.trace_eq_one hR, toProbComp_qbPrfMsgWL]

end lazy

/-! ## The per-arity SM-TCR adversaries at the tight caps -/

theorem toProbCompC_qbTcrS_forge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    toProbCompC ((qbTcrS Q).forge tbl pkSeed) Q.ρ₀ =
      (Lazy.bTcrS Q.toClassical).forge tbl pkSeed := by
  change toProbCompC (_ >>= fun r => liftU _) Q.ρ₀ = _
  rw [toProbCompC_bind_liftU, toProbCompC_close _ (forwardsUnif_ofLift_add _)]
  rfl

/-- The classical re-indexing of a collision into the class `P` performed by
`TcrSplit.restrict` after the forge phase. -/
def restrictAnswer {Tweak Y : Type} (P : List Y → Prop) [DecidablePred P]
    (d : {xs : List Y // P xs}) (L : List (Tweak × List Y)) (jm : ℕ × List Y) :
    ℕ × {xs : List Y // P xs} :=
  match L[jm.1]? with
  | some q => if h : P q.2 ∧ P jm.2 then (TcrSplit.classIdx P L jm.1, ⟨jm.2, h.2⟩)
      else (L.length, d)
  | none => (L.length, d)

theorem restrict_forge {PkSeed Tweak Y : Type} [DecidableEq Tweak]
    {th : TweakableHash PkSeed Tweak (List Y) Y} {N : ℕ} (P : List Y → Prop) [DecidablePred P]
    (d : {xs : List Y // P xs}) (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N))
    (s : B.State × List (Tweak × List Y)) (pk : PkSeed) :
    (TcrSplit.restrict P d B).forge s pk =
      B.forge s.1 pk >>= fun jm => pure (restrictAnswer P d s.2 jm) := rfl

/-- A quantum two-phase SM-DT-TCR adversary from a classical one: the classical state type and
`choose` phase are kept, the `forge` phase is replaced by a quantum machine. -/
def qTcrOfClassical {ι PkSeed Tweak M Y : Type} {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (B : SM_DT_TCR_Adversary P) (qf : B.State → PkSeed → Closed W (ℕ × M))
    (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1) : QSM_DT_TCR_Adversary W P where
  State := B.State
  choose := B.choose
  forge := qf
  ρ₀ := ρ₀
  posSemidef := h₁
  trace_eq_one := h₂

/-- If the quantum `forge` phase classicalises to the `forge` phase of `B`, the classical
strategy of `qTcrOfClassical B …` is `B`. -/
theorem toClassical_qTcrOfClassical {ι PkSeed Tweak M Y : Type}
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (B : SM_DT_TCR_Adversary P)
    (qf : B.State → PkSeed → Closed W (ℕ × M)) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef)
    (h₂ : ρ₀.trace = 1) (h : ∀ st pk, toProbCompC (qf st pk) ρ₀ = B.forge st pk) :
    (qTcrOfClassical B qf ρ₀ h₁ h₂).toClassical = B := by
  obtain ⟨S, c, f⟩ := B
  have : (fun st pk => toProbCompC (qf st pk) ρ₀) = f := funext fun st => funext fun pk => h st pk
  simp only [qTcrOfClassical, QSM_DT_TCR_Adversary.toClassical, this]

/-- The `forge` phase of the quantum arity-`n` adversary: the quantum forge phase of `qbTcrS Q`
followed by the classical re-indexing of the collision into the arity class. -/
noncomputable def qTcrArForge (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    Closed W (ℕ × {xs : List prims.Y // xs.length = n}) :=
  (qbTcrS Q).forge s.1 pk >>= fun jm =>
    liftU (pure (restrictAnswer (fun xs : List prims.Y => xs.length = n) (arityDefault prims n)
      s.2 jm))

theorem toProbCompC_qTcrArForge (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    toProbCompC (qTcrArForge n Q s pk) Q.ρ₀ = (bTcrArST n Q.toClassical).forge s pk := by
  rw [qTcrArForge, toProbCompC_bind_liftU, toProbCompC_qbTcrS_forge, bTcrArST_forge]
  exact (restrict_forge (fun xs : List prims.Y => xs.length = n) (arityDefault prims n)
    (Lazy.bTcrS Q.toClassical) s pk).symm

/-- The quantum arity-`n` SM-TCR adversary at the tight cap, "`bTcrArST n`'s code around `Q`":
the classical `choose` phase of `bTcrArST n` (the routing wrapper of `TcrSplit.restrict` around
the `choose` phase of `bTcrS`, which does not run the forger), and the quantum `forge` phase
`qTcrArForge n Q`. -/
noncomputable def qbTcrArST (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QSM_DT_TCR_Adversary W (thashArityProblemT vp prims pkSeedDist n) :=
  qTcrOfClassical (bTcrArST n Q.toClassical) (fun s pk => qTcrArForge n Q s pk) Q.ρ₀
    Q.posSemidef Q.trace_eq_one

theorem toClassical_qbTcrArST (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qbTcrArST n Q).toClassical = bTcrArST n Q.toClassical :=
  toClassical_qTcrOfClassical _ _ _ _ _ fun s pk => toProbCompC_qTcrArForge n Q s pk

theorem qSM_DT_TCR_Advantage_qbTcrArST (n : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qSM_DT_TCR_Advantage (qbTcrArST n Q) = SM_DT_TCR_Advantage (bTcrArST n Q.toClassical) := by
  have hR : ∀ st pk, RationalBorn ((qbTcrArST n Q).forge st pk) (qbTcrArST n Q).ρ₀ :=
    fun st pk ↦ rationalBorn_bind_liftU _ _ _
      (rationalBorn_qbTcrS Q hQ (st : SecretTable vp prims × _).1 pk)
  rw [qSM_DT_TCR_Advantage_eq (qbTcrArST n Q) hR, toClassical_qbTcrArST]

/-- The quantum WOTS-chain SM-TCR(F) adversary at the tight cap, "`rTcrT (bWotsS ·)`'s code
around `Q`" (the program of `qrTcr Q`, typed against `wotsTcrProblemT`). -/
noncomputable def qrTcrT (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QSM_DT_TCR_Adversary W (wotsTcrProblemT vp prims pkSeedDist) where
  State := (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
    List (WotsGame.Entry prims)
  choose := (rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical)).choose
  forge st pk := qWotsForge Q st.1 pk >>= fun x => liftU (pure (tcrAnswer pk st.2 x.1 x.2.1 x.2.2))
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

theorem toClassical_qrTcrT (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qrTcrT Q).toClassical = rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical) := by
  have hforge : ∀ (st : (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
        List (WotsGame.Entry prims)) pk,
      (qrTcrT Q).toClassical.forge st pk =
        (rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical)).forge st pk := by
    intro st pk
    change toProbCompC (_ >>= fun x => liftU _) Q.ρ₀ = _
    rw [toProbCompC_bind_liftU, toProbCompC_qWotsForge]
    rfl
  change SM_DT_TCR_Adversary.mk _ _ _ = SM_DT_TCR_Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hforge st pk

theorem qSM_DT_TCR_Advantage_qrTcrT (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qSM_DT_TCR_Advantage (qrTcrT Q) =
      SM_DT_TCR_Advantage (rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical)) := by
  rw [qSM_DT_TCR_Advantage_eq (qrTcrT Q) fun (st : (SecretTable vp prims ×
        List (WotsGame.Entry prims) × prims.Y) × List (WotsGame.Entry prims)) pk ↦
      rationalBorn_bind_liftU _ _ _ (rationalBorn_qWotsForge Q hQ st.1 pk),
    toClassical_qrTcrT]

/-! ## The bound with quantum advantages -/

/-- The tight-cap bound with every term a quantum advantage of an explicit quantum machine
running `Q` once; `P₁`, `P₂` are the two PRF terms (they differ between EUF-CMA and SUF-CMA).
Twelve terms: PRF, PRF_msg, ITSR, SM-DSPR(F), 3·SM-TCR(F) (FORS leaves), SM-TCR on `F`, `H`,
`T_len`, `T_k` (arity classes, tight caps), (w−2)·SM-UD(F), SM-PRE(F), SM-TCR(F) (WOTS chains,
tight cap). -/
noncomputable def qBoundTight (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (P₁ P₂ : ℝ≥0∞) : ℝ≥0∞ :=
  P₁ + P₂ +
    qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
    (qDsprFV_Advantage (qToDspr Q) + 3 * qTcrFV_Advantage (qToTcr Q)) +
    (qSM_DT_TCR_Advantage (qbTcrArST 1 Q) + qSM_DT_TCR_Advantage (qbTcrArST 2 Q) +
      qSM_DT_TCR_Advantage (qbTcrArST vp.params.len Q) +
      qSM_DT_TCR_Advantage (qbTcrArST vp.params.k Q)) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_Advantage (qrUd Q) +
    qSM_DT_PRE_Advantage (qrPre Q) +
    qSM_DT_TCR_Advantage (qrTcrT Q)

/-- The EUF-CMA bound: `qBoundTight` with the PRF distinguishers `qbPrfC Q`, `qbPrfMsgL Q`. -/
noncomputable def qBetaEufTight (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    ℝ≥0∞ :=
  qBoundTight Q (qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀)
    (qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀)

/-- The SUF-CMA bound: `qBoundTight` with the PRF distinguishers `qbPrfWC sufCheck Q`,
`qbPrfMsgWL sufCheck Q`. -/
noncomputable def qBetaSufTight (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    ℝ≥0∞ :=
  qBoundTight Q (qPrfAdvantage (skPrfC vp prims) (qbPrfWC sufCheck Q) Q.ρ₀)
    (qPrfAdvantage (msgPrf vp prims) (qbPrfMsgWL sufCheck Q) Q.ρ₀)

/-- The classical tight bound at the classical strategy of `Q` is the quantum bound: all twelve
terms are converted. -/
theorem boundFinalTight_toClassical (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims) :
    boundFinalTight pkSeedDist B₁ B₂ (Lazy.bItsrL Q.toClassical)
        (toDspr (Lazy.bOpenPreS Q.toClassical)) (toTcr (Lazy.bOpenPreS Q.toClassical))
        (bTcrArST 1 Q.toClassical) (bTcrArST 2 Q.toClassical)
        (bTcrArST vp.params.len Q.toClassical) (bTcrArST vp.params.k Q.toClassical)
        (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)) (rPre pkSeedDist (Lazy.bWotsS Q.toClassical))
        (rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical)) =
      qBoundTight Q ((skPrfC vp prims).prfAdvantage B₁) ((msgPrf vp prims).prfAdvantage B₂) := by
  unfold boundFinalTight qBoundTight
  rw [qItsrAdvantage_qbItsrL Q hQ, qDsprFV_Advantage_qToDspr Q hQ, qTcrFV_Advantage_qToTcr Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArST 1 Q hQ, qSM_DT_TCR_Advantage_qbTcrArST 2 Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArST vp.params.len Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArST vp.params.k Q hQ, qSM_DT_UD_Advantage_qrUd Q hQ,
    qSM_DT_PRE_Advantage_qrPre Q hQ, qSM_DT_TCR_Advantage_qrTcrT Q hQ]

theorem betaEufFinalTight_toClassical (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    betaEufFinalTight Q.toClassical = qBetaEufTight Q := by
  unfold betaEufFinalTight qBetaEufTight
  rw [boundFinalTight_toClassical Q hQ, qPrfAdvantage_qbPrfC Q hQ, qPrfAdvantage_qbPrfMsgL Q hQ]

theorem betaSufFinalTight_toClassical (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    betaSufFinalTight Q.toClassical = qBetaSufTight Q := by
  unfold betaSufFinalTight qBetaSufTight
  rw [boundFinalTight_toClassical Q hQ, qPrfAdvantage_qbPrfWC sufCheck Q hQ,
    qPrfAdvantage_qbPrfMsgWL sufCheck Q hQ]

/-! ## Headlines: the internal scheme -/

/-- **EUF-CMA of SLH-DSA (internal algorithms) against quantum forgers, tight caps, quantum
reduction adversaries.**  For every quantum forger `Q` with classical signing queries and rational
Born probabilities, the quantum EUF-CMA advantage is at most `qBetaEufTight Q`: twelve quantum
advantages of explicit quantum machines running `Q` once. -/
theorem slhdsa_euf_cma_final_tight_quantum (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q ≤ qBetaEufTight Q := by
  rw [← betaEufFinalTight_toClassical Q hQ]
  exact qUnforgeableAdvantage_le_of_forall Q hQ betaEufFinalTight (slhdsa_euf_cma_final_tight' hS)

/-- **SUF-CMA of SLH-DSA (internal algorithms) against quantum forgers, tight caps, quantum
reduction adversaries.**  The quantum strong-unforgeability advantage of `Q` is at most
`qBetaSufTight Q`. -/
theorem slhdsa_suf_cma_final_tight_quantum (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufTight Q := by
  rw [← betaSufFinalTight_toClassical Q hQ]
  exact qStrongUnforgeableAdvantage_le_of_forall Q hQ
    (fun S ↦ betaSufFinalTight S.toUnforgeableAdversary) (slhdsa_suf_cma_final_tight' hS)

/-! ## Headlines: the external pure interface -/

lemma forwardsUnif0_signingImpl {E M S ε : Type} (enc : E → Except ε M) :
    ForwardsUnif0 (Guarded.signingImpl (S := S) enc) := fun _ ↦ rfl

/-- The external-to-internal wrapper `Reduction.toInternal` around a quantum forger against the
external pure interface: classical code (context-string encoding of the signing queries and of
the final forgery) around the quantum machine.  The result is a quantum forger against the
internal scheme with the same workspace and initial state. -/
noncomputable def qToInternal (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    QForger W (internalAlg vp prims optRand pkSeedDist) where
  main pk := Guarded.readForgery pureEncode ([], constSig default) <$>
    wrap0 (Guarded.signingImpl pureEncode) (Q.main pk)
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

theorem toClassical_qToInternal (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    (qToInternal Q).toClassical = toInternal Q.toClassical := by
  have hmain : ∀ pk, (qToInternal Q).toClassical.main pk = (toInternal Q.toClassical).main pk := by
    intro pk
    change toProbComp (_ <$> wrap0 _ _) Q.ρ₀ = _
    rw [toProbComp_map, toProbComp_wrap0 _ (forwardsUnif0_signingImpl _)]
    rfl
  change SignatureAlg.UnforgeableAdversary.mk _ = SignatureAlg.UnforgeableAdversary.mk _
  congr 1
  funext pk
  exact hmain pk

theorem rationalBorn_qToInternal (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) (pk : PublicKeyCore prims.core) :
    RationalBorn ((qToInternal Q).main pk) (qToInternal Q).ρ₀ :=
  rationalBorn_map _ _ _ (rationalBorn_wrap0 _ _ _ (hQ pk))

/-- **EUF-CMA of the external pure interface of SLH-DSA (FIPS 205 Alg. 22/24, context strings)
against quantum forgers, tight caps, quantum reduction adversaries.**  The quantum EUF-CMA
advantage of a quantum forger `Q` against `externalAlg` is at most the quantum bound at the
internal quantum forger `qToInternal Q`. -/
theorem slhdsa_pure_euf_cma_final_tight_quantum (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q ≤ qBetaEufTight (qToInternal Q) := by
  rw [← betaEufFinalTight_toClassical (qToInternal Q) (rationalBorn_qToInternal Q hQ),
    toClassical_qToInternal]
  exact qUnforgeableAdvantage_le_of_forall Q hQ (fun A ↦ betaEufFinalTight (toInternal A))
    (slhdsa_pure_euf_cma_final_tight' hS)

/-- **SUF-CMA of the external pure interface against quantum forgers, tight caps, quantum
reduction adversaries.** -/
theorem slhdsa_pure_suf_cma_final_tight_quantum (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufTight (qToInternal Q) := by
  rw [← betaSufFinalTight_toClassical (qToInternal Q) (rationalBorn_qToInternal Q hQ),
    toClassical_qToInternal]
  exact qStrongUnforgeableAdvantage_le_of_forall Q hQ
    (fun S ↦ betaSufFinalTight (toInternal S.toUnforgeableAdversary))
    (slhdsa_pure_suf_cma_final_tight' hS)

end Reduction

#print axioms Reduction.qPrfAdvantage_qbPrfWC
#print axioms Reduction.qPrfAdvantage_qbPrfMsgWL
#print axioms Reduction.qSM_DT_TCR_Advantage_qbTcrArST
#print axioms Reduction.qSM_DT_TCR_Advantage_qrTcrT
#print axioms Reduction.toClassical_qToInternal
#print axioms Reduction.slhdsa_euf_cma_final_tight_quantum
#print axioms Reduction.slhdsa_suf_cma_final_tight_quantum
#print axioms Reduction.slhdsa_pure_euf_cma_final_tight_quantum
#print axioms Reduction.slhdsa_pure_suf_cma_final_tight_quantum
