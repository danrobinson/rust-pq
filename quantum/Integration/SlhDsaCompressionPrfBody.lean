import Integration.SlhDsaCompressionPrfSample

namespace Reduction.Compression.SkGame
open SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed} {W : Type} [Fintype W]

/-- Signing reduction after its single public-seed draw. -/
noncomputable def body (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pkSeed : prims.PkSeed) :
    QOC W (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool :=
  letI : HasQuery (publicHashSpec prims.core)
      (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
    ⟨fun q => pure (PublicHash.impl prims q)⟩
  let secret (pkSeed : prims.PkSeed) (a : Adrs) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y :=
    PRFScheme.functionQuery (pkSeed, a)
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

noncomputable def checkedBody (w : WinCheck vp prims) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (pk : prims.PkSeed) := wrap0 (Restrict.restrictImpl (skRestrict vp prims)) (body w Q pk)

theorem qbPrfWC_draw (w : WinCheck vp prims) (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qbPrfWC w Q = drawThen pkSeedDist (checkedBody w Q) := by
  unfold qbPrfWC qbPrfW
  rw [QInd.wrap0_liftQ_bind, Restrict.simulateQ_restrict_liftM]
  rfl

theorem realPr_qbPrfWC [Fintype prims.SkSeed] [Fintype prims.PkSeed]
    (w : WinCheck vp prims) (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qPrfRealPr (skPrfC vp prims) (qbPrfWC w Q) Q.ρ₀ = ∑' pk, prob pkSeedDist (· = pk) *
      qPrfRealPr (skPrfC vp prims) (checkedBody w Q pk) Q.ρ₀ := by
  rw [qbPrfWC_draw, realPr_draw]

theorem idealPr_qbPrfWC (w : WinCheck vp prims) (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qPrfIdealPr (qbPrfWC w Q) Q.ρ₀ = ∑' pk, prob pkSeedDist (· = pk) *
      qPrfIdealPr (checkedBody w Q pk) Q.ρ₀ := by
  rw [qbPrfWC_draw, idealPr_draw]

end Reduction.Compression.SkGame
#print axioms Reduction.Compression.SkGame.qbPrfWC_draw
