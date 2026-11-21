import Reduction.Gen.Forger
import Reduction.Gen.GamePrf
import Reduction.SufPrfV2
import Reduction.Linear

/-!
# The PRF distinguishers around a general-spec forger (`bPrfC`, `bPrfWC`)

`bPrfG ds optRand pkSeedDist F` / `bPrfWG ds optRand pkSeedDist w F` are `bPrf` / `bPrfW w` (game
on all of `Adrs`) with the forger family `F` run through `runGO` against the classical harness
handlers (`runForger` / `runForgerSig`); `bPrfCG` / `bPrfWCG` are these behind the
domain-restricting wrapper `Restrict.restrictImpl (skRestrict vp prims)`, applied by `wrapS`.

Both are instances of one shape, `openAdv`: "classical open prefix; one open run of the forger;
pure final test", for which naturality (`openAdv_embed`) and linearity in both PRF worlds
(`isLin_openAdv_real`, `isLin_openAdv_ideal`) are proved once.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction.Gen

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]

/-! ## The generic shape -/

section generic

variable {ιx ιg ιh ιx' : Type} {X : OracleSpec ιx} {G : OracleSpec ιg} {Hs : OracleSpec ιh}
  {X' : OracleSpec ιx'} {P PK PK' σ α α' : Type}

/-- Classical open prefix `pre`; one open run of the forger (key `pkOf x`) against the classical
handler `impl x` from state `s₀`; pure final test `post x`. -/
def openAdv (pre : OracleComp (unifSpec + G) P) (pkOf : P → PK)
    (impl : P → QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s₀ : σ)
    (post : P → α × σ → Bool) (F : PK → OracleComp ((ds + unifSpec) + X) α) :
    OracleComp ((ds + unifSpec) + G) Bool :=
  embed ds pre >>= fun x ↦ runGO ds (impl x) (F (pkOf x)) s₀ >>= fun r ↦ pure (post x r)

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- On a `ds`-free family the generic adversary is the classical program. -/
theorem openAdv_embed (pre : OracleComp (unifSpec + G) P) (pkOf : P → PK)
    (impl : P → QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s₀ : σ)
    (post : P → α × σ → Bool) (F₀ : PK → OracleComp (unifSpec + X) α) :
    openAdv ds pre pkOf impl s₀ post (fun pk ↦ embed ds (F₀ pk)) =
      embed ds (pre >>= fun x ↦ (simulateQ (impl x) (F₀ (pkOf x))).run s₀ >>= fun r ↦
        pure (post x r)) := by
  simp only [openAdv, runGO_embed, embed_bind, embed_pure]

/-- Linearity of a closed run of the generic adversary behind a stateless wrapper `R`, from any
start state and with any pure final projection. -/
theorem isLin_runG_openAdv {τ : Type} (H : QueryImpl (unifSpec + Hs) (StateT τ ProbComp)) (t : τ)
    (R : QueryImpl (unifSpec + G) (OracleComp (unifSpec + Hs)))
    (pre : OracleComp (unifSpec + G) P) (pkOf : P → PK)
    (impl : P → QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s₀ : σ)
    (post : P → α × σ → Bool)
    (w' : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X))) (e : PK → PK') (g : α' → α) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prG ds (Prod.fst <$> runG ds H
        (wrapS ds R (openAdv ds pre pkOf impl s₀ post (wrapFam ds w' e g F'))) t)) := by
  unfold openAdv
  simp only [runG_wrapS, runG_bind, runG_embedO, runG_runGO, runGO_wrapFam, runG_pure,
    bind_map_left, map_bind, map_pure]
  refine isLin_liftR_bind ds _ _ fun y ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- Linearity, real PRF world. -/
theorem isLin_openAdv_real {K D R' : Type} (prf : PRFScheme K D R')
    (R : QueryImpl (unifSpec + G) (OracleComp (unifSpec + (D →ₒ R'))))
    (pre : OracleComp (unifSpec + G) P) (pkOf : P → PK)
    (impl : P → QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s₀ : σ)
    (post : P → α × σ → Bool)
    (w' : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X))) (e : PK → PK') (g : α' → α) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfRealPrG ds prf
        (wrapS ds R (openAdv ds pre pkOf impl s₀ post (wrapFam ds w' e g F')))) := by
  unfold prfRealPrG prfRealExperimentG
  refine isLin_liftR_bind ds _ _ fun k ↦ ?_
  exact isLin_runG_openAdv ds _ _ R pre pkOf impl s₀ post w' e g

/-- Linearity, ideal PRF world. -/
theorem isLin_openAdv_ideal {D R' : Type} [DecidableEq D] [SampleableType R']
    (R : QueryImpl (unifSpec + G) (OracleComp (unifSpec + (D →ₒ R'))))
    (pre : OracleComp (unifSpec + G) P) (pkOf : P → PK)
    (impl : P → QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s₀ : σ)
    (post : P → α × σ → Bool)
    (w' : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X))) (e : PK → PK') (g : α' → α) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfIdealPrG ds (D := D) (R := R')
        (wrapS ds R (openAdv ds pre pkOf impl s₀ post (wrapFam ds w' e g F')))) := by
  unfold prfIdealPrG prfIdealExperimentG
  exact isLin_runG_openAdv ds _ _ R pre pkOf impl s₀ post w' e g

end generic

/-! ## The two distinguishers -/

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- Public-hash queries inside the PRF distinguisher are evaluated by `prims` (as in `bPrf`). -/
@[reducible] private def prfQG (prims : Primitives vp.params) :
    HasQuery (publicHashSpec prims.core)
      (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
  ⟨fun q ↦ pure (PublicHash.impl prims q)⟩

attribute [local instance] prfQG

/-- The forger-independent prefix of `bPrf` / `bPrfW`: sample `PK.seed` and `SK.prf`, compute the
root through the PRF oracle. -/
noncomputable def prfPre :
    OracleComp (unifSpec + ((prims.PkSeed × Adrs) →ₒ prims.Y))
      (prims.PkSeed × prims.SkPrf × prims.Y) :=
  (liftM pkSeedDist :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.PkSeed) >>=
  fun pkSeed ↦
    (monadLift ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.SkPrf) >>=
    fun skPrf ↦
      (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
        (fun a ↦ PRFScheme.functionQuery (pkSeed, a)) pkSeed :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) >>=
      fun root ↦ pure (pkSeed, skPrf, root)

/-- The public key computed by the prefix. -/
def prfPk (x : prims.PkSeed × prims.SkPrf × prims.Y) : PublicKeyCore prims.core := ⟨x.1, x.2.2⟩

/-- The handler of `runForger` inside `bPrf`. -/
noncomputable def prfHarness (x : prims.PkSeed × prims.SkPrf × prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (List (List Byte)) (OracleComp (unifSpec + ((prims.PkSeed × Adrs) →ₒ prims.Y)))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec + ((prims.PkSeed × Adrs) →ₒ prims.Y)))).liftTarget
      (StateT (List (List Byte)) (OracleComp (unifSpec + ((prims.PkSeed × Adrs) →ₒ prims.Y)))) +
    harnessSignOracle (bSignC optRand (prfPk x) x.2.1)

/-- The handler of `runForgerSig` inside `bPrfW`. -/
noncomputable def prfHarnessW (x : prims.PkSeed × prims.SkPrf × prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (SigLog vp prims) (OracleComp (unifSpec + ((prims.PkSeed × Adrs) →ₒ prims.Y)))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec + ((prims.PkSeed × Adrs) →ₒ prims.Y)))).liftTarget
      (StateT (SigLog vp prims) (OracleComp (unifSpec + ((prims.PkSeed × Adrs) →ₒ prims.Y)))) +
    sigSignOracle (bSignW optRand (prfPk x) x.2.1)

/-- `bPrf` around a general-spec forger family (game on all of `Adrs`). -/
noncomputable def bPrfG (F : GFam ds vp prims) : PRFAdversaryG ds (prims.PkSeed × Adrs) prims.Y :=
  openAdv ds (prfPre pkSeedDist) prfPk (prfHarness optRand) []
    (fun x z ↦ harnessValid (prfPk x) z.2 z.1.1 z.1.2) F

/-- `bPrfW w` around a general-spec forger family (game on all of `Adrs`). -/
noncomputable def bPrfWG (w : WinCheck vp prims) (F : GFam ds vp prims) :
    PRFAdversaryG ds (prims.PkSeed × Adrs) prims.Y :=
  openAdv ds (prfPre pkSeedDist) prfPk (prfHarnessW optRand) []
    (fun x z ↦ w (prfPk x) z.1 z.2) F

/-- **`bPrfC` around a general-spec forger family**: `bPrfG` behind the domain-restricting
wrapper. -/
noncomputable def bPrfCG (F : GFam ds vp prims) :
    PRFAdversaryG ds (prims.PkSeed × SkAdrs vp) prims.Y :=
  wrapS ds (Restrict.restrictImpl (skRestrict vp prims)) (bPrfG ds optRand pkSeedDist F)

/-- **`bPrfWC w` around a general-spec forger family**: `bPrfWG` behind the domain-restricting
wrapper. -/
noncomputable def bPrfWCG (w : WinCheck vp prims) (F : GFam ds vp prims) :
    PRFAdversaryG ds (prims.PkSeed × SkAdrs vp) prims.Y :=
  wrapS ds (Restrict.restrictImpl (skRestrict vp prims)) (bPrfWG ds optRand pkSeedDist w F)

variable {optRand pkSeedDist}

/-! ## Naturality -/

/-- `bPrf A` in the shape "prefix; run; test". -/
theorem bPrf_eq_pre (A : Forger vp prims optRand pkSeedDist) :
    bPrf A = prfPre pkSeedDist >>= fun x ↦
      (simulateQ (prfHarness optRand x) (A.main (prfPk x))).run [] >>= fun z ↦
        pure (harnessValid (prfPk x) z.2 z.1.1 z.1.2) := by
  rw [bPrf_eq_bRestC]
  simp only [prfPre, bind_assoc, pure_bind]
  rfl

/-- `bPrfW w A` in the shape "prefix; run; test". -/
theorem bPrfW_eq_pre (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    bPrfW w A = prfPre pkSeedDist >>= fun x ↦
      (simulateQ (prfHarnessW optRand x) (A.main (prfPk x))).run [] >>= fun z ↦
        pure (w (prfPk x) z.1 z.2) := by
  rw [bPrfW_eq_bRestW]
  simp only [seedThen, prfPre, bind_assoc, pure_bind]
  rfl

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem bPrfG_embed (A : Forger vp prims optRand pkSeedDist) :
    bPrfG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) = embed ds (bPrf A) := by
  rw [bPrfG, openAdv_embed, ← bPrf_eq_pre]

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem bPrfWG_embed (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    bPrfWG ds optRand pkSeedDist w (fun pk ↦ embed ds (A.main pk)) = embed ds (bPrfW w A) := by
  rw [bPrfWG, openAdv_embed, ← bPrfW_eq_pre]

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **Naturality.** On a classical forger, `bPrfCG` is `bPrfC`. -/
theorem bPrfCG_embed (A : Forger vp prims optRand pkSeedDist) :
    bPrfCG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) = embed ds (bPrfC A) := by
  rw [bPrfCG, bPrfG_embed, wrapS_embed]
  rfl

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **Naturality.** On a classical forger, `bPrfWCG w` is `bPrfWC w`. -/
theorem bPrfWCG_embed (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    bPrfWCG ds optRand pkSeedDist w (fun pk ↦ embed ds (A.main pk)) = embed ds (bPrfWC w A) := by
  rw [bPrfWCG, bPrfWG_embed, wrapS_embed]
  rfl

/-! ## Linearity -/

section linearity

variable {ιx' : Type} {X' : OracleSpec ιx'} {PK' α' : Type}
  (w' : QueryImpl (unifSpec + X')
    (OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))))
  (e : PublicKeyCore prims.core → PK')
  (g : α' → List Byte × GeneralScheme.SignatureCore vp prims.core)

/-- **Linearity**, real world of the PRF game on `skPrfC`, for `bPrfCG`. -/
theorem isLin_bPrfCG_real :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfRealPrG ds (skPrfC vp prims)
        (bPrfCG ds optRand pkSeedDist (wrapFam ds w' e g F'))) :=
  isLin_openAdv_real ds (skPrfC vp prims) _ _ _ _ _ _ w' e g

/-- **Linearity**, ideal world, for `bPrfCG`. -/
theorem isLin_bPrfCG_ideal :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfIdealPrG ds (bPrfCG ds optRand pkSeedDist (wrapFam ds w' e g F'))) :=
  isLin_openAdv_ideal ds _ _ _ _ _ _ w' e g

/-- **Linearity**, real world of the PRF game on `skPrfC`, for `bPrfWCG w`. -/
theorem isLin_bPrfWCG_real (w : WinCheck vp prims) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfRealPrG ds (skPrfC vp prims)
        (bPrfWCG ds optRand pkSeedDist w (wrapFam ds w' e g F'))) :=
  isLin_openAdv_real ds (skPrfC vp prims) _ _ _ _ _ _ w' e g

/-- **Linearity**, ideal world, for `bPrfWCG w`. -/
theorem isLin_bPrfWCG_ideal (w : WinCheck vp prims) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfIdealPrG ds (bPrfWCG ds optRand pkSeedDist w (wrapFam ds w' e g F'))) :=
  isLin_openAdv_ideal ds _ _ _ _ _ _ w' e g

end linearity

/-! ## Classical forgers -/

theorem prfRealPrG_bPrfCG_embed (A : Forger vp prims optRand pkSeedDist) :
    prfRealPrG ds (skPrfC vp prims)
        (bPrfCG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      prfRealPr (bPrfC A) := by
  rw [bPrfCG_embed, prfRealPrG_embed]; rfl

theorem prfIdealPrG_bPrfCG_embed (A : Forger vp prims optRand pkSeedDist) :
    prfIdealPrG ds (bPrfCG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      prfIdealPr (bPrfC A) := by
  rw [bPrfCG_embed, prfIdealPrG_embed]; rfl

theorem prfRealPrG_bPrfWCG_embed (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prfRealPrG ds (skPrfC vp prims)
        (bPrfWCG ds optRand pkSeedDist w (fun pk ↦ embed ds (A.main pk))) =
      prfRealPr (bPrfWC w A) := by
  rw [bPrfWCG_embed, prfRealPrG_embed]; rfl

theorem prfIdealPrG_bPrfWCG_embed (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prfIdealPrG ds (bPrfWCG ds optRand pkSeedDist w (fun pk ↦ embed ds (A.main pk))) =
      prfIdealPr (bPrfWC w A) := by
  rw [bPrfWCG_embed, prfIdealPrG_embed]; rfl

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms bPrfCG_embed
#print axioms bPrfWCG_embed
#print axioms isLin_bPrfCG_real
#print axioms isLin_bPrfCG_ideal
#print axioms isLin_bPrfWCG_real
#print axioms isLin_bPrfWCG_ideal
#print axioms prfRealPrG_bPrfCG_embed
#print axioms prfIdealPrG_bPrfCG_embed
#print axioms prfRealPrG_bPrfWCG_embed
#print axioms prfIdealPrG_bPrfWCG_embed
end Axioms
