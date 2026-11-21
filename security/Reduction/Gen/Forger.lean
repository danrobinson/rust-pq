import Reduction.Gen.Sig
import Reduction.External
import Reduction.TcrMemo

/-!
# General-spec forgers against the typed internal scheme; the `G2` run

* `GFam ds vp prims` — forger programs indexed by the public key, over `(ds + unifSpec) +` signing;
* `GForger ds vp prims optRand pkSeedDist` — VCVio's `UnforgeableAdversary` of the scheme
  `liftAlg ds (internalAlg …)` (this is quantum's `UnforgeableAdversary (liftSig sigAlg)`);
* `dummyForger` — a classical forger that outputs a fixed pair (used only to name the
  forger-independent first phases of the two-phase reduction adversaries);
* `g2RunWithG`, `g2RunG` — `g2RunWith`, `g2Run` around a general-spec forger.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction.Gen

variable {κ : Type} (ds : OracleSpec κ)
variable (vp : ValidatedParams) (prims : Primitives vp.params)

/-- Forger programs indexed by the public key (typed internal interface). -/
abbrev GFam : Type :=
  PublicKeyCore prims.core → OracleComp
    ((ds + unifSpec) + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (List Byte × GeneralScheme.SignatureCore vp prims.core)

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- A chosen-message forger against the typed internal scheme, over `ds + unifSpec`. -/
abbrev GForger : Type :=
  SignatureAlg.UnforgeableAdversary (liftAlg ds (internalAlg vp prims optRand pkSeedDist))

/-- A strong forger against the typed internal scheme, over `ds + unifSpec`. -/
abbrev GStrongForger : Type :=
  SignatureAlg.StrongUnforgeableAdversary (liftAlg ds (internalAlg vp prims optRand pkSeedDist))

variable {vp prims optRand pkSeedDist}

/-- The general-spec forger with a given program family. -/
def GForger.ofFam (F : GFam ds vp prims) : GForger ds vp prims optRand pkSeedDist := ⟨F⟩

/-- A classical forger that outputs a fixed pair without any query. -/
def dummyForger [Inhabited prims.Y] : Forger vp prims optRand pkSeedDist :=
  ⟨fun _ ↦ pure ([], constSig default)⟩

/-- `g2RunWith` around a general-spec forger family. -/
noncomputable def g2RunWithG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (F : GFam ds vp prims) (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core) :
    OracleComp (gSpec ds)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  runG ds ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
    g2SignOracle optRand pk signR) (F pk) []

/-- `g2Run` around a general-spec forger family. -/
noncomputable def g2RunG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (F : GFam ds vp prims) (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core) :
    OracleComp (gSpec ds)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  g2RunWithG ds optRand F pk fun m R ↦ idealSign vp prims tbl m pk R

/-- On a classical forger the general `G2` run is the classical one. -/
theorem g2RunWithG_embed (A : Forger vp prims optRand pkSeedDist) (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core) :
    g2RunWithG ds optRand (fun pk ↦ embed ds (A.main pk)) pk signR =
      liftR ds (g2RunWith A pk signR) :=
  runG_embed ds _ _ _

theorem g2RunG_embed (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pk : PublicKeyCore prims.core) :
    g2RunG ds optRand (fun pk ↦ embed ds (A.main pk)) tbl pk = liftR ds (g2Run A tbl pk) :=
  g2RunWithG_embed ds A pk _

end Reduction.Gen
