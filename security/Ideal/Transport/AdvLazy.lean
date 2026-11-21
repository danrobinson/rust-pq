import Ideal.Transport.AdvCommon
import Reduction.Lazy.Open

/-!
# Open programs (`Reduction.Lazy`) over `setPrf prims prf pm` and over `prims`

The interface `Lazy.OSpec (setPrf prims prf pm) G` of the open programs is only kernel-defeq to
`Lazy.OSpec prims G` (`publicHashSpec` is a `match` on the query, parameterised by the core).
`castO` / `castO'` are the two kernel-identity coercions between programs over the two
interfaces; all lemmas about them are `krfl`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

open Reduction

set_option linter.unusedSectionVars false

section Cast

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable {ι : Type} (G : OracleSpec ι)

/-- A program over the open interface of `setPrf prims prf pm`, read over that of `prims`
(the identity; the two interfaces are kernel-defeq). -/
def castO {α : Type} (x : OracleComp (Lazy.OSpec (setPrf prims prf pm) G) α) :
    OracleComp (Lazy.OSpec prims G) α := by
  kexact x

/-- The inverse reading. -/
def castO' {α : Type} (x : OracleComp (Lazy.OSpec prims G) α) :
    OracleComp (Lazy.OSpec (setPrf prims prf pm) G) α := by
  kexact x

theorem castO_castO' {α : Type} (x : OracleComp (Lazy.OSpec prims G) α) :
    castO prims prf pm G (castO' prims prf pm G x) = x := by krfl

theorem castO_bind {α β : Type} (x : OracleComp (Lazy.OSpec (setPrf prims prf pm) G) α)
    (f : α → OracleComp (Lazy.OSpec (setPrf prims prf pm) G) β) :
    castO prims prf pm G (x >>= f) =
      castO prims prf pm G x >>= fun a => castO prims prf pm G (f a) := by krfl

theorem castO_pure {α : Type} (a : α) :
    castO prims prf pm G (pure a : OracleComp (Lazy.OSpec (setPrf prims prf pm) G) α) =
      pure a := by krfl

theorem castO_map {α β : Type} (g : α → β)
    (x : OracleComp (Lazy.OSpec (setPrf prims prf pm) G) α) :
    castO prims prf pm G (g <$> x) = g <$> castO prims prf pm G x := by krfl

theorem castO_liftM {α : Type} (x : ProbComp α) :
    castO prims prf pm G (liftM x : OracleComp (Lazy.OSpec (setPrf prims prf pm) G) α) =
      liftM x := by krfl

theorem castO_gameQ (t : ι) :
    castO prims prf pm G (Lazy.gameQ (setPrf prims prf pm) G t) = Lazy.gameQ prims G t := by krfl

theorem castO'_bind {α β : Type} (x : OracleComp (Lazy.OSpec prims G) α)
    (f : α → OracleComp (Lazy.OSpec prims G) β) :
    castO' prims prf pm G (x >>= f) =
      castO' prims prf pm G x >>= fun a => castO' prims prf pm G (f a) := by krfl

theorem castO'_liftM {α : Type} (x : ProbComp α) :
    castO' prims prf pm G (liftM x : OracleComp (Lazy.OSpec prims G) α) = liftM x := by krfl

theorem castO'_gameQ (t : ι) :
    castO' prims prf pm G (Lazy.gameQ prims G t) = Lazy.gameQ (setPrf prims prf pm) G t := by krfl

theorem castO_openKeygen (pkSeed : prims.PkSeed) :
    castO prims prf pm G (Lazy.openKeygen (setPrf prims prf pm) G pkSeed) =
      Lazy.openKeygen prims G pkSeed := by krfl

/-- Open signing over `setPrf prims prf pm`. -/
theorem lazyOpenSign_tr (msg : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y) :
    Lazy.openSign (setPrf prims prf pm) G msg pkSeed pkRoot R =
      trSig _ prf pm <$> castO' prims prf pm G (Lazy.openSign prims G msg pkSeed pkRoot R) := by
  kexact signInternalWithSecretRandomizerM_tr (vp := vp) prims.core prf pm
    (m := OracleComp (Lazy.OSpec (setPrf prims prf pm) G))
    (by kexact Lazy.openQ prims G) (Lazy.openQ (setPrf prims prf pm) G)
    (fun _ _ _ => by krfl) (fun _ _ _ _ => by krfl)
    (Lazy.secQ (setPrf prims prf pm) G) msg pkSeed pkRoot R

variable [DecidableEq prims.Y] [SampleableType prims.Y]

/-- `lazyRun` over `setPrf prims prf pm` is `lazyRun` over `prims` of the same program. -/
theorem lazyRun_setPrf {α : Type} (P : OracleComp (Lazy.OSpec (setPrf prims prf pm) G) α) :
    Lazy.lazyRun (PublicHash.impl (setPrf prims prf pm)) P =
      Lazy.lazyRun (PublicHash.impl prims) (castO prims prf pm G P) := by krfl

section Harness

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)
  (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))

include hopt in
/-- `runForgerLog` inside an open program. -/
theorem lazy_runForgerLog_tr (pk : PublicKeyCore prims.core)
    (rnd : G2Log prims → List Byte → prims.Y → OracleComp (Lazy.OSpec prims G) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (Lazy.OSpec prims G) (GeneralScheme.SignatureCore vp prims.core))
    (signR' : List Byte → prims.Y → OracleComp (Lazy.OSpec (setPrf prims prf pm) G)
      (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m R, signR' m R = trSig _ prf pm <$> castO' prims prf pm G (signR m R)) :
    castO prims prf pm G
        (runForgerLog (prims := setPrf prims prf pm)
          (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk)
          (fun l m a => castO' prims prf pm G (rnd l m a)) signR') =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        runForgerLog (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk rnd signR := by
  rw [runForgerLog_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist hopt S pk _
    (fun m R => castO' prims prf pm G (signR m R)) signR' hs]
  krfl

/-- `runForger` inside an open program. -/
theorem lazy_runForger_tr (pk : PublicKeyCore prims.core)
    (sign : List Byte →
      OracleComp (Lazy.OSpec prims G) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte → OracleComp (Lazy.OSpec (setPrf prims prf pm) G)
      (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m, sign' m = trSig _ prf pm <$> castO' prims prf pm G (sign m)) :
    castO prims prf pm G
        (runForger (prims := setPrf prims prf pm)
          (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk) sign') =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        runForger (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk sign := by
  rw [runForger_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist S pk
    (fun m => castO' prims prf pm G (sign m)) sign' hs]
  krfl

/-- `runForgerSig` inside an open program. -/
theorem lazy_runForgerSig_tr (pk : PublicKeyCore prims.core)
    (sign : List Byte →
      OracleComp (Lazy.OSpec prims G) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte → OracleComp (Lazy.OSpec (setPrf prims prf pm) G)
      (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m, sign' m = trSig _ prf pm <$> castO' prims prf pm G (sign m)) :
    castO prims prf pm G
        (runForgerSig (prims := setPrf prims prf pm)
          (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk) sign') =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), trLog prf pm z.2)) <$>
        runForgerSig (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk sign := by
  rw [runForgerSig_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist S pk
    (fun m => castO' prims prf pm G (sign m)) sign' hs]
  krfl

end Harness

end Cast

end Ideal.Transport

section AxiomCheck
open Ideal.Transport
#print axioms castO_bind
#print axioms castO_openKeygen
#print axioms lazyOpenSign_tr
#print axioms lazyRun_setPrf
#print axioms lazy_runForgerLog_tr
#print axioms lazy_runForger_tr
#print axioms lazy_runForgerSig_tr
end AxiomCheck
