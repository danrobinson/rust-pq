import Ideal.Transport.AdvLazy
import Reduction.Lazy.ItsrLazy

/-!
# Core-invariance of the ITSR adversary `Lazy.bItsrL A`
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

open Reduction

set_option linter.unusedSectionVars false

section Itsr

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)
  (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))

set_option quotPrecheck false in
/-- The typed forger over `prims` built from the byte-level main `S`. -/
local notation "Abase" =>
  (bytesToTyped (prims := prims) (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
    ⟨S⟩)

set_option quotPrecheck false in
/-- The typed forger over `setPrf prims prf pm` built from the same byte-level main `S`. -/
local notation "Aset" =>
  (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
    (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)

include hopt in
/-- The forger run inside the open ITSR program. -/
theorem itsr_run_setPrf (pkSeed : prims.PkSeed) (root : prims.Y) :
    castO prims prf pm (Lazy.itsrG prims)
        (runForgerLog (prims := setPrf prims prf pm) Aset ⟨pkSeed, root⟩
          (Lazy.itsrRandomizerO (prims := setPrf prims prf pm) pkSeed root)
          (fun m R => Lazy.openSign (setPrf prims prf pm) (Lazy.itsrG (setPrf prims prf pm)) m
            pkSeed root R)) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        runForgerLog Abase ⟨pkSeed, root⟩ (Lazy.itsrRandomizerO pkSeed root)
          (fun m R => Lazy.openSign prims (Lazy.itsrG prims) m pkSeed root R) := by
  kexact lazy_runForgerLog_tr prims prf pm (Lazy.itsrG prims) codec optRand optRand' hopt
    pkSeedDist S ⟨pkSeed, root⟩ (Lazy.itsrRandomizerO pkSeed root)
    (fun m R => Lazy.openSign prims (Lazy.itsrG prims) m pkSeed root R)
    (fun m R => Lazy.openSign (setPrf prims prf pm) (Lazy.itsrG prims) m pkSeed root R)
    (fun m R => lazyOpenSign_tr prims prf pm (Lazy.itsrG prims) m pkSeed root R)

include hopt in
/-- The open ITSR program. -/
theorem itsrOpen_setPrf :
    castO prims prf pm (Lazy.itsrG prims) (Lazy.itsrOpen Aset) = Lazy.itsrOpen Abase := by
  unfold Lazy.itsrOpen
  simp only [castO_bind, castO_liftM, castO_pure,
    itsr_run_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S, bind_map_left,
    trSig_randomness]
  krfl

include hopt in
/-- **`main` of the ITSR adversary.** -/
theorem bItsrL_main_setPrf : (Lazy.bItsrL Aset).main = (Lazy.bItsrL Abase).main := by
  unfold Lazy.bItsrL
  dsimp only
  rw [lazyRun_setPrf, itsrOpen_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S]

include hopt in
/-- **The ITSR adversary over `setPrf prims prf pm` is the ITSR adversary over `prims`.** -/
theorem bItsrL_setPrf : Lazy.bItsrL Aset = Lazy.bItsrL Abase :=
  congrArg KeyedHash.ITSRAdversary.mk
    (bItsrL_main_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- The same for the strong (SUF) forger wrapper. -/
theorem bItsrL_setPrf_S :
    Lazy.bItsrL (bytesToTypedS (prims := setPrf prims prf pm)
        (codec := trCodec _ prf pm codec) (optRand := optRand') (pkSeedDist := pkSeedDist)
        ⟨S⟩).toUnforgeableAdversary =
      Lazy.bItsrL (bytesToTypedS (prims := prims) (codec := codec) (optRand := optRand)
        (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary :=
  bItsrL_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S

include hopt in
/-- The ITSR advantage does not depend on `PRF`, `PRF_msg`. -/
theorem bItsrL_advantage_setPrf :
    KeyedHash.ITSRAdvantage (Lazy.bItsrL Aset) = KeyedHash.ITSRAdvantage (Lazy.bItsrL Abase) :=
  congrArg KeyedHash.ITSRAdvantage
    (bItsrL_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
theorem bItsrL_experiment_setPrf :
    KeyedHash.ITSRExperiment (Lazy.bItsrL Aset) = KeyedHash.ITSRExperiment (Lazy.bItsrL Abase) :=
  congrArg KeyedHash.ITSRExperiment
    (bItsrL_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

end Itsr

end Ideal.Transport

section AxiomCheck
open Ideal.Transport
#print axioms itsrOpen_setPrf
#print axioms bItsrL_main_setPrf
#print axioms bItsrL_setPrf
#print axioms bItsrL_setPrf_S
#print axioms bItsrL_advantage_setPrf
#print axioms bItsrL_experiment_setPrf
end AxiomCheck
