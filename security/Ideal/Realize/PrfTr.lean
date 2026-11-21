import Ideal.Transport.AdvPrf
import Reduction.Open.Prf

/-!
# The open `PRF` distinguishers over `setPrf prims prf pm` and over `prims`

`Reduction.Open.bPrfWCOpen sufCheckOpen A` / `bPrfCOpen A` evaluate neither `PRF` nor
`PRF_msg` (secrets are game queries, randomizers `.prfmsg` queries, hashes hash queries), so
they are the same programs over `setPrf prims prf pm` (any `prf`, `pm`) and over `prims`, up to
the kernel-identity `castP` between the two (kernel-defeq) interfaces.  This fills the gap "no
`withHash` statement for the PRF programs" of `status/OPEN.md` §2 for the `PRF` / `PRF_msg`
components; `bPrfWCOpen_withTH`, `bPrfCOpen_withTH` (`rfl`) do the same for `Thash` / `H_msg`.

* `castP`, `castP'` and their `bind`/`pure`/`liftM`/query lemmas (all `krfl`);
* `openKeygenP_tr`, `openSignP_tr`, `prf_runForgerSig_tr`, `prf_runForger_tr`,
  `sufCheckOpen_tr`, `eufCheckOpen_tr`;
* **`bPrfWCOpen_setPrf`**, **`bPrfCOpen_setPrf`**, `bPrfWCOpen_withTH`, `bPrfCOpen_withTH`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Prf

open Reduction Reduction.Open Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Cast

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y) (D : Type)

/-- A program over the open interface of `setPrf prims prf pm`, read over that of `prims`. -/
def castP {α : Type} (x : OracleComp (PSpec (setPrf prims prf pm) D) α) :
    OracleComp (PSpec prims D) α := by
  kexact x

/-- The inverse reading. -/
def castP' {α : Type} (x : OracleComp (PSpec prims D) α) :
    OracleComp (PSpec (setPrf prims prf pm) D) α := by
  kexact x

/-- A hash program over `setPrf`'s core read over `prims.core`'s. -/
def castH' {α : Type} (x : OracleComp (publicHashSpec prims.core) α) :
    OracleComp (publicHashSpec (setPrfC prims.core prf pm)) α := by
  kexact x

theorem castP_bind {α β : Type} (x : OracleComp (PSpec (setPrf prims prf pm) D) α)
    (f : α → OracleComp (PSpec (setPrf prims prf pm) D) β) :
    castP prims prf pm D (x >>= f) =
      castP prims prf pm D x >>= fun a => castP prims prf pm D (f a) := by krfl

theorem castP_pure {α : Type} (a : α) :
    castP prims prf pm D (pure a : OracleComp (PSpec (setPrf prims prf pm) D) α) = pure a := by
  krfl

theorem castP_map {α β : Type} (g : α → β) (x : OracleComp (PSpec (setPrf prims prf pm) D) α) :
    castP prims prf pm D (g <$> x) = g <$> castP prims prf pm D x := by krfl

theorem castP_liftM {α : Type} (x : ProbComp α) :
    castP prims prf pm D (liftM x : OracleComp (PSpec (setPrf prims prf pm) D) α) = liftM x := by
  krfl

theorem castP_castP' {α : Type} (x : OracleComp (PSpec prims D) α) :
    castP prims prf pm D (castP' prims prf pm D x) = x := by krfl

theorem castP'_bind {α β : Type} (x : OracleComp (PSpec prims D) α)
    (f : α → OracleComp (PSpec prims D) β) :
    castP' prims prf pm D (x >>= f) =
      castP' prims prf pm D x >>= fun a => castP' prims prf pm D (f a) := by krfl

theorem castP'_liftM {α : Type} (x : ProbComp α) :
    castP' prims prf pm D (liftM x : OracleComp (PSpec prims D) α) = liftM x := by krfl

theorem castP'_gameQ (d : D) :
    castP' prims prf pm D (gameQ prims d) = gameQ (setPrf prims prf pm) d := by krfl

theorem castP'_prfMsgQ (skPrf : prims.SkPrf) (addrnd : prims.Y) (m : List Byte) :
    castP' prims prf pm D (prfMsgQ prims D skPrf addrnd m) =
      prfMsgQ (setPrf prims prf pm) D skPrf addrnd m := by krfl

end Cast

section Tr

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

theorem castP_openKeygenP (pkSeed : prims.PkSeed) :
    castP prims prf pm (prims.PkSeed × Adrs) (openKeygenP (setPrf prims prf pm) pkSeed) =
      openKeygenP prims pkSeed := by krfl

/-- Open signing at a supplied randomizer, over `setPrf prims prf pm`. -/
theorem openSignCoreP_tr (m : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y) :
    openSignCoreP (setPrf prims prf pm) m pkSeed pkRoot R =
      trSig _ prf pm <$> castP' prims prf pm (prims.PkSeed × Adrs)
        (openSignCoreP prims m pkSeed pkRoot R) := by
  kexact signInternalWithSecretRandomizerM_tr (vp := vp) prims.core prf pm
    (m := OracleComp (PSpec (setPrf prims prf pm) (prims.PkSeed × Adrs)))
    (by kexact openQ prims (prims.PkSeed × Adrs)) (openQ (setPrf prims prf pm) (prims.PkSeed × Adrs))
    (fun _ _ _ => by krfl) (fun _ _ _ _ => by krfl)
    (fun a => gameQ (setPrf prims prf pm) (pkSeed, a)) m pkSeed pkRoot R

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)

include hopt in
/-- The open signing procedure over `setPrf prims prf pm`. -/
theorem openSignP_tr (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) (m : List Byte) :
    openSignP (prims := setPrf prims prf pm) optRand' (trPk _ prf pm pk) skPrf m =
      trSig _ prf pm <$> castP' prims prf pm (prims.PkSeed × Adrs)
        (openSignP optRand pk skPrf m) := by
  unfold openSignP
  rw [hopt]
  simp only [castP'_bind, castP'_liftM, castP'_prfMsgQ, map_bind, trPk_pkSeed, trPk_pkRoot]
  refine bind_congr fun addrnd => bind_congr fun R => ?_
  exact openSignCoreP_tr prims prf pm m pk.pkSeed pk.pkRoot R

variable (codec : CoreWireCodec vp.params prims.core) (pkSeedDist : ProbComp prims.PkSeed)
  (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))

/-- `runForgerSig` inside an open PRF program. -/
theorem prf_runForgerSig_tr {D : Type} (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (PSpec prims D) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte → OracleComp (PSpec (setPrf prims prf pm) D)
      (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m, sign' m = trSig _ prf pm <$> castP' prims prf pm D (sign m)) :
    castP prims prf pm D
        (runForgerSig (prims := setPrf prims prf pm)
          (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk) sign') =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), trLog prf pm z.2)) <$>
        runForgerSig (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk sign := by
  rw [runForgerSig_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist S pk
    (fun m => castP' prims prf pm D (sign m)) sign' hs]
  krfl

/-- `runForger` inside an open PRF program. -/
theorem prf_runForger_tr {D : Type} (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (PSpec prims D) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte → OracleComp (PSpec (setPrf prims prf pm) D)
      (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m, sign' m = trSig _ prf pm <$> castP' prims prf pm D (sign m)) :
    castP prims prf pm D
        (runForger (prims := setPrf prims prf pm)
          (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk) sign') =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        runForger (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk sign := by
  rw [runForger_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist S pk
    (fun m => castP' prims prf pm D (sign m)) sign' hs]
  krfl

/-- The SUF log test, transported. -/
theorem contains_tr (log : SigLog vp prims) (m : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    @SignatureAlg.signingLogContains (List Byte)
        (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)) _
        (sigDecEq (vp := vp) (prims := setPrf prims prf pm)) (trLog prf pm log) m
        (trSig _ prf pm sig) =
      @SignatureAlg.signingLogContains (List Byte) (GeneralScheme.SignatureCore vp prims.core) _
        (sigDecEq (vp := vp) (prims := prims)) log m sig := by
  unfold SignatureAlg.signingLogContains
  rw [decide_eq_decide]
  exact trLog_mem prims prf pm log m sig

/-- The open SUF check, transported. -/
theorem sufCheckOpen_tr {D : Type} (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims) :
    simulateQ (hashEmb (setPrf prims prf pm) D)
        (sufCheckOpen (prims := setPrf prims prf pm) (trPk _ prf pm pk) (f.1, trSig _ prf pm f.2)
          (trLog prf pm log)) =
      castP' prims prf pm D (simulateQ (hashEmb prims D) (sufCheckOpen pk f log)) := by
  have hv := verifyInternalM_setPrf (vp := vp) prims.core prf pm
    (m := OracleComp (publicHashSpec (setPrfC prims.core prf pm)))
    (by kexact (inferInstance : HasQuery (publicHashSpec prims.core)
      (OracleComp (publicHashSpec prims.core))))
    inferInstance (fun _ _ _ => by krfl) (fun _ _ _ _ => by krfl) f.1 f.2 pk
  have e : sufCheckOpen (prims := setPrf prims prf pm) (trPk _ prf pm pk) (f.1, trSig _ prf pm f.2)
      (trLog prf pm log) = castH' prims prf pm (sufCheckOpen pk f log) := by
    unfold sufCheckOpen
    dsimp only
    rw [contains_tr prims prf pm log f.1 f.2]
    rw [hv]
    show _ = _
    krfl
  rw [e]
  show _ = _
  krfl

/-- The open EUF check (used with `harnessValid`'s message list), transported. -/
theorem verifyEmb_tr {D : Type} (pk : PublicKeyCore prims.core) (msgs : List (List Byte))
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (hashEmb (setPrf prims prf pm) D)
        (GeneralScheme.verifyInternalM vp (setPrfC prims.core prf pm) msg (trSig _ prf pm sig)
          (trPk _ prf pm pk) : OracleComp (publicHashSpec (setPrfC prims.core prf pm)) Bool) =
      castP' prims prf pm D (simulateQ (hashEmb prims D)
        (GeneralScheme.verifyInternalM vp prims.core msg sig pk :
          OracleComp (publicHashSpec prims.core) Bool)) := by
  have hv := verifyInternalM_setPrf (vp := vp) prims.core prf pm
    (m := OracleComp (publicHashSpec (setPrfC prims.core prf pm)))
    (by kexact (inferInstance : HasQuery (publicHashSpec prims.core)
      (OracleComp (publicHashSpec prims.core))))
    inferInstance (fun _ _ _ => by krfl) (fun _ _ _ _ => by krfl) msg sig pk
  rw [hv]
  show _ = _
  krfl

include hopt in
/-- **The open SUF `PRF` distinguisher (before the domain restriction) over `setPrf`.** -/
theorem bPrfWOpen_setPrf :
    castP prims prf pm (prims.PkSeed × Adrs)
        (bPrfWOpen (prims := setPrf prims prf pm) sufCheckOpen
          (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)) =
      bPrfWOpen sufCheckOpen (bytesToTyped (prims := prims) (codec := codec)
        (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩) := by
  unfold bPrfWOpen bRestWOpen
  simp only [castP_bind, castP_liftM]
  refine bind_congr fun pkSeed => bind_congr fun skPrf => ?_
  rw [castP_openKeygenP]
  refine bind_congr fun root => ?_
  have h := prf_runForgerSig_tr prims prf pm optRand optRand' codec pkSeedDist S
    (D := prims.PkSeed × Adrs) ⟨pkSeed, root⟩ (openSignP optRand ⟨pkSeed, root⟩ skPrf)
    (openSignP (prims := setPrf prims prf pm) optRand' (trPk _ prf pm ⟨pkSeed, root⟩) skPrf)
    (fun m => openSignP_tr prims prf pm optRand optRand' hopt ⟨pkSeed, root⟩ skPrf m)
  simp only [trPk_mk] at h
  rw [h, bind_map_left]
  refine bind_congr fun z => ?_
  have hc := sufCheckOpen_tr prims prf pm (D := prims.PkSeed × Adrs) ⟨pkSeed, root⟩ z.1 z.2
  simp only [trPk_mk] at hc
  rw [hc, castP_castP']

include hopt in
/-- **The open EUF `PRF` distinguisher (before the domain restriction) over `setPrf`.** -/
theorem bPrfOpen_setPrf :
    castP prims prf pm (prims.PkSeed × Adrs)
        (bPrfOpen (prims := setPrf prims prf pm)
          (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)) =
      bPrfOpen (bytesToTyped (prims := prims) (codec := codec)
        (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩) := by
  unfold bPrfOpen bRestOpen
  simp only [castP_bind, castP_liftM]
  refine bind_congr fun pkSeed => bind_congr fun skPrf => ?_
  rw [castP_openKeygenP]
  refine bind_congr fun root => ?_
  have h := prf_runForger_tr prims prf pm optRand optRand' codec pkSeedDist S
    (D := prims.PkSeed × Adrs) ⟨pkSeed, root⟩ (openSignP optRand ⟨pkSeed, root⟩ skPrf)
    (openSignP (prims := setPrf prims prf pm) optRand' (trPk _ prf pm ⟨pkSeed, root⟩) skPrf)
    (fun m => openSignP_tr prims prf pm optRand optRand' hopt ⟨pkSeed, root⟩ skPrf m)
  simp only [trPk_mk] at h
  rw [h, bind_map_left]
  refine bind_congr fun z => ?_
  have hc := verifyEmb_tr prims prf pm (D := prims.PkSeed × Adrs) ⟨pkSeed, root⟩ z.2 z.1.1 z.1.2
  simp only [trPk_mk] at hc
  simp only [castP_pure]
  rw [hc, castP_castP']

theorem castP_restrictO {α : Type} (x : OracleComp (PSpec (setPrf prims prf pm) (prims.PkSeed × Adrs)) α) :
    castP prims prf pm (prims.PkSeed × SkAdrs vp)
        (simulateQ (restrictO (prims := setPrf prims prf pm) (skRestrict vp (setPrf prims prf pm))) x) =
      simulateQ (restrictO (prims := prims) (skRestrict vp prims))
        (castP prims prf pm (prims.PkSeed × Adrs) x) := by krfl

include hopt in
/-- **The open SUF `PRF` distinguisher over `setPrf prims prf pm` is the one over `prims`.** -/
theorem bPrfWCOpen_setPrf :
    castP prims prf pm (prims.PkSeed × SkAdrs vp)
        (bPrfWCOpen (prims := setPrf prims prf pm) sufCheckOpen
          (bytesToTypedS (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary) =
      bPrfWCOpen sufCheckOpen (bytesToTypedS (prims := prims) (codec := codec)
        (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary := by
  unfold bPrfWCOpen
  rw [castP_restrictO]
  exact congrArg _ (bPrfWOpen_setPrf prims prf pm optRand optRand' hopt codec pkSeedDist S)

include hopt in
/-- **The open EUF `PRF` distinguisher over `setPrf prims prf pm` is the one over `prims`.** -/
theorem bPrfCOpen_setPrf :
    castP prims prf pm (prims.PkSeed × SkAdrs vp)
        (bPrfCOpen (prims := setPrf prims prf pm)
          (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
            (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)) =
      bPrfCOpen (bytesToTyped (prims := prims) (codec := codec)
        (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩) := by
  unfold bPrfCOpen
  rw [castP_restrictO]
  exact congrArg _ (bPrfOpen_setPrf prims prf pm optRand optRand' hopt codec pkSeedDist S)

end Tr

section WithTH

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- **The open SUF `PRF` distinguisher does not depend on `Thash`, `H_msg`** (the `withTH` form
missing from `status/OPEN.md` §2). -/
theorem bPrfWCOpen_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    bPrfWCOpen (prims := withTH prims T H) sufCheckOpen (castForger T H A) =
      bPrfWCOpen sufCheckOpen A := by krfl

/-- **The open EUF `PRF` distinguisher does not depend on `Thash`, `H_msg`.** -/
theorem bPrfCOpen_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    bPrfCOpen (prims := withTH prims T H) (castForger T H A) = bPrfCOpen A := by krfl

end WithTH

end Ideal.Realize.Prf

#print axioms Ideal.Realize.Prf.openSignP_tr
#print axioms Ideal.Realize.Prf.prf_runForgerSig_tr
#print axioms Ideal.Realize.Prf.sufCheckOpen_tr
#print axioms Ideal.Realize.Prf.bPrfWOpen_setPrf
#print axioms Ideal.Realize.Prf.bPrfOpen_setPrf
#print axioms Ideal.Realize.Prf.bPrfWCOpen_setPrf
#print axioms Ideal.Realize.Prf.bPrfCOpen_setPrf
#print axioms Ideal.Realize.Prf.bPrfWCOpen_withTH
#print axioms Ideal.Realize.Prf.bPrfCOpen_withTH
