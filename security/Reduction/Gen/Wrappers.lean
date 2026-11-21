import Reduction.Gen.Forger
import Reduction.Bytes

/-!
# Forger-to-forger wrappers over the general sampling interface

The classical reductions `toInternal` (external pure → internal), `bytesToTyped` (byte-level →
typed, internal) and `pureBytesToTyped` (byte-level → typed, external pure), and their
strong-unforgeability versions, are all of the form
`main pk := g <$> simulateQ w (adv.main (e pk))` for a stateless classical handler `w`.  Around a
forger over `ds + unifSpec` this is `wrapFam ds w e g`.

* `GExtForger`, `GBytesForger`, `GPureBytesForger` (and `…Strong…`) — forger types;
* `toInternalG`, `bytesToTypedG`, `pureBytesToTypedG` (and `…SG`) — the wrappers, with their
  families (`…_main`), naturality on classical forgers (`…_embed`) and compatibility with
  `toUnforgeableAdversary`;
* `isLin_sigExpG_wrap`, `eufAdvG_wrap_le`, `sufAdvG_wrap_le` — the generic transfer: a classical
  advantage inequality "outer forger ≤ wrapped forger" holds for all general-spec forgers;
* `external_advantage_leG`, `bytes_advantage_leG`, `pure_bytes_advantage_leG` (and strong);
* `toInternalG_pureBytesToTypedG_main` — the composite as one `wrapFam`;
* `wrapFam_queryBound` and its instances — signing-query budgets.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction.Gen

set_option linter.unusedSectionVars false

/-! ## Generic transfer -/

section generic

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
  {M PK SK S M' PK' SK' S' : Type}

/-- **Linearity through a wrapper.**  The signature experiment of a wrapped family is a linear
functional of the family. -/
theorem isLin_sigExpG_wrap (sigAlg : SignatureAlg ProbComp M PK SK S)
    (fresh : QueryLog (M →ₒ S) → M → S → Bool)
    (w : QueryImpl (unifSpec + (M' →ₒ S')) (OracleComp (unifSpec + (M →ₒ S))))
    (e : PK → PK') (g : M' × S' → M × S) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + (M' →ₒ S')) (M' × S') ↦
      prG ds (sigExpG ds sigAlg fresh (wrapFam ds w e g F'))) := by
  have h : (fun F' : PK' → OracleComp ((ds + unifSpec) + (M' →ₒ S')) (M' × S') ↦
        prG ds (sigExpG ds sigAlg fresh (wrapFam ds w e g F'))) =
      fun F' ↦ prG ds (liftR ds sigAlg.keygen >>= fun ks ↦
        runG ds (compS (signH sigAlg ks.1 ks.2) w) (F' (e ks.1)) [] >>=
          fun r : (M' × S') × QueryLog (M →ₒ S) ↦
            liftR ds (sigAlg.verify ks.1 (g r.1).1 (g r.1).2 >>= fun v ↦
              pure (fresh r.2 (g r.1).1 (g r.1).2 && v))) := by
    funext F'
    unfold sigExpG
    simp only [runG_wrapFam, bind_map_left]
  rw [h]
  exact isLin_liftR_bind ds sigAlg.keygen
    (fun ks F' ↦ runG ds (compS (signH sigAlg ks.1 ks.2) w) (F' (e ks.1)) [] >>=
      fun r : (M' × S') × QueryLog (M →ₒ S) ↦
        liftR ds (sigAlg.verify ks.1 (g r.1).1 (g r.1).2 >>= fun v ↦
          pure (fresh r.2 (g r.1).1 (g r.1).2 && v)))
    (fun ks ↦ isLin_run ds (compS (signH sigAlg ks.1 ks.2) w) (e ks.1) []
      (fun r : (M' × S') × QueryLog (M →ₒ S) ↦
        sigAlg.verify ks.1 (g r.1).1 (g r.1).2 >>= fun v ↦
          pure (fresh r.2 (g r.1).1 (g r.1).2 && v)))

/-- The EUF-CMA advantage of a wrapped family is a linear functional of the family. -/
theorem isLin_eufAdvG_wrap (sigAlg : SignatureAlg ProbComp M PK SK S)
    (w : QueryImpl (unifSpec + (M' →ₒ S')) (OracleComp (unifSpec + (M →ₒ S))))
    (e : PK → PK') (g : M' × S' → M × S) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + (M' →ₒ S')) (M' × S') ↦
      eufAdvG ds (sigAlg := sigAlg) ⟨wrapFam ds w e g F'⟩) := by
  classical
  simpa only [eufAdvG_eq_sigExpG] using
    isLin_sigExpG_wrap ds sigAlg (fun log m _ ↦ !log.wasQueried m) w e g

/-- The SUF-CMA advantage of a wrapped family is a linear functional of the family. -/
theorem isLin_sufAdvG_wrap (sigAlg : SignatureAlg ProbComp M PK SK S)
    (w : QueryImpl (unifSpec + (M' →ₒ S')) (OracleComp (unifSpec + (M →ₒ S))))
    (e : PK → PK') (g : M' × S' → M × S) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + (M' →ₒ S')) (M' × S') ↦
      sufAdvG ds (sigAlg := sigAlg) ⟨wrapFam ds w e g F'⟩) := by
  classical
  simpa only [sufAdvG_eq_sigExpG] using
    isLin_sigExpG_wrap ds sigAlg (fun log m σ ↦ !SignatureAlg.signingLogContains log m σ) w e g

/-- **Generic transfer, EUF-CMA.**  If every classical forger against `alg'` has advantage at most
that of its `(w, e, g)`-wrapping against `alg`, the same holds for forgers over `ds + unifSpec`. -/
theorem eufAdvG_wrap_le (alg : SignatureAlg ProbComp M PK SK S)
    (alg' : SignatureAlg ProbComp M' PK' SK' S')
    (w : QueryImpl (unifSpec + (M' →ₒ S')) (OracleComp (unifSpec + (M →ₒ S))))
    (e : PK → PK') (g : M' × S' → M × S)
    (h : ∀ A₀ : SignatureAlg.UnforgeableAdversary alg',
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A₀ ≤
        SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
          (⟨fun pk ↦ g <$> simulateQ w (A₀.main (e pk))⟩ : SignatureAlg.UnforgeableAdversary alg))
    (A : SignatureAlg.UnforgeableAdversary (liftAlg ds alg')) :
    eufAdvG ds A ≤ eufAdvG ds (sigAlg := alg) ⟨wrapFam ds w e g A.main⟩ := by
  refine derandG ds (N := fun F' ↦ eufAdvG ds (sigAlg := alg') ⟨F'⟩)
    (P := fun F' ↦ eufAdvG ds (sigAlg := alg) ⟨wrapFam ds w e g F'⟩)
    ENNReal.one_ne_top ENNReal.one_ne_top (isLin_eufAdvG ds alg')
    (isLin_eufAdvG_wrap ds alg w e g) (fun F₀ ↦ ?_) A.main
  rw [wrapFam_embed]
  exact (eufAdvG_embedAdv ds (sigAlg := alg') ⟨F₀⟩).le.trans
    ((h ⟨F₀⟩).trans (eufAdvG_embedAdv ds (sigAlg := alg)
      ⟨fun pk ↦ g <$> simulateQ w (F₀ (e pk))⟩).ge)

/-- **Generic transfer, SUF-CMA.** -/
theorem sufAdvG_wrap_le (alg : SignatureAlg ProbComp M PK SK S)
    (alg' : SignatureAlg ProbComp M' PK' SK' S')
    (w : QueryImpl (unifSpec + (M' →ₒ S')) (OracleComp (unifSpec + (M →ₒ S))))
    (e : PK → PK') (g : M' × S' → M × S)
    (h : ∀ A₀ : SignatureAlg.StrongUnforgeableAdversary alg',
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A₀ ≤
        SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
          (⟨fun pk ↦ g <$> simulateQ w (A₀.main (e pk))⟩ :
            SignatureAlg.StrongUnforgeableAdversary alg))
    (A : SignatureAlg.StrongUnforgeableAdversary (liftAlg ds alg')) :
    sufAdvG ds A ≤ sufAdvG ds (sigAlg := alg) ⟨wrapFam ds w e g A.main⟩ := by
  refine derandG ds (N := fun F' ↦ sufAdvG ds (sigAlg := alg') ⟨F'⟩)
    (P := fun F' ↦ sufAdvG ds (sigAlg := alg) ⟨wrapFam ds w e g F'⟩)
    ENNReal.one_ne_top ENNReal.one_ne_top (isLin_sufAdvG ds alg')
    (isLin_sufAdvG_wrap ds alg w e g) (fun F₀ ↦ ?_) A.main
  rw [wrapFam_embed]
  exact (sufAdvG_embedAdvS ds (sigAlg := alg') ⟨F₀⟩).le.trans
    ((h ⟨F₀⟩).trans (sufAdvG_embedAdvS ds (sigAlg := alg)
      ⟨fun pk ↦ g <$> simulateQ w (F₀ (e pk))⟩).ge)

end generic

/-! ## Signing-query budgets through a wrapper -/

section budget

variable {κ : Type} (ds : OracleSpec κ) {ιx ιx' : Type} {X : OracleSpec ιx} {X' : OracleSpec ιx'}
  {PK PK' α α' : Type}

/-- `embed` keeps the number of `X`-queries. -/
theorem embed_queryBound (t : OracleComp (unifSpec + X) α) (n : ℕ)
    (h : IsQueryBoundP t (fun i ↦ i.isRight = true) n) :
    IsQueryBoundP (embed ds t) (fun i ↦ i.isRight = true) n := by
  unfold embed
  apply h.simulateQ_of_step
  · rintro (t | x) ht
    · simp at ht
    · simp [embedImpl]
  · rintro (t | x) ht
    · simp [embedImpl]
    · simp at ht

/-- **Budget of a wrapped family.**  If the handler `w` makes no `X`-query on a sampling query and
at most one on an `X'`-query, the wrapped program makes at most as many `X`-queries as the
original program makes `X'`-queries. -/
theorem wrapFam_queryBound (w : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X)))
    (e : PK → PK') (g : α' → α)
    (hw0 : ∀ n, IsQueryBoundP (w (Sum.inl n)) (fun i ↦ i.isRight = true) 0)
    (hw1 : ∀ x, IsQueryBoundP (w (Sum.inr x)) (fun i ↦ i.isRight = true) 1)
    (F : PK' → OracleComp ((ds + unifSpec) + X') α') (qs : ℕ) (pk : PK)
    (h : IsQueryBoundP (F (e pk)) (fun i ↦ i.isRight = true) qs) :
    IsQueryBoundP (wrapFam ds w e g F pk) (fun i ↦ i.isRight = true) qs := by
  simp only [wrapFam, wrapS, isQueryBoundP_map_iff]
  apply h.simulateQ_of_step
  · rintro ((d | n) | x) ht
    · simp at ht
    · simp at ht
    · exact embed_queryBound ds _ 1 (hw1 x)
  · rintro ((d | n) | x) ht
    · simp [gImplS]
    · exact embed_queryBound ds _ 0 (hw0 n)
    · simp at ht

end budget

/-! ## The SLH-DSA wrappers -/

section slhdsa

variable {κ : Type} (ds : OracleSpec κ)
variable (vp : ValidatedParams) (prims : Primitives vp.params)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- A chosen-message forger against the external pure scheme, over `ds + unifSpec`. -/
abbrev GExtForger : Type :=
  SignatureAlg.UnforgeableAdversary (liftAlg ds (externalAlg vp prims optRand pkSeedDist))

/-- A strong forger against the external pure scheme, over `ds + unifSpec`. -/
abbrev GExtStrongForger : Type :=
  SignatureAlg.StrongUnforgeableAdversary (liftAlg ds (externalAlg vp prims optRand pkSeedDist))

/-- A chosen-message forger against the byte-level internal scheme, over `ds + unifSpec`. -/
abbrev GBytesForger : Type :=
  SignatureAlg.UnforgeableAdversary (liftAlg ds (bytesAlg vp prims codec optRand pkSeedDist))

/-- A strong forger against the byte-level internal scheme, over `ds + unifSpec`. -/
abbrev GBytesStrongForger : Type :=
  SignatureAlg.StrongUnforgeableAdversary
    (liftAlg ds (bytesAlg vp prims codec optRand pkSeedDist))

/-- A chosen-message forger against the byte-level external pure scheme, over `ds + unifSpec`. -/
abbrev GPureBytesForger : Type :=
  SignatureAlg.UnforgeableAdversary (liftAlg ds (pureBytesAlg vp prims codec optRand pkSeedDist))

/-- A strong forger against the byte-level external pure scheme, over `ds + unifSpec`. -/
abbrev GPureBytesStrongForger : Type :=
  SignatureAlg.StrongUnforgeableAdversary
    (liftAlg ds (pureBytesAlg vp prims codec optRand pkSeedDist))

variable {vp prims codec optRand pkSeedDist}
variable [Inhabited prims.Y]

/-! ### Definitions -/

/-- `toInternal` around a general-spec forger. -/
noncomputable def toInternalG (A : GExtForger ds vp prims optRand pkSeedDist) :
    GForger ds vp prims optRand pkSeedDist :=
  ⟨wrapFam ds (Guarded.signingImpl pureEncode) id
    (Guarded.readForgery pureEncode ([], constSig default)) A.main⟩

/-- `toInternalS` around a general-spec strong forger. -/
noncomputable def toInternalSG (A : GExtStrongForger ds vp prims optRand pkSeedDist) :
    GStrongForger ds vp prims optRand pkSeedDist :=
  ⟨wrapFam ds (Guarded.signingImpl pureEncode) id
    (Guarded.readForgery pureEncode ([], constSig default)) A.main⟩

/-- `bytesToTyped` around a general-spec forger. -/
noncomputable def bytesToTypedG (A : GBytesForger ds vp prims codec optRand pkSeedDist) :
    GForger ds vp prims optRand pkSeedDist :=
  ⟨wrapFam ds (Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist))
    (bytesView vp prims codec optRand pkSeedDist).encPk
    (Coded.readForgery (bytesView vp prims codec optRand pkSeedDist) (constSig default)) A.main⟩

/-- `bytesToTypedS` around a general-spec strong forger. -/
noncomputable def bytesToTypedSG (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    GStrongForger ds vp prims optRand pkSeedDist :=
  ⟨wrapFam ds (Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist))
    (bytesView vp prims codec optRand pkSeedDist).encPk
    (Coded.readForgery (bytesView vp prims codec optRand pkSeedDist) (constSig default)) A.main⟩

/-- `pureBytesToTyped` around a general-spec forger. -/
noncomputable def pureBytesToTypedG (A : GPureBytesForger ds vp prims codec optRand pkSeedDist) :
    GExtForger ds vp prims optRand pkSeedDist :=
  ⟨wrapFam ds (Coded.signingImpl (pureBytesView vp prims codec optRand pkSeedDist))
    (pureBytesView vp prims codec optRand pkSeedDist).encPk
    (Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
      (.error (.contextTooLong 0))) A.main⟩

/-- `pureBytesToTypedS` around a general-spec strong forger. -/
noncomputable def pureBytesToTypedSG
    (A : GPureBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    GExtStrongForger ds vp prims optRand pkSeedDist :=
  ⟨wrapFam ds (Coded.signingImpl (pureBytesView vp prims codec optRand pkSeedDist))
    (pureBytesView vp prims codec optRand pkSeedDist).encPk
    (Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
      (.error (.contextTooLong 0))) A.main⟩

/-! ### Families -/

lemma toInternalG_main (A : GExtForger ds vp prims optRand pkSeedDist) :
    (toInternalG ds A).main = wrapFam ds (Guarded.signingImpl pureEncode) id
      (Guarded.readForgery pureEncode ([], constSig default)) A.main := rfl

lemma toInternalSG_main (A : GExtStrongForger ds vp prims optRand pkSeedDist) :
    (toInternalSG ds A).main = wrapFam ds (Guarded.signingImpl pureEncode) id
      (Guarded.readForgery pureEncode ([], constSig default)) A.main := rfl

lemma bytesToTypedG_main (A : GBytesForger ds vp prims codec optRand pkSeedDist) :
    (bytesToTypedG ds A).main =
      wrapFam ds (Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist))
        (bytesView vp prims codec optRand pkSeedDist).encPk
        (Coded.readForgery (bytesView vp prims codec optRand pkSeedDist) (constSig default))
        A.main := rfl

lemma bytesToTypedSG_main (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    (bytesToTypedSG ds A).main =
      wrapFam ds (Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist))
        (bytesView vp prims codec optRand pkSeedDist).encPk
        (Coded.readForgery (bytesView vp prims codec optRand pkSeedDist) (constSig default))
        A.main := rfl

lemma pureBytesToTypedG_main (A : GPureBytesForger ds vp prims codec optRand pkSeedDist) :
    (pureBytesToTypedG ds A).main =
      wrapFam ds (Coded.signingImpl (pureBytesView vp prims codec optRand pkSeedDist))
        (pureBytesView vp prims codec optRand pkSeedDist).encPk
        (Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
          (.error (.contextTooLong 0))) A.main := rfl

lemma pureBytesToTypedSG_main (A : GPureBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    (pureBytesToTypedSG ds A).main =
      wrapFam ds (Coded.signingImpl (pureBytesView vp prims codec optRand pkSeedDist))
        (pureBytesView vp prims codec optRand pkSeedDist).encPk
        (Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
          (.error (.contextTooLong 0))) A.main := rfl

/-! ### Compatibility with `toUnforgeableAdversary` -/

theorem toInternalSG_toUnforgeableAdversary (A : GExtStrongForger ds vp prims optRand pkSeedDist) :
    (toInternalSG ds A).toUnforgeableAdversary = toInternalG ds A.toUnforgeableAdversary := rfl

theorem bytesToTypedSG_toUnforgeableAdversary
    (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    (bytesToTypedSG ds A).toUnforgeableAdversary = bytesToTypedG ds A.toUnforgeableAdversary :=
  rfl

theorem pureBytesToTypedSG_toUnforgeableAdversary
    (A : GPureBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    (pureBytesToTypedSG ds A).toUnforgeableAdversary =
      pureBytesToTypedG ds A.toUnforgeableAdversary := rfl

/-! ### Naturality on classical forgers -/

theorem toInternalG_embed (A : ExtForger vp prims optRand pkSeedDist) :
    toInternalG ds (embedAdv ds A) = embedAdv ds (toInternal A) :=
  congrArg SignatureAlg.UnforgeableAdversary.mk (wrapFam_embed ds _ _ _ A.main)

theorem toInternalSG_embed (A : ExtStrongForger vp prims optRand pkSeedDist) :
    toInternalSG ds (embedAdvS ds A) = embedAdvS ds (toInternalS A) :=
  congrArg SignatureAlg.StrongUnforgeableAdversary.mk (wrapFam_embed ds _ _ _ A.main)

theorem bytesToTypedG_embed (A : BytesForger vp prims codec optRand pkSeedDist) :
    bytesToTypedG ds (embedAdv ds A) = embedAdv ds (bytesToTyped A) :=
  congrArg SignatureAlg.UnforgeableAdversary.mk (wrapFam_embed ds _ _ _ A.main)

theorem bytesToTypedSG_embed (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    bytesToTypedSG ds (embedAdvS ds A) = embedAdvS ds (bytesToTypedS A) :=
  congrArg SignatureAlg.StrongUnforgeableAdversary.mk (wrapFam_embed ds _ _ _ A.main)

theorem pureBytesToTypedG_embed (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    pureBytesToTypedG ds (embedAdv ds A) = embedAdv ds (pureBytesToTyped A) :=
  congrArg SignatureAlg.UnforgeableAdversary.mk (wrapFam_embed ds _ _ _ A.main)

theorem pureBytesToTypedSG_embed (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    pureBytesToTypedSG ds (embedAdvS ds A) = embedAdvS ds (pureBytesToTypedS A) :=
  congrArg SignatureAlg.StrongUnforgeableAdversary.mk (wrapFam_embed ds _ _ _ A.main)

/-! ### Composition -/

/-- The composite external-bytes → internal wrapper as a single `wrapFam`. -/
theorem toInternalG_pureBytesToTypedG_main
    (A : GPureBytesForger ds vp prims codec optRand pkSeedDist) :
    (toInternalG ds (pureBytesToTypedG ds A)).main =
      wrapFam ds
        (compSS (Guarded.signingImpl pureEncode)
          (Coded.signingImpl (pureBytesView vp prims codec optRand pkSeedDist)))
        ((pureBytesView vp prims codec optRand pkSeedDist).encPk ∘ id)
        (Guarded.readForgery pureEncode ([], constSig default) ∘
          Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
            (.error (.contextTooLong 0))) A.main :=
  wrapFam_wrapFam ds _ _ _ _ _ _ A.main

/-- The same for the strong versions (the same family). -/
theorem toInternalSG_pureBytesToTypedSG_main
    (A : GPureBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    (toInternalSG ds (pureBytesToTypedSG ds A)).main =
      wrapFam ds
        (compSS (Guarded.signingImpl pureEncode)
          (Coded.signingImpl (pureBytesView vp prims codec optRand pkSeedDist)))
        ((pureBytesView vp prims codec optRand pkSeedDist).encPk ∘ id)
        (Guarded.readForgery pureEncode ([], constSig default) ∘
          Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
            (.error (.contextTooLong 0))) A.main :=
  wrapFam_wrapFam ds _ _ _ _ _ _ A.main

/-! ### Signing-query budgets -/

omit [Inhabited prims.Y] in
lemma guarded_signingImpl_bound0 (n : ℕ) :
    IsQueryBoundP (Guarded.signingImpl (S := GeneralScheme.SignatureCore vp prims.core)
      pureEncode (Sum.inl n)) (fun i ↦ i.isRight = true) 0 := by
  simp [Guarded.signingImpl]

omit [Inhabited prims.Y] in
lemma guarded_signingImpl_bound1 (x : List Byte × List Byte) :
    IsQueryBoundP (Guarded.signingImpl (S := GeneralScheme.SignatureCore vp prims.core)
      pureEncode (Sum.inr x)) (fun i ↦ i.isRight = true) 1 := by
  simp only [Guarded.signingImpl]
  cases pureEncode x <;> simp

/-- **Resources of `toInternalG`**: at most as many signing queries as `A`. -/
theorem toInternalG_queryBound (A : GExtForger ds vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((toInternalG ds A).main pk) (fun i ↦ i.isRight = true) qs :=
  fun pk ↦ wrapFam_queryBound ds _ _ _ guarded_signingImpl_bound0 guarded_signingImpl_bound1
    A.main qs pk (hA _)

theorem toInternalSG_queryBound (A : GExtStrongForger ds vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((toInternalSG ds A).main pk) (fun i ↦ i.isRight = true) qs :=
  toInternalG_queryBound ds A.toUnforgeableAdversary qs hA

/-- **Resources of `bytesToTypedG`**: at most as many signing queries as `A`. -/
theorem bytesToTypedG_queryBound (A : GBytesForger ds vp prims codec optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((bytesToTypedG ds A).main pk) (fun i ↦ i.isRight = true) qs :=
  fun pk ↦ wrapFam_queryBound ds _ _ _ (fun n ↦ by simp [Coded.signingImpl])
    (fun x ↦ by simp [Coded.signingImpl]) A.main qs pk (hA _)

theorem bytesToTypedSG_queryBound (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((bytesToTypedSG ds A).main pk) (fun i ↦ i.isRight = true) qs :=
  bytesToTypedG_queryBound ds A.toUnforgeableAdversary qs hA

/-- **Resources of `pureBytesToTypedG`**: at most as many signing queries as `A`. -/
theorem pureBytesToTypedG_queryBound (A : GPureBytesForger ds vp prims codec optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((pureBytesToTypedG ds A).main pk) (fun i ↦ i.isRight = true) qs :=
  fun pk ↦ wrapFam_queryBound ds _ _ _ (fun n ↦ by simp [Coded.signingImpl])
    (fun x ↦ by simp [Coded.signingImpl]) A.main qs pk (hA _)

theorem pureBytesToTypedSG_queryBound
    (A : GPureBytesStrongForger ds vp prims codec optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((pureBytesToTypedSG ds A).main pk) (fun i ↦ i.isRight = true) qs :=
  pureBytesToTypedG_queryBound ds A.toUnforgeableAdversary qs hA

/-- Resources of the composite `toInternalG (pureBytesToTypedG A)`. -/
theorem toInternalG_pureBytesToTypedG_queryBound
    (A : GPureBytesForger ds vp prims codec optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((toInternalG ds (pureBytesToTypedG ds A)).main pk)
      (fun i ↦ i.isRight = true) qs :=
  toInternalG_queryBound ds _ qs (pureBytesToTypedG_queryBound ds A qs hA)

/-! ### Advantage transfer -/

variable [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]

/-- **External advantage ≤ internal advantage**, general-spec forgers. -/
theorem external_advantage_leG (A : GExtForger ds vp prims optRand pkSeedDist) :
    eufAdvG ds A ≤ eufAdvG ds (toInternalG ds A) :=
  eufAdvG_wrap_le ds _ _ _ _ _ (fun A₀ ↦ external_advantage_le A₀) A

/-- **External SUF-CMA advantage ≤ internal SUF-CMA advantage**, general-spec forgers. -/
theorem external_strong_advantage_leG (A : GExtStrongForger ds vp prims optRand pkSeedDist) :
    sufAdvG ds A ≤ sufAdvG ds (toInternalSG ds A) :=
  sufAdvG_wrap_le ds _ _ _ _ _ (fun A₀ ↦ external_strong_advantage_le A₀) A

/-- **Byte-level EUF-CMA advantage ≤ typed (internal)**, general-spec forgers. -/
theorem bytes_advantage_leG (A : GBytesForger ds vp prims codec optRand pkSeedDist) :
    eufAdvG ds A ≤ eufAdvG ds (bytesToTypedG ds A) :=
  eufAdvG_wrap_le ds _ _ _ _ _ (fun A₀ ↦ bytes_advantage_le A₀) A

/-- **Byte-level SUF-CMA advantage ≤ typed (internal)**, general-spec forgers. -/
theorem bytes_strong_advantage_leG (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    sufAdvG ds A ≤ sufAdvG ds (bytesToTypedSG ds A) :=
  sufAdvG_wrap_le ds _ _ _ _ _ (fun A₀ ↦ bytes_strong_advantage_le A₀) A

/-- **Byte-level EUF-CMA advantage ≤ typed (external pure)**, general-spec forgers. -/
theorem pure_bytes_advantage_leG (A : GPureBytesForger ds vp prims codec optRand pkSeedDist) :
    eufAdvG ds A ≤ eufAdvG ds (pureBytesToTypedG ds A) :=
  eufAdvG_wrap_le ds _ _ _ _ _ (fun A₀ ↦ pure_bytes_advantage_le A₀) A

/-- **Byte-level SUF-CMA advantage ≤ typed (external pure)**, general-spec forgers. -/
theorem pure_bytes_strong_advantage_leG
    (A : GPureBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    sufAdvG ds A ≤ sufAdvG ds (pureBytesToTypedSG ds A) :=
  sufAdvG_wrap_le ds _ _ _ _ _ (fun A₀ ↦ pure_bytes_strong_advantage_le A₀) A

end slhdsa

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms isLin_sigExpG_wrap
#print axioms eufAdvG_wrap_le
#print axioms sufAdvG_wrap_le
#print axioms toInternalG_embed
#print axioms pureBytesToTypedSG_embed
#print axioms toInternalG_pureBytesToTypedG_main
#print axioms external_advantage_leG
#print axioms external_strong_advantage_leG
#print axioms bytes_advantage_leG
#print axioms bytes_strong_advantage_leG
#print axioms pure_bytes_advantage_leG
#print axioms pure_bytes_strong_advantage_leG
#print axioms wrapFam_queryBound
#print axioms toInternalG_queryBound
#print axioms bytesToTypedG_queryBound
#print axioms toInternalG_pureBytesToTypedG_queryBound
end Axioms
