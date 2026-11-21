import Reduction.Gen.Sem
import VCVio.CryptoFoundations.SignatureAlg

/-!
# Signature experiments over the general sampling interface

A classical scheme `sigAlg : SignatureAlg ProbComp M PK SK S` is run over `gSpec ds = ds + unifSpec`
(`liftAlg`, quantum's `liftSig` at `ds := distSpec`).  VCVio's EUF-CMA / SUF-CMA experiments for
`liftAlg ds sigAlg` are put in the normal form `sigExpG` ("classical keygen; one run of the forger
against the classical stateful signing handler `signH`; classical verification and freshness"),
which

* coincides with the classical VCVio advantage on `embed`ded classical forgers
  (`eufAdvG_embedAdv`, `sufAdvG_embedAdvS`), and
* is an `IsLin` functional of the forger (`isLin_eufAdvG`, `isLin_sufAdvG`).
-/

open OracleComp OracleSpec ENNReal MeasureTheory

namespace Reduction.Gen

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
  {M PK SK S α : Type}

/-- A classical scheme, run over the general sampling interface. -/
def liftAlg (sigAlg : SignatureAlg ProbComp M PK SK S) :
    SignatureAlg (OracleComp (gSpec ds)) M PK SK S where
  keygen := liftR ds sigAlg.keygen
  sign pk sk m := liftR ds (sigAlg.sign pk sk m)
  verify pk m s := liftR ds (sigAlg.verify pk m s)

variable {sigAlg : SignatureAlg ProbComp M PK SK S}

/-- A classical EUF-CMA forger as a forger over the general sampling interface. -/
def embedAdv (A : SignatureAlg.UnforgeableAdversary sigAlg) :
    SignatureAlg.UnforgeableAdversary (liftAlg ds sigAlg) :=
  ⟨fun pk ↦ embed ds (A.main pk)⟩

/-- A classical SUF-CMA forger as a forger over the general sampling interface. -/
def embedAdvS (A : SignatureAlg.StrongUnforgeableAdversary sigAlg) :
    SignatureAlg.StrongUnforgeableAdversary (liftAlg ds sigAlg) :=
  ⟨fun pk ↦ embed ds (A.main pk)⟩

/-- The classical stateful signing handler: uniform queries are forwarded, signing queries are
answered by `sigAlg.sign pk sk` and the returned pair is appended to the log. -/
def signH (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK) :
    QueryImpl (unifSpec + (M →ₒ S)) (StateT (QueryLog (M →ₒ S)) ProbComp)
  | .inl n => fun l ↦ (fun u ↦ (u, l)) <$> (liftM (unifSpec.query n) : ProbComp _)
  | .inr m => fun l ↦ (fun σ ↦ (σ, l ++ [⟨m, σ⟩])) <$> sigAlg.sign pk sk m

/-! ## The stateful handler is VCVio's logged signing oracle -/

/-- Classical: `signH` is VCVio's `runWithSigningOracle`, started from a log prefix. -/
theorem run_simulateQ_signH (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK)
    (oa : OracleComp (unifSpec + (M →ₒ S)) α) (l₀ : QueryLog (M →ₒ S)) :
    (simulateQ (signH sigAlg pk sk) oa).run l₀ =
      (fun x ↦ (x.1, l₀ ++ x.2)) <$> sigAlg.runWithSigningOracle pk sk oa := by
  unfold SignatureAlg.runWithSigningOracle
  induction oa using OracleComp.inductionOn generalizing l₀ with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, WriterT.run_bind',
      simulateQ_spec_query, simulateQ_spec_query]
    rcases t with n | m
    · have h1 : (signH sigAlg pk sk (Sum.inl n)).run l₀ =
          (fun u ↦ (u, l₀)) <$> (liftM (unifSpec.query n) : ProbComp _) := rfl
      have h2 : ((unifSpec.passthrough + sigAlg.signingOracle pk sk) (Sum.inl n)).run =
          (fun u ↦ (u, ([] : QueryLog (M →ₒ S)))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          QueryImpl.id'_apply]
        rfl
      rw [h1, h2]
      simp [ih]
    · have h1 : (signH sigAlg pk sk (Sum.inr m)).run l₀ =
          (fun σ ↦ (σ, l₀ ++ [⟨m, σ⟩])) <$> sigAlg.sign pk sk m := rfl
      have h2 : ((unifSpec.passthrough + sigAlg.signingOracle pk sk) (Sum.inr m)).run =
          (fun σ ↦ (σ, ([⟨m, σ⟩] : QueryLog (M →ₒ S)))) <$> sigAlg.sign pk sk m := by
        simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inr,
          SignatureAlg.signingOracle, QueryImpl.withLogging_apply]
        simp
      rw [h1, h2]
      simp [ih]

/-- General interface: `runG` against `signH` is VCVio's `runWithSigningOracle` for the lifted
scheme, started from a log prefix. -/
theorem runG_signH (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK)
    (oa : OracleComp ((ds + unifSpec) + (M →ₒ S)) α) (l₀ : QueryLog (M →ₒ S)) :
    runG ds (signH sigAlg pk sk) oa l₀ =
      (fun x ↦ (x.1, l₀ ++ x.2)) <$> (liftAlg ds sigAlg).runWithSigningOracle pk sk oa := by
  unfold SignatureAlg.runWithSigningOracle runG
  induction oa using OracleComp.inductionOn generalizing l₀ with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, WriterT.run_bind',
      simulateQ_spec_query, simulateQ_spec_query]
    rcases t with c | m
    · have h1 : (gImpl ds (signH sigAlg pk sk) (Sum.inl c)).run l₀ =
          (fun u ↦ (u, l₀)) <$> (liftM ((gSpec ds).query c) : OracleComp (gSpec ds) _) := by
        rcases c with d | n
        · rfl
        · change liftR ds ((fun u ↦ (u, l₀)) <$> (liftM (unifSpec.query n) : ProbComp _)) = _
          rw [liftR_map, liftR_query]
          rfl
      have h2 : (((gSpec ds).passthrough + (liftAlg ds sigAlg).signingOracle pk sk)
            (Sum.inl c)).run =
          (fun u ↦ (u, ([] : QueryLog (M →ₒ S)))) <$>
            (liftM ((gSpec ds).query c) : OracleComp (gSpec ds) _) := by
        simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          QueryImpl.id'_apply]
        rfl
      rw [h1, h2]
      simp [ih]
    · have h1 : (gImpl ds (signH sigAlg pk sk) (Sum.inr m)).run l₀ =
          (fun σ ↦ (σ, l₀ ++ [⟨m, σ⟩])) <$> liftR ds (sigAlg.sign pk sk m) := by
        change liftR ds ((fun σ ↦ (σ, l₀ ++ [⟨m, σ⟩])) <$> sigAlg.sign pk sk m) = _
        rw [liftR_map]
      have h2 : (((gSpec ds).passthrough + (liftAlg ds sigAlg).signingOracle pk sk)
            (Sum.inr m)).run =
          (fun σ ↦ (σ, ([⟨m, σ⟩] : QueryLog (M →ₒ S)))) <$> liftR ds (sigAlg.sign pk sk m) := by
        simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inr,
          SignatureAlg.signingOracle, QueryImpl.withLogging_apply, liftAlg]
        simp
      rw [h1, h2]
      simp [ih]

/-- The key lemma at the empty log. -/
theorem runWithSigningOracle_liftAlg (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK)
    (oa : OracleComp ((ds + unifSpec) + (M →ₒ S)) α) :
    (liftAlg ds sigAlg).runWithSigningOracle pk sk oa = runG ds (signH sigAlg pk sk) oa [] := by
  rw [runG_signH]; simp

/-- Classical version at the empty log. -/
theorem runWithSigningOracle_eq_signH (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK)
    (oa : OracleComp (unifSpec + (M →ₒ S)) α) :
    sigAlg.runWithSigningOracle pk sk oa = (simulateQ (signH sigAlg pk sk) oa).run [] := by
  rw [run_simulateQ_signH]; simp

/-! ## Normal forms -/

/-- The signature experiment over the general interface, with freshness test `fresh`. -/
noncomputable def sigExpG (sigAlg : SignatureAlg ProbComp M PK SK S)
    (fresh : QueryLog (M →ₒ S) → M → S → Bool)
    (F : PK → OracleComp ((ds + unifSpec) + (M →ₒ S)) (M × S)) : OracleComp (gSpec ds) Bool :=
  liftR ds sigAlg.keygen >>= fun ks ↦
    runG ds (signH sigAlg ks.1 ks.2) (F ks.1) [] >>= fun r ↦
      liftR ds (sigAlg.verify ks.1 r.1.1 r.1.2 >>= fun v ↦ pure (fresh r.2 r.1.1 r.1.2 && v))

/-- The classical signature experiment with freshness test `fresh`. -/
noncomputable def sigExpC (sigAlg : SignatureAlg ProbComp M PK SK S)
    (fresh : QueryLog (M →ₒ S) → M → S → Bool)
    (F : PK → OracleComp (unifSpec + (M →ₒ S)) (M × S)) : ProbComp Bool :=
  sigAlg.keygen >>= fun ks ↦
    (simulateQ (signH sigAlg ks.1 ks.2) (F ks.1)).run [] >>= fun r ↦
      sigAlg.verify ks.1 r.1.1 r.1.2 >>= fun v ↦ pure (fresh r.2 r.1.1 r.1.2 && v)

/-- On embedded classical forgers the general experiment is the lifted classical one. -/
theorem sigExpG_embed (sigAlg : SignatureAlg ProbComp M PK SK S)
    (fresh : QueryLog (M →ₒ S) → M → S → Bool)
    (F : PK → OracleComp (unifSpec + (M →ₒ S)) (M × S)) :
    sigExpG ds sigAlg fresh (fun pk ↦ embed ds (F pk)) = liftR ds (sigExpC sigAlg fresh F) := by
  unfold sigExpG sigExpC
  rw [liftR_bind]
  refine bind_congr fun ks ↦ ?_
  rw [runG_embed, liftR_bind]

open scoped Classical in
theorem unforgeableExperiment_eq (A : SignatureAlg.UnforgeableAdversary (liftAlg ds sigAlg)) :
    SignatureAlg.unforgeableExperiment A =
      sigExpG ds sigAlg (fun log m _ ↦ !log.wasQueried m) A.main := by
  unfold SignatureAlg.unforgeableExperiment sigExpG
  refine bind_congr fun ks ↦ ?_
  obtain ⟨pk, sk⟩ := ks
  dsimp only
  rw [runWithSigningOracle_liftAlg]
  refine bind_congr fun r ↦ ?_
  obtain ⟨⟨m, σ⟩, log⟩ := r
  change liftR ds (sigAlg.verify pk m σ) >>= _ = _
  rw [liftR_bind]
  refine bind_congr fun v ↦ ?_
  rw [liftR_pure]

open scoped Classical in
theorem strongUnforgeableExperiment_eq
    (A : SignatureAlg.StrongUnforgeableAdversary (liftAlg ds sigAlg)) :
    SignatureAlg.strongUnforgeableExperiment A =
      sigExpG ds sigAlg (fun log m σ ↦ !SignatureAlg.signingLogContains log m σ) A.main := by
  unfold SignatureAlg.strongUnforgeableExperiment sigExpG
  refine bind_congr fun ks ↦ ?_
  obtain ⟨pk, sk⟩ := ks
  dsimp only
  rw [runWithSigningOracle_liftAlg]
  refine bind_congr fun r ↦ ?_
  obtain ⟨⟨m, σ⟩, log⟩ := r
  change liftR ds (sigAlg.verify pk m σ) >>= _ = _
  rw [liftR_bind]
  refine bind_congr fun v ↦ ?_
  rw [liftR_pure]

open scoped Classical in
/-- Classical normal form of VCVio's EUF-CMA experiment. -/
theorem unforgeableExperiment_eq_sigExpC (A : SignatureAlg.UnforgeableAdversary sigAlg) :
    SignatureAlg.unforgeableExperiment A =
      sigExpC sigAlg (fun log m _ ↦ !log.wasQueried m) A.main := by
  unfold SignatureAlg.unforgeableExperiment sigExpC
  refine bind_congr fun ks ↦ ?_
  obtain ⟨pk, sk⟩ := ks
  dsimp only
  rw [runWithSigningOracle_eq_signH]

open scoped Classical in
/-- Classical normal form of VCVio's SUF-CMA experiment. -/
theorem strongUnforgeableExperiment_eq_sigExpC
    (A : SignatureAlg.StrongUnforgeableAdversary sigAlg) :
    SignatureAlg.strongUnforgeableExperiment A =
      sigExpC sigAlg (fun log m σ ↦ !SignatureAlg.signingLogContains log m σ) A.main := by
  unfold SignatureAlg.strongUnforgeableExperiment sigExpC
  refine bind_congr fun ks ↦ ?_
  obtain ⟨pk, sk⟩ := ks
  dsimp only
  rw [runWithSigningOracle_eq_signH]

/-! ## Advantages -/

/-- EUF-CMA advantage of a forger over the general sampling interface. -/
noncomputable def eufAdvG (A : SignatureAlg.UnforgeableAdversary (liftAlg ds sigAlg)) : ℝ≥0∞ :=
  prG ds (SignatureAlg.unforgeableExperiment A)

/-- SUF-CMA advantage of a forger over the general sampling interface. -/
noncomputable def sufAdvG (A : SignatureAlg.StrongUnforgeableAdversary (liftAlg ds sigAlg)) :
    ℝ≥0∞ :=
  prG ds (SignatureAlg.strongUnforgeableExperiment A)

lemma eufAdvG_def (A : SignatureAlg.UnforgeableAdversary (liftAlg ds sigAlg)) :
    eufAdvG ds A = 𝒟[SignatureAlg.unforgeableExperiment A] {true} := rfl

lemma sufAdvG_def (A : SignatureAlg.StrongUnforgeableAdversary (liftAlg ds sigAlg)) :
    sufAdvG ds A = 𝒟[SignatureAlg.strongUnforgeableExperiment A] {true} := rfl

open scoped Classical in
lemma eufAdvG_eq_sigExpG (A : SignatureAlg.UnforgeableAdversary (liftAlg ds sigAlg)) :
    eufAdvG ds A = prG ds (sigExpG ds sigAlg (fun log m _ ↦ !log.wasQueried m) A.main) := by
  rw [eufAdvG, unforgeableExperiment_eq]

open scoped Classical in
lemma sufAdvG_eq_sigExpG (A : SignatureAlg.StrongUnforgeableAdversary (liftAlg ds sigAlg)) :
    sufAdvG ds A = prG ds (sigExpG ds sigAlg
      (fun log m σ ↦ !SignatureAlg.signingLogContains log m σ) A.main) := by
  rw [sufAdvG, strongUnforgeableExperiment_eq]

theorem eufAdvG_le_one (A : SignatureAlg.UnforgeableAdversary (liftAlg ds sigAlg)) :
    eufAdvG ds A ≤ 1 := prG_le_one ds _

theorem sufAdvG_le_one (A : SignatureAlg.StrongUnforgeableAdversary (liftAlg ds sigAlg)) :
    sufAdvG ds A ≤ 1 := prG_le_one ds _

/-! ## Coincidence at classical forgers -/

/-- On an embedded classical forger, the general EUF-CMA advantage is the classical one. -/
theorem eufAdvG_embedAdv (A : SignatureAlg.UnforgeableAdversary sigAlg) :
    eufAdvG ds (embedAdv ds A) =
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A := by
  classical
  rw [eufAdvG_eq_sigExpG]
  change prG ds (sigExpG ds sigAlg _ (fun pk ↦ embed ds (A.main pk))) = _
  rw [sigExpG_embed, prG_liftR, SignatureAlg.unforgeableAdvantage,
    ProbCompRuntime.probComp_evalDist, unforgeableExperiment_eq_sigExpC]
  rfl

/-- On an embedded classical forger, the general SUF-CMA advantage is the classical one. -/
theorem sufAdvG_embedAdvS (A : SignatureAlg.StrongUnforgeableAdversary sigAlg) :
    sufAdvG ds (embedAdvS ds A) =
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A := by
  classical
  rw [sufAdvG_eq_sigExpG]
  change prG ds (sigExpG ds sigAlg _ (fun pk ↦ embed ds (A.main pk))) = _
  rw [sigExpG_embed, prG_liftR, SignatureAlg.strongUnforgeableAdvantage,
    ProbCompRuntime.probComp_evalDist, strongUnforgeableExperiment_eq_sigExpC]
  rfl

/-! ## Linearity -/

/-- The signature experiment is a linear functional of the forger. -/
theorem isLin_sigExpG (sigAlg : SignatureAlg ProbComp M PK SK S)
    (fresh : QueryLog (M →ₒ S) → M → S → Bool) :
    IsLin ds (wOf ds) 1 (fun F : PK → OracleComp ((ds + unifSpec) + (M →ₒ S)) (M × S) ↦
      prG ds (sigExpG ds sigAlg fresh F)) :=
  isLin_liftR_bind ds sigAlg.keygen
    (fun ks F ↦ runG ds (signH sigAlg ks.1 ks.2) (F ks.1) [] >>= fun r : (M × S) × QueryLog (M →ₒ S) ↦
      liftR ds (sigAlg.verify ks.1 r.1.1 r.1.2 >>= fun v ↦ pure (fresh r.2 r.1.1 r.1.2 && v)))
    (fun ks ↦ isLin_run ds (signH sigAlg ks.1 ks.2) ks.1 []
      (fun r : (M × S) × QueryLog (M →ₒ S) ↦ sigAlg.verify ks.1 r.1.1 r.1.2 >>= fun v ↦ pure (fresh r.2 r.1.1 r.1.2 && v)))

theorem isLin_eufAdvG (sigAlg : SignatureAlg ProbComp M PK SK S) :
    IsLin ds (wOf ds) 1 (fun F : PK → OracleComp ((ds + unifSpec) + (M →ₒ S)) (M × S) ↦
      eufAdvG ds (sigAlg := sigAlg) ⟨F⟩) := by
  classical
  simpa only [eufAdvG_eq_sigExpG] using
    isLin_sigExpG ds sigAlg (fun log m _ ↦ !log.wasQueried m)

theorem isLin_sufAdvG (sigAlg : SignatureAlg ProbComp M PK SK S) :
    IsLin ds (wOf ds) 1 (fun F : PK → OracleComp ((ds + unifSpec) + (M →ₒ S)) (M × S) ↦
      sufAdvG ds (sigAlg := sigAlg) ⟨F⟩) := by
  classical
  simpa only [sufAdvG_eq_sigExpG] using
    isLin_sigExpG ds sigAlg (fun log m σ ↦ !SignatureAlg.signingLogContains log m σ)

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms runG_signH
#print axioms unforgeableExperiment_eq
#print axioms strongUnforgeableExperiment_eq
#print axioms eufAdvG_embedAdv
#print axioms sufAdvG_embedAdvS
#print axioms isLin_sigExpG
#print axioms isLin_eufAdvG
#print axioms isLin_sufAdvG
#print axioms eufAdvG_le_one
end Axioms
