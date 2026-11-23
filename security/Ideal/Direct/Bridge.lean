import Ideal.Direct.ExtractWots
import Ideal.Direct.Tagged

/-!
# The bridge: the real experiment at the `PRF` table (D3/D4 of `status/DIRECT.md`)

Over any `Structural` bundle: the chosen-message experiment against the **real** scheme
(`expW realAlg w A`, secrets `PRF(PK.seed, SK.seed, ·)`, randomizers `PRF_msg(SK.prf, ·, ·)`)
is, exactly (no `PRF` advantage is charged), the experiment against the table scheme at the
**`PRF` table** `prfTbl pkSeed k` (`secretOf (prfTbl pkSeed k) a = PRF(pkSeed, k, a)` at every
canonical address).  With the signing transcript recorded as a `G2Log` (`g1Run`), the
strong-forgery check is `sufWin` of `Reduction/Suf.lean`, so the `G2`-level extraction
(`suf_extract_full`) applies pathwise.

* `prfTbl`, `secretOf_prfTbl`;
* `expW_real_eq_prfTbl`: `Pr[expW realAlg w A] = Pr[pkSeed, k, SK.prf; run against tableAlg
  at prfTbl pkSeed k; w]`;
* `g1Run` (the forger against the deterministic-randomizer signer of a table, transcript
  `(M, opt_rand, R)`), `g1Run_proj` (it projects to `tableAlg.runWithSigningOracle`);
* `sufCheck_g1` (`sufCheck` of the projected log is `sufWin`), and **`suf_real_eq_sufWin`**:
  `Pr[expW realAlg sufCheck A] = Pr[pkSeed, k, SK.prf; z ← g1Run; sufWin pkSeed (prfTbl pkSeed k) z]`;
* **`suf_real_le_extract`**: the same probability is at most that of
  `evItsr ∨ evColl ∨ evHidF ∨ evHidW` at the `PRF` table.

The proof of `expW_real_eq_prfTbl` re-uses the program `bPrfW` and its real-world equation
`prfReal_bPrfW` (`Reduction/SufHopPrf.lean`); the private lemmas of that file it needs
(`keygen_sim`, `sign_sim`, `run_eq`, `rest_sim`, the canonical-address `QueriesIn` lemma) are
**copied** below (suffix `B`), restated for the canonical-address set without the seed condition.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

namespace Direct

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The `PRF` table -/

open Classical in
/-- The secret table of the key `k` at the seed `pkSeed`: at the index of a canonical address,
the `PRF` value there. -/
noncomputable def prfTbl (pkSeed : prims.PkSeed) (k : prims.SkSeed) : SecretTable vp prims :=
  fun idx => if h : ∃ a : Adrs, a.isCanonical = true ∧ secIdx a = idx then
    prims.PRF pkSeed k (Classical.choose h) else default

theorem secretOf_prfTbl (pkSeed : prims.PkSeed) (k : prims.SkSeed) (a : Adrs)
    (ha : a.isCanonical = true) :
    secretOf vp prims (prfTbl pkSeed k) a = prims.PRF pkSeed k a := by
  have hex : ∃ a' : Adrs, a'.isCanonical = true ∧ secIdx a' = secIdx a := ⟨a, ha, rfl⟩
  unfold secretOf prfTbl
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hs := Classical.choose_spec hex
  rw [secIdx_injOn_canonical hs.1 ha hs.2]

/-! ## Copied from `Reduction/SufHopPrf.lean` (private there) -/

section Copied

@[reducible] private def prfQB (prims : Primitives vp.params) : HasQuery (publicHashSpec prims.core)
    (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

@[reducible] private def probQB (prims : Primitives vp.params) :
    HasQuery (publicHashSpec prims.core) ProbComp :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

attribute [local instance] prfQB probQB

private noncomputable def fnHomB (h : prims.PkSeed × Adrs → prims.Y) :
    HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) ProbComp :=
  { toMonadHom := simulateQ' (Tables.fnImpl h)
    map_query' := fun q => by
      simp }

private theorem free_applyB {α : Type} (oa : OracleComp (publicHashSpec prims.core) α) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
      (m := ProbComp)).toMonadHom oa = pure (simulateQ (PublicHash.impl prims) oa) := by
  have hImpl : HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp) =
      (PublicHash.impl prims).liftTarget ProbComp := by
    funext q
    rfl
  rw [HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
  rfl

private theorem keygen_simB (h : prims.PkSeed × Adrs → prims.Y) (pkSeed : prims.PkSeed) :
    simulateQ (Tables.fnImpl h)
      (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) =
      pure (simulateQ (PublicHash.impl prims)
        (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
          (fun a => pure (h (pkSeed, a))) pkSeed :
          OracleComp (publicHashSpec prims.core) prims.Y)) := by
  have h1 := GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core (fnHomB h)
    (fun a => PRFScheme.functionQuery (pkSeed, a)) (fun a => pure (h (pkSeed, a)))
    (fun a _ => Tables.simulateQ_fnImpl_functionQuery h (pkSeed, a)) pkSeed
  have h2 := GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))
    (fun a => pure (h (pkSeed, a))) (fun a => pure (h (pkSeed, a)))
    (fun a _ => by simp) pkSeed
  rw [free_applyB] at h2
  exact h1.trans h2.symm

private theorem sign_simB (h : prims.PkSeed × Adrs → prims.Y) (pkSeed : prims.PkSeed)
    (msg : List Byte) (pkRoot R : prims.Y) :
    simulateQ (Tables.fnImpl h)
      (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pkSeed, a)) msg pkSeed pkRoot R :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
          (GeneralScheme.SignatureCore vp prims.core)) =
      pure (simulateQ (PublicHash.impl prims)
        (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
          (fun a => pure (h (pkSeed, a))) msg pkSeed pkRoot R :
          OracleComp (publicHashSpec prims.core) (GeneralScheme.SignatureCore vp prims.core))) := by
  have h1 := GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp) prims.core
    (fnHomB h)
    (fun a => PRFScheme.functionQuery (pkSeed, a)) (fun a => pure (h (pkSeed, a)))
    (fun a _ => Tables.simulateQ_fnImpl_functionQuery h (pkSeed, a)) msg pkSeed pkRoot R
  have h2 := GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp) prims.core
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))
    (fun a => pure (h (pkSeed, a))) (fun a => pure (h (pkSeed, a)))
    (fun a _ => by simp) msg pkSeed pkRoot R
  rw [free_applyB] at h2
  exact h1.trans h2.symm

private noncomputable def bSignB (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) (m : List Byte) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
      (GeneralScheme.SignatureCore vp prims.core) := do
  let addrnd ← (monadLift (optRand pk) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
  (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
    (fun a => PRFScheme.functionQuery (pk.pkSeed, a)) m pk.pkSeed pk.pkRoot
    (prims.PRFmsg skPrf addrnd m) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
      (GeneralScheme.SignatureCore vp prims.core))

private noncomputable def bRestB (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pkSeed : prims.PkSeed) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool := do
  let skPrf ← (monadLift ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.SkPrf)
  let root ← (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
    (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
  let z ← runForgerSig A ⟨pkSeed, root⟩ (bSignB optRand ⟨pkSeed, root⟩ skPrf)
  return w ⟨pkSeed, root⟩ z.1 z.2

private theorem bPrfW_eqB (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    bPrfW w A = (liftM pkSeedDist :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.PkSeed) >>=
        bRestB w A := rfl

private theorem run_eqB {SK : Type} (A : Forger vp prims optRand pkSeedDist)
    (alg : SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) SK
      (GeneralScheme.SignatureCore vp prims.core))
    (h : prims.PkSeed × Adrs → prims.Y) (pk : PublicKeyCore prims.core) (sk : SK)
    (sign : List Byte → OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
      (GeneralScheme.SignatureCore vp prims.core))
    (hsign : ∀ m, simulateQ (Tables.fnImpl h) (sign m) = alg.sign pk sk m) :
    simulateQ (Tables.fnImpl h) (runForgerSig A pk sign) =
      alg.runWithSigningOracle pk sk (A.main pk) := by
  rw [runWithSigningOracle_eq_appendLog]
  unfold runForgerSig
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  have hH : (Tables.fnImpl h).mapStateTBase
      (QueryImpl.liftTarget (StateT (SigLog vp prims)
          (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)))
        (QueryImpl.ofLift unifSpec
          (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))) +
        sigSignOracle sign) =
      (QueryImpl.liftTarget (StateT (SigLog vp prims) ProbComp)
          (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
        appendLog (alg.sign pk sk)) := by
    funext t
    cases t with
    | inl n =>
      refine StateT.ext fun s => ?_
      simp [QueryImpl.mapStateTBase]
      exact Tables.simulateQ_fnImpl_liftM h (liftM (unifSpec.query n))
    | inr m =>
      refine StateT.ext fun s => ?_
      simp [QueryImpl.mapStateTBase, sigSignOracle, appendLog, hsign]
  rw [hH]

private theorem lift_simB (h : prims.PkSeed × Adrs → prims.Y) {β : Type} (ob : ProbComp β) :
    simulateQ (Tables.fnImpl h) (monadLift ob :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) β) = ob :=
  Tables.simulateQ_fnImpl_liftM h ob

private theorem rest_simB {SK : Type} (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist)
    (alg : SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) SK
      (GeneralScheme.SignatureCore vp prims.core))
    (h : prims.PkSeed × Adrs → prims.Y) (pkSeed : prims.PkSeed) (root : prims.Y)
    (sk : prims.SkPrf → SK)
    (hroot : simulateQ (PublicHash.impl prims)
        (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
          (fun a => pure (h (pkSeed, a))) pkSeed :
          OracleComp (publicHashSpec prims.core) prims.Y) = root)
    (hsign : ∀ skPrf m, (do
        let addrnd ← optRand ⟨pkSeed, root⟩
        pure (simulateQ (PublicHash.impl prims)
          (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
            (fun a => pure (h (pkSeed, a))) m pkSeed root (prims.PRFmsg skPrf addrnd m) :
            OracleComp (publicHashSpec prims.core) (GeneralScheme.SignatureCore vp prims.core)))) =
        alg.sign ⟨pkSeed, root⟩ (sk skPrf) m) :
    simulateQ (Tables.fnImpl h) (bRestB w A pkSeed) = (do
      let skPrf ← $ᵗ prims.SkPrf
      let z ← alg.runWithSigningOracle ⟨pkSeed, root⟩ (sk skPrf) (A.main ⟨pkSeed, root⟩)
      pure (w ⟨pkSeed, root⟩ z.1 z.2)) := by
  unfold bRestB
  simp only [simulateQ_bind, simulateQ_pure]
  rw [lift_simB]
  refine bind_congr fun skPrf => ?_
  rw [keygen_simB, hroot, pure_bind]
  rw [run_eqB A alg h ⟨pkSeed, root⟩ (sk skPrf) _ (fun m => ?_)]
  unfold bSignB
  simp only [simulateQ_bind]
  rw [lift_simB, ← hsign skPrf m]
  refine bind_congr fun addrnd => ?_
  exact sign_simB h pkSeed m root _

private theorem canonical_of_secretChildB (hb : CanonicalAddressBounds vp.params) {a b : Adrs}
    (hmem : b ∈ constructionAddresses vp) (h : .inl a ∈ childAdrs vp b) :
    a.isCanonical = true := by
  rcases List.mem_append.1 (mem_secretChildren_of_inl_mem_childAdrs hmem h) with h1 | h2
  · obtain ⟨⟨pos, i⟩, -, rfl⟩ := List.mem_map.1 h1
    exact (addressFacts_wotsSkAdrs hb pos i).canonical
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 h2
    have hc := (addressFacts_forsLeafAddresses vp hb b' hb').canonical
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := Adrs.fits_of_isCanonical b' hc
    simp [Adrs.isCanonical, forsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setTreeIndex, Adrs.getKeyPairAddress, f1, f2, f4, f6]
    exact ⟨by decide, by decide⟩

/-- The function queries of `bRestB w A pkSeed` are at canonical addresses. -/
private theorem queriesIn_bRestB (hb : CanonicalAddressBounds vp.params) (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed) :
    Tables.QueriesIn {d : prims.PkSeed × Adrs | d.2.isCanonical = true} (bRestB w A pkSeed) := by
  set S : Set (prims.PkSeed × Adrs) := {d | d.2.isCanonical = true} with hSdef
  have hsecret : ∀ a b, b ∈ constructionAddresses vp → .inl a ∈ childAdrs vp b →
      Tables.QueriesIn S (PRFScheme.functionQuery (pkSeed, a) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) :=
    fun a b hmem hab =>
      Tables.queriesIn_functionQuery (canonical_of_secretChildB hb hmem hab)
  unfold bRestB
  refine Tables.queriesIn_bind (Tables.queriesIn_liftM S _) fun skPrf => ?_
  refine Tables.queriesIn_bind ?_ fun root => ?_
  · exact keygenInternalWithSecretM_pred_of_ledger
      (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
      (fun {α} oa => Tables.QueriesIn S oa) (fun x => Tables.queriesIn_pure S x)
      (fun oa ob h1 h2 => Tables.queriesIn_bind h1 h2) prims.core hsecret pkSeed
      (fun a _ xs => Tables.queriesIn_pure S _)
  refine Tables.queriesIn_bind ?_ fun z => Tables.queriesIn_pure S _
  unfold runForgerSig
  refine AllQueriesSatisfy.simulateQ_run (P := fun _ => True)
    (allQueriesSatisfy_of_forall (fun _ => trivial) _) (fun t _ s => ?_) []
  cases t with
  | inl n =>
    simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    exact Tables.queriesIn_bind (Tables.queriesIn_liftM S (liftM (unifSpec.query n)))
      fun x => Tables.queriesIn_pure S _
  | inr m =>
    simp [sigSignOracle, appendLog, bSignB]
    refine Tables.queriesIn_bind (Tables.queriesIn_liftM S _) fun addrnd => ?_
    rw [map_eq_bind_pure_comp]
    refine Tables.queriesIn_bind ?_ fun sig => Tables.queriesIn_pure S _
    exact signInternalWithSecretRandomizerM_pred_of_ledger
      (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
      (fun {α} oa => Tables.QueriesIn S oa) (fun x => Tables.queriesIn_pure S x)
      (fun oa ob h1 h2 => Tables.queriesIn_bind h1 h2) prims.core hsecret m pkSeed root _
      (fun a _ xs => Tables.queriesIn_pure S _) (Tables.queriesIn_pure S _)

end Copied

/-! ## The real experiment at the `PRF` table -/

/-- **The real experiment is the table experiment at the `PRF` table** (exact). -/
theorem expW_real_eq_prfTbl (hS : Structural vp prims) (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prTrue (expW (realAlg vp prims optRand pkSeedDist) w A) =
      prTrue (pkSeedDist >>= fun pkSeed => ($ᵗ prims.SkSeed : ProbComp prims.SkSeed) >>= fun k =>
        ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) >>= fun skPrf =>
          (tableAlg vp prims optRand pkSeedDist).runWithSigningOracle
            (idealPk vp prims (prfTbl pkSeed k) pkSeed) (prfTbl pkSeed k, skPrf)
            (A.main (idealPk vp prims (prfTbl pkSeed k) pkSeed)) >>= fun z =>
          pure (w (idealPk vp prims (prfTbl pkSeed k) pkSeed) z.1 z.2)) := by
  rw [← prfReal_bPrfW]
  unfold PRFScheme.prfRealExperiment
  have hk : ∀ k : prims.SkSeed,
      simulateQ ((skPrf vp prims).prfRealQueryImpl k) (bPrfW w A) =
        (pkSeedDist >>= fun pkSeed => ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) >>= fun skPrf =>
          (tableAlg vp prims optRand pkSeedDist).runWithSigningOracle
            (idealPk vp prims (prfTbl pkSeed k) pkSeed) (prfTbl pkSeed k, skPrf)
            (A.main (idealPk vp prims (prfTbl pkSeed k) pkSeed)) >>= fun z =>
          pure (w (idealPk vp prims (prfTbl pkSeed k) pkSeed) z.1 z.2)) := by
    intro k
    change simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => prims.PRF d.1 k d.2) _ = _
    rw [bPrfW_eqB, simulateQ_bind, Tables.simulateQ_fnImpl_liftM]
    refine bind_congr fun pkSeed => ?_
    rw [Tables.simulateQ_fnImpl_congr (queriesIn_bRestB hS.bounds w A pkSeed)
      (h₂ := fun d => secretOf vp prims (prfTbl d.1 k) d.2)
      (fun d hd => (secretOf_prfTbl d.1 k d.2 hd).symm)]
    exact rest_simB w A (tableAlg vp prims optRand pkSeedDist) _ pkSeed
      (idealRoot vp prims (prfTbl pkSeed k) pkSeed) (fun skPrf => (prfTbl pkSeed k, skPrf)) rfl
      (fun skPrf m => rfl)
  simp only [hk]
  rw [prTrue]
  congr 1
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-! ## The deterministic-randomizer transcript -/

/-- The signing oracle of the table scheme with the randomizer `PRF_msg(SK.prf, opt_rand, M)`,
recording `(M, opt_rand, R)`. -/
noncomputable def g1SignOracle (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pk : PublicKeyCore prims.core) (tbl : SecretTable vp prims) (skPrf : prims.SkPrf) :
    QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT (G2Log prims) ProbComp) :=
  fun msg => StateT.mk fun log =>
    (fun addrnd => (idealSign vp prims tbl msg pk (prims.PRFmsg skPrf addrnd msg),
      log ++ [(msg, addrnd, prims.PRFmsg skPrf addrnd msg)])) <$> optRand pk

/-- The forger against `g1SignOracle`; returns the forgery and the transcript. -/
noncomputable def g1Run (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) :
    ProbComp ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  (simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
      g1SignOracle optRand pk tbl skPrf) (A.main pk)).run []

/-- The signature log of a transcript. -/
def toSigLog (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core) (log : G2Log prims) :
    SigLog vp prims :=
  log.map fun e => ⟨e.1, idealSign vp prims tbl e.1 pk e.2.2⟩

/-- **The transcript projects to the signing log of the table scheme.** -/
theorem g1Run_proj (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) :
    (fun z => (z.1, toSigLog tbl pk z.2)) <$> g1Run A tbl pk skPrf =
      (tableAlg vp prims optRand pkSeedDist).runWithSigningOracle pk (tbl, skPrf) (A.main pk) := by
  rw [runWithSigningOracle_eq_appendLog]
  unfold g1Run
  have h := Ideal.Direct.run_proj
    ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (SigLog vp prims) ProbComp) +
      appendLog ((tableAlg vp prims optRand pkSeedDist).sign pk (tbl, skPrf)))
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
      g1SignOracle optRand pk tbl skPrf) (toSigLog tbl pk) ?_ (A.main pk) []
  · exact h
  intro t s
  rcases t with n | m
  · simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    simp [Functor.map_map]
  · simp only [QueryImpl.add_apply_inr]
    rw [run_appendLog_apply]
    simp only [g1SignOracle, StateT.run_mk, Functor.map_map, tableAlg, bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_apply]
    refine bind_congr fun addrnd => ?_
    simp [toSigLog]

open scoped Classical in
/-- `sufCheck` of the projected log is `sufWin`. -/
theorem sufCheck_toSigLog (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims)
    (z : G2Out vp prims) :
    sufCheck (idealPk vp prims tbl pkSeed) z.1 (toSigLog tbl (idealPk vp prims tbl pkSeed) z.2) =
      sufWin pkSeed tbl z := by
  unfold sufCheck sufWin verifies SignatureAlg.signingLogContains
  congr 1
  have hmem : (⟨z.1.1, z.1.2⟩ : (_ : List Byte) × GeneralScheme.SignatureCore vp prims.core) ∈
      toSigLog tbl (idealPk vp prims tbl pkSeed) z.2 ↔ z.1 ∈ g2Returned pkSeed tbl z.2 := by
    unfold toSigLog g2Returned
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, he, heq⟩
      refine ⟨e, he, ?_⟩
      have h1 := congrArg Sigma.fst heq
      have h2 := Sigma.ext_iff.mp heq
      exact Prod.ext h1 (eq_of_heq h2.2)
    · rintro ⟨e, he, heq⟩
      refine ⟨e, he, ?_⟩
      rw [← heq]
  by_cases h : z.1 ∈ g2Returned pkSeed tbl z.2
  · have h' := hmem.2 h
    simp [h, h']
  · have h' : ¬ _ := fun hh => h (hmem.1 hh)
    simp [h, h']

/-- **The real SUF experiment as the `G2` strong-forgery predicate at the `PRF` table.** -/
theorem suf_real_eq_sufWin (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (expW (realAlg vp prims optRand pkSeedDist) sufCheck A) =
      prTrue (pkSeedDist >>= fun pkSeed => ($ᵗ prims.SkSeed : ProbComp prims.SkSeed) >>= fun k =>
        ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) >>= fun skPrf =>
          g1Run A (prfTbl pkSeed k) (idealPk vp prims (prfTbl pkSeed k) pkSeed) skPrf >>= fun z =>
          pure (sufWin pkSeed (prfTbl pkSeed k) z)) := by
  rw [expW_real_eq_prfTbl hS]
  congr 1
  refine bind_congr fun pkSeed => bind_congr fun k => bind_congr fun skPrf => ?_
  rw [← g1Run_proj, bind_map_left]
  refine bind_congr fun z => ?_
  rw [sufCheck_toSigLog]

open scoped Classical in
/-- **Extraction at the `PRF` table.**  The real SUF experiment wins with at most the
probability that, at the `PRF` table of its key, the run is Cover, Hit, or HiddenEq. -/
theorem suf_real_le_extract (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (expW (realAlg vp prims optRand pkSeedDist) sufCheck A) ≤
      prTrue (pkSeedDist >>= fun pkSeed => ($ᵗ prims.SkSeed : ProbComp prims.SkSeed) >>= fun k =>
        ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) >>= fun skPrf =>
          g1Run A (prfTbl pkSeed k) (idealPk vp prims (prfTbl pkSeed k) pkSeed) skPrf >>= fun z =>
          pure (decide (evItsr pkSeed (prfTbl pkSeed k) z = true ∨
            evColl pkSeed (prfTbl pkSeed k) z = true ∨
            evHidF pkSeed (prfTbl pkSeed k) z ∨ evHidW pkSeed (prfTbl pkSeed k) z))) := by
  rw [suf_real_eq_sufWin hS]
  refine prTrue_bind_mono _ _ _ fun pkSeed _ => prTrue_bind_mono _ _ _ fun k _ =>
    prTrue_bind_mono _ _ _ fun skPrf _ => prTrue_bind_pure_mono _ _ _ fun z _ hw => ?_
  exact decide_eq_true (suf_extract_full hS pkSeed _ z hw)

end Direct

end Reduction

#print axioms Reduction.Direct.secretOf_prfTbl
#print axioms Reduction.Direct.expW_real_eq_prfTbl
#print axioms Reduction.Direct.g1Run_proj
#print axioms Reduction.Direct.suf_real_eq_sufWin
#print axioms Reduction.Direct.suf_real_le_extract
