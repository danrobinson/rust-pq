import Reduction.Tables
import Reduction.Harness
import HashSig.SLHDSA.Security.WeakKeyBound

/-!
# Step 1: the `PRF` hop (`G0 → G1`)

`bPrf A` is the distinguisher (EC: `R_SKGPRF_EUFCMA`).  It samples `PK.seed`, `SK.prf`,
runs key generation and every signing query through VCVio's provider-parametric programs with the
secret provider `a ↦ O(PK.seed, a)`, runs `A` once, and outputs "`A` forged".  It is the only
adversary of `Reduction/Final.lean` that is polynomial in `qs` as written:
`2^h'·len + qs·(k·2^a + d·2^h'·len)` PRF queries (`17920 + qs·182784` at 128s,
`Resources.keygenReads_128s`, `signReads_128s`); its local hash evaluations (one XMSS tree, and
per signature one FORS instance and `d` XMSS trees) are not counted by any lemma.  Its game
`skPrf` has the oracle domain all of `Adrs` and is false at SHA2-128s; `Reduction.bPrfC`
(`Reduction/PrfDomain.lean`) is the same distinguisher in the game on secret-key addresses.

Proof plan (see `REDUCTION_STATUS.md`, package P1):
1. real world: `O = PRF(·, SK.seed, ·)`; by the `*_eq_*` theorems of `SecretProvider` the run is
   `G0` (`prfReal_bPrf`);
2. ideal world: `O` is a lazy random function; every secret read is at a FIPS-canonical
   secret-key address (`SecretTraces.*_pred_of_ledger`), on which `secIdx` is injective, so the
   lazy function may be replaced by the eagerly sampled table (`prfIdeal_bPrf`), which is `G1`.

Both worlds go through one program identity, `rest_sim`: answering the provider queries of `bPrf`
by a function `h` gives the EUF-CMA run against any scheme whose root and signer are the
`h`-interpretations of the provider programs (`internalAlg` for `h = PRF(·, SK.seed, ·)`,
`tableAlg` for `h = tbl ∘ secIdx`).

Query count (`bPrf_queryBound_exact`): `2^h'·len + qs·(k·2^a + d·2^h'·len)`; the frozen budget
`skPrfQueries` is a (slightly loose) upper bound of it.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The `PRF` distinguisher built from a forger. -/
noncomputable def bPrf (A : Forger vp prims optRand pkSeedDist) : SkPrfAdv prims :=
  letI : HasQuery (publicHashSpec prims.core)
      (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
    ⟨fun q => pure (PublicHash.impl prims q)⟩
  let secret (pkSeed : prims.PkSeed) (a : Adrs) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y :=
    PRFScheme.functionQuery (pkSeed, a)
  ((do
    let pkSeed ← (monadLift pkSeedDist :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.PkSeed)
    let skPrf ← (monadLift ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.SkPrf)
    let root ← (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core (secret pkSeed)
      pkSeed : OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
    let pk : PublicKeyCore prims.core := ⟨pkSeed, root⟩
    let ((msg, sig), msgs) ← runForger A pk fun m => do
      let addrnd ← (monadLift (optRand pk) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
      (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core (secret pkSeed) m
        pkSeed root (prims.PRFmsg skPrf addrnd m) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
          (GeneralScheme.SignatureCore vp prims.core))
    return harnessValid pk msgs msg sig) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool)

/-- Secret values read by key generation plus `qs` signatures (an upper bound):
`2^h'·len` for the top tree, and per signature `k·2^a` FORS leaves and, per layer, the
`2^h'` WOTS+ key generations plus one WOTS+ signature.  The exact count is smaller by
`qs·d·len` (the authentication path skips the signing leaf): see `bPrf_queryBound_exact`. -/
def skPrfQueries (vp : ValidatedParams) (qs : ℕ) : ℕ :=
  2 ^ vp.params.hp * vp.params.len +
    qs * (vp.params.k * 2 ^ vp.params.a +
      vp.params.d * ((2 ^ vp.params.hp + 1) * vp.params.len))

/-- Public-hash queries inside the PRF distinguisher are evaluated by `prims`. -/
@[reducible] private def prfQ (prims : Primitives vp.params) : HasQuery (publicHashSpec prims.core)
    (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

/-- Public-hash queries in `ProbComp` are evaluated by `prims`. -/
@[reducible] private def probQ (prims : Primitives vp.params) :
    HasQuery (publicHashSpec prims.core) ProbComp :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

attribute [local instance] prfQ probQ

/-- `fnImpl h` as a public-hash-preserving monad morphism. -/
private noncomputable def fnHom (h : prims.PkSeed × Adrs → prims.Y) :
    HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) ProbComp :=
  { toMonadHom := simulateQ' (Tables.fnImpl h)
    map_query' := fun q => by
      simp }

private theorem free_apply {α : Type} (oa : OracleComp (publicHashSpec prims.core) α) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
      (m := ProbComp)).toMonadHom oa = pure (simulateQ (PublicHash.impl prims) oa) := by
  have hImpl : HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp) =
      (PublicHash.impl prims).liftTarget ProbComp := by
    funext q
    rfl
  rw [HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
  rfl

/-- Key generation with the provider answered by `h`. -/
private theorem keygen_sim (h : prims.PkSeed × Adrs → prims.Y) (pkSeed : prims.PkSeed) :
    simulateQ (Tables.fnImpl h)
      (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) =
      pure (simulateQ (PublicHash.impl prims)
        (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
          (fun a => pure (h (pkSeed, a))) pkSeed :
          OracleComp (publicHashSpec prims.core) prims.Y)) := by
  have h1 := GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core (fnHom h)
    (fun a => PRFScheme.functionQuery (pkSeed, a)) (fun a => pure (h (pkSeed, a)))
    (fun a _ => Tables.simulateQ_fnImpl_functionQuery h (pkSeed, a)) pkSeed
  have h2 := GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))
    (fun a => pure (h (pkSeed, a))) (fun a => pure (h (pkSeed, a)))
    (fun a _ => by simp) pkSeed
  rw [free_apply] at h2
  exact h1.trans h2.symm

private theorem sign_sim (h : prims.PkSeed × Adrs → prims.Y) (pkSeed : prims.PkSeed)
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
    (fnHom h)
    (fun a => PRFScheme.functionQuery (pkSeed, a)) (fun a => pure (h (pkSeed, a)))
    (fun a _ => Tables.simulateQ_fnImpl_functionQuery h (pkSeed, a)) msg pkSeed pkRoot R
  have h2 := GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp) prims.core
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))
    (fun a => pure (h (pkSeed, a))) (fun a => pure (h (pkSeed, a)))
    (fun a _ => by simp) msg pkSeed pkRoot R
  rw [free_apply] at h2
  exact h1.trans h2.symm

/-- The signing procedure `bPrf` hands to the harness. -/
private noncomputable def bSign (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
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

/-- Everything `bPrf A` does after sampling `PK.seed`. -/
private noncomputable def bRest (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool := do
  let skPrf ← (monadLift ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.SkPrf)
  let root ← (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
    (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
  let z ← runForger A ⟨pkSeed, root⟩ (bSign optRand ⟨pkSeed, root⟩ skPrf)
  return harnessValid ⟨pkSeed, root⟩ z.2 z.1.1 z.1.2

private theorem bPrf_eq (A : Forger vp prims optRand pkSeedDist) :
    bPrf A = (liftM pkSeedDist :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.PkSeed) >>=
        bRest A := rfl

/-- Answering the provider by `h` turns the harness run into a run against the signing oracle of
any scheme whose signing algorithm is the `h`-interpretation of the harness's signer. -/
private theorem run_eq {SK : Type} (A : Forger vp prims optRand pkSeedDist)
    (alg : SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) SK
      (GeneralScheme.SignatureCore vp prims.core))
    (h : prims.PkSeed × Adrs → prims.Y) (pk : PublicKeyCore prims.core) (sk : SK)
    (sign : List Byte → OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
      (GeneralScheme.SignatureCore vp prims.core))
    (hsign : ∀ m, simulateQ (Tables.fnImpl h) (sign m) = alg.sign pk sk m) :
    simulateQ (Tables.fnImpl h) (runForger A pk sign) =
      (fun z => (z.1, z.2.map (fun e => e.1))) <$>
        (alg.runWithSigningOracle pk sk (A.main pk)) := by
  have hh := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog (spec₀ := unifSpec)
    (alg.sign pk sk) (A.main pk) []
  dsimp only at hh
  unfold runForger
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  have hH : (Tables.fnImpl h).mapStateTBase
      (QueryImpl.liftTarget (StateT (List (List Byte))
          (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)))
        (QueryImpl.ofLift unifSpec
          (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))) +
        harnessSignOracle sign) =
      (QueryImpl.liftTarget (StateT (List (List Byte)) ProbComp)
          (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
        QueryImpl.appendInputLog (alg.sign pk sk)) := by
    funext t
    cases t with
    | inl n =>
      refine StateT.ext fun s => ?_
      simp [QueryImpl.mapStateTBase]
      exact Tables.simulateQ_fnImpl_liftM h (liftM (unifSpec.query n))
    | inr m =>
      refine StateT.ext fun s => ?_
      simp [QueryImpl.mapStateTBase, harnessSignOracle, hsign]
  rw [hH]
  refine Eq.trans hh.symm ?_
  simp [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle]
  rfl

private theorem lift_sim (h : prims.PkSeed × Adrs → prims.Y) {β : Type} (ob : ProbComp β) :
    simulateQ (Tables.fnImpl h) (monadLift ob :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) β) = ob :=
  Tables.simulateQ_fnImpl_liftM h ob

/-- `bRest` under a provider function `h`, for any scheme `alg` whose public root and signing
algorithm are the `h`-interpretations of the provider programs. -/
private theorem rest_sim {SK : Type} (A : Forger vp prims optRand pkSeedDist)
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
    simulateQ (Tables.fnImpl h) (bRest A pkSeed) = (do
      let skPrf ← $ᵗ prims.SkPrf
      let z ← alg.runWithSigningOracle ⟨pkSeed, root⟩ (sk skPrf) (A.main ⟨pkSeed, root⟩)
      pure (harnessValid ⟨pkSeed, root⟩ (z.2.map (fun e => e.1)) z.1.1 z.1.2)) := by
  unfold bRest
  simp only [simulateQ_bind, simulateQ_pure]
  rw [lift_sim]
  refine bind_congr fun skPrf => ?_
  rw [keygen_sim, hroot, pure_bind]
  rw [run_eq A alg h ⟨pkSeed, root⟩ (sk skPrf) _ (fun m => ?_)]
  · simp
  · unfold bSign
    simp only [simulateQ_bind]
    rw [lift_sim, ← hsign skPrf m]
    refine bind_congr fun addrnd => ?_
    exact sign_sim h pkSeed m root _

private theorem keygenInternal_eq (k : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    GeneralScheme.keygenInternal vp prims k skPrf pkSeed =
      (⟨pkSeed, simulateQ (PublicHash.impl prims)
        (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
          (fun a => pure (prims.PRF pkSeed k a)) pkSeed :
          OracleComp (publicHashSpec prims.core) prims.Y)⟩,
       ⟨k, skPrf, pkSeed, simulateQ (PublicHash.impl prims)
        (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
          (fun a => pure (prims.PRF pkSeed k a)) pkSeed :
          OracleComp (publicHashSpec prims.core) prims.Y)⟩) := by
  unfold GeneralScheme.keygenInternalWithSecretM
  rw [GeneralHypertree.rootWithSecretM_eq_rootM]
  unfold GeneralScheme.keygenInternal GeneralScheme.keygenInternalM
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

/-- Real world of the PRF game at `bPrf A` is `G0`. -/
theorem prfReal_bPrf (A : Forger vp prims optRand pkSeedDist) :
    𝒟[(skPrf vp prims).prfRealExperiment (bPrf A)] {true} = prTrue (g0 A) := by
  have hL : (skPrf vp prims).prfRealExperiment (bPrf A) = (do
      let k ← $ᵗ prims.SkSeed
      let pkSeed ← pkSeedDist
      let skPrf ← $ᵗ prims.SkPrf
      let kp := GeneralScheme.keygenInternal vp prims k skPrf pkSeed
      let z ← (internalAlg vp prims optRand pkSeedDist).runWithSigningOracle kp.1 kp.2
        (A.main kp.1)
      pure (harnessValid kp.1 (z.2.map (fun e => e.1)) z.1.1 z.1.2)) := by
    unfold PRFScheme.prfRealExperiment
    rw [bPrf_eq]
    refine bind_congr fun k => ?_
    change simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => prims.PRF d.1 k d.2) _ = _
    rw [simulateQ_bind, Tables.simulateQ_fnImpl_liftM]
    refine bind_congr fun pkSeed => ?_
    simp only [keygenInternal_eq]
    refine rest_sim A (internalAlg vp prims optRand pkSeedDist) _ pkSeed _
      (fun skPrf => ⟨k, skPrf, pkSeed, _⟩) rfl fun skPrf m => ?_
    simp only [internalAlg]
    refine bind_congr fun addrnd => ?_
    rw [GeneralScheme.signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM]
    rfl
  have hR : g0 A = (do
      let pkSeed ← pkSeedDist
      let k ← $ᵗ prims.SkSeed
      let skPrf ← $ᵗ prims.SkPrf
      let kp := GeneralScheme.keygenInternal vp prims k skPrf pkSeed
      let z ← (internalAlg vp prims optRand pkSeedDist).runWithSigningOracle kp.1 kp.2
        (A.main kp.1)
      pure (harnessValid kp.1 (z.2.map (fun e => e.1)) z.1.1 z.1.2)) := by
    unfold g0 SignatureAlg.unforgeableExperiment
    simp [internalAlg, harnessValid, QueryLog.wasQueried_eq_decide_mem_map_fst]
    refine bind_congr fun pkSeed => bind_congr fun k => bind_congr fun skPrf => ?_
    congr!
  rw [hL, hR, prTrue]
  congr 1
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-! ## Ideal world -/

/-- `secIdx` is injective on FIPS-canonical addresses. -/
theorem secIdx_injOn_canonical : Set.InjOn secIdx {a : Adrs | a.isCanonical = true} := by
  intro a ha b hb h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Adrs.fits_of_isCanonical a ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := Adrs.fits_of_isCanonical b hb
  rw [Adrs.fits_iff] at a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
  have h' := congrArg Fin.val h
  simp only [secIdx, Fin.ofNat] at h'
  norm_num at a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 h'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  apply Adrs.ext <;> omega


/-- Every secret child of a ledger address is FIPS-canonical. -/
private theorem canonical_of_secretChild (hb : CanonicalAddressBounds vp.params) {a b : Adrs}
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

/-- The function queries of `bRest A pkSeed` are at `PK.seed = pkSeed` and canonical addresses. -/
private theorem queriesIn_bRest (hb : CanonicalAddressBounds vp.params)
    (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed) :
    Tables.QueriesIn {d : prims.PkSeed × Adrs | d.1 = pkSeed ∧ d.2.isCanonical = true}
      (bRest A pkSeed) := by
  set S : Set (prims.PkSeed × Adrs) := {d | d.1 = pkSeed ∧ d.2.isCanonical = true} with hSdef
  have hsecret : ∀ a b, b ∈ constructionAddresses vp → .inl a ∈ childAdrs vp b →
      Tables.QueriesIn S (PRFScheme.functionQuery (pkSeed, a) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) :=
    fun a b hmem hab =>
      Tables.queriesIn_functionQuery ⟨rfl, canonical_of_secretChild hb hmem hab⟩
  unfold bRest
  refine Tables.queriesIn_bind (Tables.queriesIn_liftM S _) fun skPrf => ?_
  refine Tables.queriesIn_bind ?_ fun root => ?_
  · exact keygenInternalWithSecretM_pred_of_ledger
      (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
      (fun {α} oa => Tables.QueriesIn S oa) (fun x => Tables.queriesIn_pure S x)
      (fun oa ob h1 h2 => Tables.queriesIn_bind h1 h2) prims.core hsecret pkSeed
      (fun a _ xs => Tables.queriesIn_pure S _)
  refine Tables.queriesIn_bind ?_ fun z => Tables.queriesIn_pure S _
  unfold runForger
  refine AllQueriesSatisfy.simulateQ_run (P := fun _ => True)
    (allQueriesSatisfy_of_forall (fun _ => trivial) _) (fun t _ s => ?_) []
  cases t with
  | inl n =>
    simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    exact Tables.queriesIn_bind (Tables.queriesIn_liftM S (liftM (unifSpec.query n)))
      fun x => Tables.queriesIn_pure S _
  | inr m =>
    simp [harnessSignOracle, bSign]
    refine Tables.queriesIn_bind (Tables.queriesIn_liftM S _) fun addrnd => ?_
    rw [map_eq_bind_pure_comp]
    refine Tables.queriesIn_bind ?_ fun sig => Tables.queriesIn_pure S _
    exact signInternalWithSecretRandomizerM_pred_of_ledger
      (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
      (fun {α} oa => Tables.QueriesIn S oa) (fun x => Tables.queriesIn_pure S x)
      (fun oa ob h1 h2 => Tables.queriesIn_bind h1 h2) prims.core hsecret m pkSeed root _
      (fun a _ xs => Tables.queriesIn_pure S _) (Tables.queriesIn_pure S _)

/-- Ideal world of the PRF game at `bPrf A` is `G1`. -/
theorem prfIdeal_bPrf (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    𝒟[PRFScheme.prfIdealExperiment (bPrf A)] {true} = prTrue (g1 A) := by
  have key := evalDist_prfIdeal_eq_sampleTable (vp := vp) (prims := prims)
    secIdx_injOn_canonical pkSeedDist id (bRest A)
    (fun s _ => queriesIn_bRest hS.bounds A s)
  have hR : g1 A = (pkSeedDist >>= fun s => sampleTable vp prims >>= fun tbl =>
      simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => secretOf vp prims tbl d.2)
        (bRest A s)) := by
    have hrest : ∀ (s : prims.PkSeed) (tbl : SecretTable vp prims),
        simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => secretOf vp prims tbl d.2)
          (bRest A s) = (do
        let skPrf ← $ᵗ prims.SkPrf
        let z ← (tableAlg vp prims optRand pkSeedDist).runWithSigningOracle
          (idealPk vp prims tbl s) (tbl, skPrf) (A.main (idealPk vp prims tbl s))
        pure (harnessValid (idealPk vp prims tbl s) (z.2.map (fun e => e.1)) z.1.1 z.1.2)) :=
      fun s tbl => rest_sim A (tableAlg vp prims optRand pkSeedDist) _ s
        (idealRoot vp prims tbl s) (fun skPrf => (tbl, skPrf)) rfl (fun skPrf m => rfl)
    simp only [hrest]
    unfold g1 SignatureAlg.unforgeableExperiment
    simp [tableAlg, harnessValid, QueryLog.wasQueried_eq_decide_mem_map_fst]
    refine bind_congr fun pkSeed => bind_congr fun tbl => bind_congr fun k => ?_
    congr!
  rw [prTrue, hR]
  exact congrArg (· {true}) key

/-! ## Query count -/

section Count

variable {ι : Type} {spec : OracleSpec ι} (core : CorePrimitives vp.params)
  {hash : Adrs → core.Y → OracleComp spec core.Y}
  {compress : Adrs → List core.Y → OracleComp spec core.Y}
  {nodeHash : Adrs → core.Y → core.Y → OracleComp spec core.Y}
  {secret : Adrs → OracleComp spec core.Y}

private theorem tqb0_pure {α : Type} (x : α) : IsTotalQueryBound (pure x : OracleComp spec α) 0 :=
  trivial

private theorem tqb0_bind {α β : Type} (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (h1 : IsTotalQueryBound oa 0) (h2 : ∀ x, IsTotalQueryBound (ob x) 0) :
    IsTotalQueryBound (oa >>= ob) 0 :=
  isTotalQueryBound_bind h1 h2

private theorem tqb_ofFnM {α : Type} {k : ℕ} (g : Fin k → OracleComp spec α) (c : ℕ)
    (h : ∀ i, IsTotalQueryBound (g i) c) : IsTotalQueryBound (Vector.ofFnM g) (k * c) := by
  induction k with
  | zero =>
      rw [Vector.ofFnM_zero]
      trivial
  | succ k ih =>
      rw [Vector.ofFnM_succ]
      refine (isTotalQueryBound_bind (ih (fun i => g i.castSucc) (fun i => h i.castSucc))
        fun xs => isTotalQueryBound_bind (n₂ := 0) (h (Fin.last k)) fun a => tqb0_pure _).mono ?_
      rw [Nat.succ_mul]
      omega

variable (hhash : ∀ a y, IsTotalQueryBound (hash a y) 0)
  (hcompress : ∀ a ys, IsTotalQueryBound (compress a ys) 0)
  (hnode : ∀ a l r, IsTotalQueryBound (nodeHash a l r) 0)
  (hsecret : ∀ a, IsTotalQueryBound (secret a) 1)

include hhash in
private theorem chain_tqb (adrs : Adrs) (x : core.Y) (i s : ℕ) :
    IsTotalQueryBound (chainWith hash adrs x i s) 0 :=
  chainWith_pred (m := OracleComp spec) (fun oa => IsTotalQueryBound oa 0) tqb0_pure tqb0_bind
    x i s fun _ _ y => hhash _ y

include hhash hsecret in
private theorem wotsTops_tqb (adrs : Adrs) :
    IsTotalQueryBound (wotsPkGenTopsWithSecret core hash secret adrs) vp.params.len := by
  have h := tqb_ofFnM (fun i : Fin vp.params.len => do
      let x ← secret (wotsSkAdrs adrs i.val)
      chainWith hash (wotsChainAdrs adrs i.val) x 0 (vp.params.w - 1)) 1
    (fun i => isTotalQueryBound_bind (hsecret _) fun x => chain_tqb core hhash _ x _ _)
  rw [Nat.mul_one] at h
  exact h

include hhash hsecret in
private theorem wotsSign_tqb (msg : core.Y) (adrs : Adrs) :
    IsTotalQueryBound (wotsSignWithSecret core hash secret msg adrs) vp.params.len := by
  have h := tqb_ofFnM (fun i : Fin vp.params.len => do
      let x ← secret (wotsSkAdrs adrs i.val)
      chainWith hash (wotsChainAdrs adrs i.val) x 0 (chainStepsCore core msg i.val)) 1
    (fun i => isTotalQueryBound_bind (hsecret _) fun x => chain_tqb core hhash _ x _ _)
  rw [Nat.mul_one] at h
  exact h

include hhash hcompress hsecret in
private theorem wotsPkGen_tqb (adrs : Adrs) :
    IsTotalQueryBound (wotsPkGenWithSecret core hash compress secret adrs) vp.params.len :=
  isTotalQueryBound_bind (n₂ := 0) (wotsTops_tqb core hhash hsecret adrs) fun _ => hcompress _ _

include hhash hcompress hnode hsecret in
private theorem xmssNode_tqb (adrs : Adrs) (z t : ℕ) :
    IsTotalQueryBound (xmssNodeWithSecret core hash compress nodeHash secret adrs z t)
      (2 ^ z * vp.params.len) := by
  have h := PerfectMerkleTree.isTotalQueryBound_merkleRootM
    (xmssLeafWithSecret core hash compress secret adrs) (xmssNodeHashWith nodeHash adrs)
    vp.params.len 0 z t (fun i => wotsPkGen_tqb core hhash hcompress hsecret _)
    (fun h i l r => hnode _ l r)
  rw [Nat.mul_zero, Nat.add_zero] at h
  exact h

include hhash hcompress hnode hsecret in
private theorem xmssSign_tqb (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound (xmssSignWithSecret core hash compress nodeHash secret msg adrs idx)
      (2 ^ vp.params.hp * vp.params.len) := by
  have h := PerfectMerkleTree.isTotalQueryBound_intrinsicAuthPathM
    (xmssLeafWithSecret core hash compress secret adrs) (xmssNodeHashWith nodeHash adrs)
    vp.params.len 0 idx vp.params.hp (fun i => wotsPkGen_tqb core hhash hcompress hsecret _)
    (fun h i l r => hnode _ l r)
  refine (isTotalQueryBound_bind h fun path => isTotalQueryBound_bind
    (wotsSign_tqb core hhash hsecret msg _) fun sig => tqb0_pure _).mono ?_
  have hpos : 0 < 2 ^ vp.params.hp := pow_pos (by decide) _
  have : 2 ^ vp.params.hp * vp.params.len =
      (2 ^ vp.params.hp - 1) * vp.params.len + vp.params.len := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hpos)]
  omega

include hhash hcompress hnode in
private theorem xmssPk_tqb (idx : ℕ) (sig : XmssSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    IsTotalQueryBound (xmssPkFromSigWith core hash compress nodeHash idx sig msg adrs) 0 :=
  xmssPkFromSigWith_pred (m := OracleComp spec) (fun oa => IsTotalQueryBound oa 0)
    tqb0_pure tqb0_bind core (fun a _ y => hhash a y) (fun a _ ys => hcompress a ys)
    (fun a _ l r => hnode a l r) idx sig msg adrs

include hhash hcompress hnode hsecret in
private theorem signFromPos_tqb (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      IsTotalQueryBound (GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash
        secret recoverFinal pos layers h msg) (layers * (2 ^ vp.params.hp * vp.params.len))
  | 0, _, _ => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      trivial
  | 1, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine (isTotalQueryBound_bind (n₂ := 0)
        (xmssSign_tqb core hhash hcompress hnode hsecret msg _ _) fun sig => ?_).mono (by omega)
      cases recoverFinal
      · exact tqb0_pure _
      · exact tqb0_bind _ _ (xmssPk_tqb core hhash hcompress hnode _ sig msg _) fun _ =>
          tqb0_pure _
  | layers + 2, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine (isTotalQueryBound_bind (xmssSign_tqb core hhash hcompress hnode hsecret msg _ _)
        fun sig => isTotalQueryBound_bind (xmssPk_tqb core hhash hcompress hnode _ sig msg _)
          fun root => isTotalQueryBound_bind
            (signFromPos_tqb false _ (layers + 1) _ root) fun _ => tqb0_pure _).mono ?_
      exact Nat.le_of_eq (by ring)

include hhash hnode hsecret in
private theorem forsSign_tqb (md : List Byte) (adrs : Adrs) :
    IsTotalQueryBound (forsSignWithSecret core hash nodeHash secret md adrs)
      (vp.params.k * 2 ^ vp.params.a) := by
  refine tqb_ofFnM _ _ fun i => ?_
  have h := PerfectMerkleTree.isTotalQueryBound_intrinsicAuthPathM
    (forsLeafWithSecret core hash secret adrs) (forsNodeHashWith nodeHash adrs)
    1 0 (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) vp.params.a
    (fun j => isTotalQueryBound_bind (hsecret _) fun x => hhash _ x)
    (fun h i l r => hnode _ l r)
  refine (isTotalQueryBound_bind (hsecret _) fun sk => isTotalQueryBound_bind h
    fun path => tqb0_pure _).mono ?_
  have hpos : 0 < 2 ^ vp.params.a := pow_pos (by decide) _
  omega

include hhash hcompress hnode in
private theorem forsPk_tqb (sig : ForsSigCore vp.params core) (md : List Byte) (adrs : Adrs) :
    IsTotalQueryBound (forsPkFromSigWith core hash nodeHash compress sig md adrs) 0 :=
  forsPkFromSigWith_pred (m := OracleComp spec) (fun oa => IsTotalQueryBound oa 0)
    tqb0_pure tqb0_bind core (fun a _ y => hhash a y) (fun a _ ys => hcompress a ys)
    (fun a _ l r => hnode a l r) sig md adrs

end Count

/-- Secret values read by one signature: `k·2^a` FORS leaves and `2^h'·len` WOTS+ values in each
of the `d` layers. -/
def signReads (vp : ValidatedParams) : ℕ :=
  vp.params.k * 2 ^ vp.params.a + vp.params.d * (2 ^ vp.params.hp * vp.params.len)

private theorem functionQuery_tqb (d : prims.PkSeed × Adrs) :
    IsTotalQueryBound (PRFScheme.functionQuery d :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) 1 := by
  simp [PRFScheme.functionQuery, IsTotalQueryBound]

private theorem keygen_tqb (pkSeed : prims.PkSeed) :
    IsTotalQueryBound (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
      (2 ^ vp.params.hp * vp.params.len) :=
  xmssNode_tqb prims.core (fun _ _ => tqb0_pure _) (fun _ _ => tqb0_pure _)
    (fun _ _ _ => tqb0_pure _) (fun a => functionQuery_tqb (pkSeed, a)) _ _ _

private theorem sign_tqb (pkSeed : prims.PkSeed) (msg : List Byte) (pkRoot R : prims.Y) :
    IsTotalQueryBound (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pkSeed, a)) msg pkSeed pkRoot R :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
          (GeneralScheme.SignatureCore vp prims.core))
      (signReads vp) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsTotalQueryBound (PublicHash.f prims.core pkSeed a y :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) 0 :=
    fun _ _ => tqb0_pure _
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsTotalQueryBound (PublicHash.tl prims.core pkSeed a ys :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) 0 :=
    fun _ _ => tqb0_pure _
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsTotalQueryBound (PublicHash.h prims.core pkSeed a l r :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) 0 :=
    fun _ _ _ => tqb0_pure _
  have hs := fun a : Adrs => functionQuery_tqb (prims := prims) (pkSeed, a)
  unfold GeneralScheme.signInternalWithSecretRandomizerM
  refine (isTotalQueryBound_bind (n₁ := 0) (tqb0_pure _) fun digest =>
    isTotalQueryBound_bind (forsSign_tqb prims.core hf hh hs _ _) fun forsSig =>
      isTotalQueryBound_bind (forsPk_tqb prims.core hf htl hh forsSig _ _) fun forsPk =>
        isTotalQueryBound_bind (signFromPos_tqb prims.core hf htl hh hs _ _ _ _ _) fun htSig =>
          tqb0_pure _).mono ?_
  unfold signReads
  omega

/-- **Step 1.** -/
theorem stepPRF (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    StepPRF A (bPrf A) := by
  unfold StepPRF
  rw [← prfReal_bPrf, ← prfIdeal_bPrf hS, PRFScheme.prfAdvantage]
  exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _

/-- A query-free continuation does not change the bound. -/
private theorem queryBound_bind_pure {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (p : ι → Prop) [DecidablePred p] (oa : OracleComp spec α) (f : α → OracleComp spec β) (n : ℕ)
    (h : IsQueryBoundP oa p n) (hf : ∀ x, ∃ b, f x = pure b) :
    IsQueryBoundP (oa >>= f) p n := by
  have key := isQueryBoundP_bind (ob := f) (m := 0) h fun x _ => by
    obtain ⟨b, hb⟩ := hf x
    rw [hb]; exact isQueryBoundP_pure _ _ _
  simpa only [Nat.add_zero] using key

/-- The exact count: `bPrf A` reads `2^h'·len` secret values in key generation and
`signReads vp = k·2^a + d·2^h'·len` in each signature. -/
theorem bPrf_queryBound_exact (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrf A) (fun i => i.isRight = true)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) := by
  rw [bPrf_eq]
  have key := isQueryBoundP_bind
    (isQueryBoundP_liftM_isRight
      (hs := (prims.PkSeed × Adrs) →ₒ prims.Y) pkSeedDist) fun pkSeed _ =>
    isQueryBoundP_bind (ob := fun skPrf => (GeneralScheme.keygenInternalWithSecretM (vp := vp)
          prims.core (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
          OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) >>=
        fun root => runForger A ⟨pkSeed, root⟩ (bSign optRand ⟨pkSeed, root⟩ skPrf) >>= fun z =>
          pure (harnessValid (vp := vp) (prims := prims) ⟨pkSeed, root⟩ z.2 z.1.1 z.1.2))
      (isQueryBoundP_liftM_isRight (hs := (prims.PkSeed × Adrs) →ₒ prims.Y)
        ($ᵗ prims.SkPrf : ProbComp prims.SkPrf)) fun skPrf _ =>
      isQueryBoundP_bind ((keygen_tqb (vp := vp) (prims := prims) pkSeed).isQueryBoundP
        (p := fun i => Sum.isRight i = true)) fun root _ =>
        queryBound_bind_pure (fun i => Sum.isRight i = true) _ _ (qs * signReads vp) ?_
          (fun x => ⟨_, rfl⟩)
  · rw [Nat.zero_add, Nat.zero_add] at key
    exact key
  unfold runForger
  refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
  · cases t with
    | inl n => simp at ht
    | inr m =>
      have hstep := isQueryBoundP_bind (m := signReads vp)
        (isQueryBoundP_liftM_isRight (hs := (prims.PkSeed × Adrs) →ₒ prims.Y)
          (optRand ⟨pkSeed, root⟩)) fun addrnd _ =>
        queryBound_bind_pure (fun i => Sum.isRight i = true)
          (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
            (fun a => PRFScheme.functionQuery (pkSeed, a)) m pkSeed root
            (prims.PRFmsg skPrf addrnd m) :
            OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
              (GeneralScheme.SignatureCore vp prims.core))
          (fun sig => pure (sig, s ++ [m])) (signReads vp)
          ((sign_tqb pkSeed m root _).isQueryBoundP) (fun x => ⟨_, rfl⟩)
      simpa [harnessSignOracle, bSign] using hstep
  · cases t with
    | inl n =>
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
      refine queryBound_bind_pure _ _ _ _ ?_ (fun x => ⟨_, rfl⟩)
      exact isQueryBoundP_liftM_isRight (liftM (unifSpec.query n) : ProbComp _)
    | inr m => simp at ht

/-- Resource lemma: if `A` makes at most `qs` signing queries, `bPrf A` makes at most
`skPrfQueries vp qs` queries to its function oracle. -/
theorem bPrf_queryBound (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrf A) (fun i => i.isRight = true) (skPrfQueries vp qs) := by
  refine (bPrf_queryBound_exact A qs hA).mono ?_
  unfold skPrfQueries signReads
  refine Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_succ _))) _)) _

#print axioms Reduction.secIdx_injOn_canonical
#print axioms Reduction.prfReal_bPrf
#print axioms Reduction.prfIdeal_bPrf
#print axioms Reduction.stepPRF
#print axioms Reduction.bPrf_queryBound_exact
#print axioms Reduction.bPrf_queryBound

end Reduction
