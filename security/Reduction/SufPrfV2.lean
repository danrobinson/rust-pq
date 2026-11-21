import Reduction.PrfDomain
import Reduction.SufHopPrf

/-!
# The SUF-CMA `PRF` distinguisher on the secret-key address domain

`bPrfW w A` (`Reduction.SufHopPrf`) is the `PRF` distinguisher of the strong-unforgeability proof;
it plays the old game `skPrf`, whose oracle domain is all of `Adrs` and which is false at
SHA2-128s (`skPrf_broken_128s`).  This file ports it to the game `skPrfC` on the secret-key
address domain `SkAdrs vp`, exactly as `Reduction.PrfDomain` does for `bPrf`:

* `prfAdvantageC_eq_of` — the generic statement: for any distinguisher of the form
  "sample `PK.seed`, then a program all of whose function queries are at that seed and at
  addresses of `SkDom vp`", the wrapper `Restrict.restrictImpl (skRestrict vp prims)` preserves
  the advantage (old game ↦ new game) exactly;
* `bPrfWC w A`, `prfAdvantageC_bPrfWC`, `bPrfWC_queryBound_exact` — the instance at `bPrfW w A`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## Generic: the wrapper preserves the advantage -/

section Generic

variable (pkSeedDist)
variable (rest : prims.PkSeed →
  OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool)

/-- "Sample `PK.seed`, then run `rest`", as a program of the old PRF oracle interface. -/
def seedThen : OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool :=
  (liftM pkSeedDist :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.PkSeed) >>= rest

theorem simulateQ_fnImpl_wrapped_of
    (hq : ∀ s, Tables.QueriesIn {d : prims.PkSeed × Adrs | d.1 = s ∧ SkDom vp d.2} (rest s))
    (s : prims.PkSeed)
    (h : prims.PkSeed × SkAdrs vp → prims.Y) (h' : prims.PkSeed × Adrs → prims.Y)
    (hh : ∀ (pk : prims.PkSeed) (a : SkAdrs vp), h (pk, a) = h' (pk, a.val)) :
    simulateQ (Tables.fnImpl h)
        (simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (rest s)) =
      simulateQ (Tables.fnImpl h') (rest s) := by
  rw [Restrict.simulateQ_fnImpl_restrict]
  refine Tables.simulateQ_fnImpl_congr (hq s) fun d hd => ?_
  unfold Restrict.pull
  rw [skRestrict_of_dom hd.2]
  exact hh d.1 ⟨d.2, hd.2⟩

theorem restrict_liftM_bind :
    simulateQ (Restrict.restrictImpl (skRestrict vp prims))
        (seedThen pkSeedDist rest) =
      (liftM pkSeedDist :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) prims.PkSeed) >>=
          fun s => simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (rest s) := by
  unfold seedThen
  rw [simulateQ_bind, Restrict.simulateQ_restrict_liftM]

/-- **The domain-restricting wrapper preserves the PRF advantage** of every distinguisher that
samples `PK.seed` and then queries only at that seed and at secret-key addresses. -/
theorem prfAdvantageC_eq_of
    (hq : ∀ s, Tables.QueriesIn {d : prims.PkSeed × Adrs | d.1 = s ∧ SkDom vp d.2} (rest s)) :
    (skPrfC vp prims).prfAdvantage
        (simulateQ (Restrict.restrictImpl (skRestrict vp prims))
          (seedThen pkSeedDist rest)) =
      (skPrf vp prims).prfAdvantage
        (seedThen pkSeedDist rest) := by
  have hreal : (skPrfC vp prims).prfRealExperiment
        (simulateQ (Restrict.restrictImpl (skRestrict vp prims))
          (seedThen pkSeedDist rest)) =
      (skPrf vp prims).prfRealExperiment
        (seedThen pkSeedDist rest) := by
    unfold PRFScheme.prfRealExperiment
    refine bind_congr fun k => ?_
    change simulateQ (Tables.fnImpl fun d : prims.PkSeed × SkAdrs vp => prims.PRF d.1 k d.2.val) _ =
      simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => prims.PRF d.1 k d.2) _
    rw [restrict_liftM_bind]
    unfold seedThen
    rw [simulateQ_bind, simulateQ_bind, Tables.simulateQ_fnImpl_liftM,
      Tables.simulateQ_fnImpl_liftM]
    exact bind_congr fun s => simulateQ_fnImpl_wrapped_of rest hq s _ _ fun _ _ => rfl
  have hideal : 𝒟[PRFScheme.prfIdealExperiment
        (simulateQ (Restrict.restrictImpl (skRestrict vp prims))
          (seedThen pkSeedDist rest))] =
      𝒟[PRFScheme.prfIdealExperiment
        (seedThen pkSeedDist rest)] := by
    have hold : 𝒟[PRFScheme.prfIdealExperiment
          (seedThen pkSeedDist rest)] =
        𝒟[pkSeedDist >>= fun s => sampleTable vp prims >>= fun tbl =>
          simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => secretOf vp prims tbl d.2)
            (rest s)] :=
      evalDist_prfIdeal_eq_sampleTable (vp := vp) (prims := prims)
        secIdx_injOn_canonical pkSeedDist id rest
        (fun s _ => (hq s).mono fun t => by
          rcases t with n | d
          · exact fun h => h
          · exact fun h => ⟨h.1, h.2.1⟩)
    have hnew : 𝒟[PRFScheme.prfIdealExperiment
          (simulateQ (Restrict.restrictImpl (skRestrict vp prims))
            (seedThen pkSeedDist rest))] =
        𝒟[pkSeedDist >>= fun s => sampleTable vp prims >>= fun tbl =>
          simulateQ (Tables.fnImpl fun d : prims.PkSeed × SkAdrs vp => tbl (secIdx d.2.val))
            (simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (rest s))] := by
      unfold PRFScheme.prfIdealExperiment
      rw [restrict_liftM_bind]
      exact Tables.evalDist_prfIdealExperiment_liftM_bind pkSeedDist
        (fun s => simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (rest s))
        (fun _ d => secIdx d.2.val) (fun s => {d : prims.PkSeed × SkAdrs vp | d.1 = s})
        (fun s _ d hd d' hd' h => Prod.ext (hd.trans hd'.symm)
          (Subtype.ext (secIdx_injOn_canonical d.2.2.1 d'.2.2.1 h)))
        (fun s _ => Restrict.queriesIn_restrict _ (S := {d | d.1 = s ∧ SkDom vp d.2})
          (fun d hd d' hd' => by
            rw [skRestrict_of_dom hd.2] at hd'
            cases hd'
            exact hd.1) (hq s))
    rw [hold, hnew]
    refine congrArg _ (bind_congr fun s => bind_congr fun tbl => ?_)
    exact simulateQ_fnImpl_wrapped_of rest hq s _ _ fun _ _ => rfl
  unfold PRFScheme.prfAdvantage
  rw [hreal, hideal]

end Generic

/-! ## The instance at `bPrfW w A` -/

@[reducible] private def prfQW (prims : Primitives vp.params) :
    HasQuery (publicHashSpec prims.core)
      (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

attribute [local instance] prfQW

/-- The signing procedure `bPrfW` hands to the harness (copy of the private `bSign`). -/
noncomputable def bSignW (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
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

/-- Everything `bPrfW w A` does after sampling `PK.seed` (copy of the private `bRest`). -/
noncomputable def bRestW (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pkSeed : prims.PkSeed) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool := do
  let skPrf ← (monadLift ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.SkPrf)
  let root ← (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
    (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
  let z ← runForgerSig A ⟨pkSeed, root⟩ (bSignW optRand ⟨pkSeed, root⟩ skPrf)
  return w ⟨pkSeed, root⟩ z.1 z.2

theorem bPrfW_eq_bRestW (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    bPrfW w A = seedThen pkSeedDist (bRestW w A) := rfl

/-- The function queries of `bRestW w A pkSeed` are at `PK.seed = pkSeed` and addresses of the
secret-key domain. -/
theorem queriesIn_bRestW (hb : CanonicalAddressBounds vp.params) (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed) :
    Tables.QueriesIn {d : prims.PkSeed × Adrs | d.1 = pkSeed ∧ SkDom vp d.2}
      (bRestW w A pkSeed) := by
  set S : Set (prims.PkSeed × Adrs) := {d | d.1 = pkSeed ∧ SkDom vp d.2} with hSdef
  have hsecret : ∀ a b, b ∈ constructionAddresses vp → .inl a ∈ childAdrs vp b →
      Tables.QueriesIn S (PRFScheme.functionQuery (pkSeed, a) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) :=
    fun a b hmem hab =>
      Tables.queriesIn_functionQuery ⟨rfl, skDom_of_secretChild hb hmem hab⟩
  unfold bRestW
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
    simp [sigSignOracle, appendLog, bSignW]
    refine Tables.queriesIn_bind (Tables.queriesIn_liftM S _) fun addrnd => ?_
    rw [map_eq_bind_pure_comp]
    refine Tables.queriesIn_bind ?_ fun sig => Tables.queriesIn_pure S _
    exact signInternalWithSecretRandomizerM_pred_of_ledger
      (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
      (fun {α} oa => Tables.QueriesIn S oa) (fun x => Tables.queriesIn_pure S x)
      (fun oa ob h1 h2 => Tables.queriesIn_bind h1 h2) prims.core hsecret m pkSeed root _
      (fun a _ xs => Tables.queriesIn_pure S _) (Tables.queriesIn_pure S _)

/-- The `PRF` distinguisher of the SUF-CMA proof on the secret-key address domain: `bPrfW w A`
behind the forwarding wrapper (whose `default` branch is never taken, `queriesIn_bRestW`). -/
noncomputable def bPrfWC (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y :=
  simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bPrfW w A)

/-- The wrapped distinguisher has, in the game on `SkAdrs vp`, exactly the advantage of `bPrfW`
in the old game. -/
theorem prfAdvantageC_bPrfWC (hb : CanonicalAddressBounds vp.params) (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    (skPrfC vp prims).prfAdvantage (bPrfWC w A) = (skPrf vp prims).prfAdvantage (bPrfW w A) := by
  unfold bPrfWC
  rw [bPrfW_eq_bRestW]
  exact prfAdvantageC_eq_of pkSeedDist (bRestW w A) (queriesIn_bRestW hb w A)

/-- `bPrfWC w A` makes at most `2^h'·len + qs·(k·2^a + d·2^h'·len)` function queries. -/
theorem bPrfWC_queryBound_exact (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfWC w A) (fun i => i.isRight = true)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  Restrict.queryBound_restrict _ (bPrfW_queryBound_exact w A qs hA)

#print axioms Reduction.prfAdvantageC_eq_of
#print axioms Reduction.prfAdvantageC_bPrfWC
#print axioms Reduction.bPrfWC_queryBound_exact

end Reduction
