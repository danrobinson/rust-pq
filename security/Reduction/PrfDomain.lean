import Reduction.PRFHop

/-!
# The `PRF` game on the secret-key address domain of the parameter set

`Reduction.skPrf` states the PRF problem for `PRF(PK.seed, SK.seed, ADRS)` with `ADRS` ranging
over *all* of `Adrs` (six unbounded naturals).  A concrete bundle has to give `prims.PRF` some
value on addresses that FIPS 205 never forms; the SHA-2 bundle returns the all-zero node outside
the checked `ADRSc` domain (`checkedNodeOrZero`, `Sha2Address.ofAdrs`).  One function query at such
an address distinguishes `prims.PRF` from a random function, so `skPrf` is a *false* assumption at
SLH-DSA-SHA2-128s (`Reduction.PrfDomainNonVacuity`: `skPrf_broken_128s`).

This file restates the problem on the domain a cryptographer means.

**Choice of domain.**  `SkDom vp a` says: `a` is FIPS-canonical, its type is `WOTS_PRF` or
`FORS_PRF` (`Adrs.IsSecretKey`), its layer is a layer of this hypertree (`a.layer < d`) and its
tree index is below `2^((d-1)·h')` (the number of trees of the bottom layer).  These are exactly
the `AddressFacts` of the reachable addresses plus the address type.

Canonical-only is **not** enough: `Adrs.isCanonical` allows a four-byte layer and a twelve-byte
tree (the full 32-byte `ADRS`), whereas SHA-2 `ADRSc` has a one-byte layer and an eight-byte tree.
`⟨256,0,0,0,0,0⟩` *is* canonical, and the SHA-2 `PRF` is the zero node there
(`canonical_256`, `prf_256_eq_zero` in `Reduction.PrfDomainNonVacuity`).  The layer/tree bounds
are what put every element of the domain inside the checked `ADRSc` domain for every approved
parameter set (`sha2Domain_of_addressFacts`).  The predicate depends on the parameter set only
through `d` and `h'`; it is decidable, so the wrapper below is an explicit program.

The domain is a superset of the addresses the honest algorithms use (it does not bound the
key-pair / chain / tree-index words beyond their four-byte width), i.e. the assumption is "PRF on
all well-formed `WOTS_PRF`/`FORS_PRF` addresses of this hypertree", the HK22 assumption.

**Adversary.**  `bPrfC A = simulateQ (restrictImpl skRestrict) (bPrf A)`: the old distinguisher run
behind a forwarding wrapper that passes a function query `(pk, a)` on when `SkDom vp a` holds and
answers `default` otherwise (this branch is never taken: `queriesIn_bRestC`).

Main results: `prfRealC_bPrfC`, `prfIdealC_bPrfC`, `prfAdvantageC_eq`, `stepPRFC`,
`bPrfC_queryBound_exact`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

/-! ## A generic domain-restricting wrapper for PRF distinguishers -/

namespace Restrict

variable {D D' V α : Type} [Inhabited V]

/-- Forward uniform-sampling queries; forward a function query at `d` to the restricted oracle at
`d'` when `r d = some d'`, and answer `default` without querying when `r d = none`. -/
def restrictImpl (r : D → Option D') :
    QueryImpl (unifSpec + (D →ₒ V)) (OracleComp (unifSpec + (D' →ₒ V)))
  | .inl n => (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (unifSpec + (D' →ₒ V)) _)
  | .inr d =>
    match r d with
    | some d' => (PRFScheme.functionQuery d' : OracleComp (PRFScheme.PRFOracleSpec D' V) V)
    | none => pure default

theorem restrictImpl_inr_some (r : D → Option D') {d : D} {d' : D'} (hd : r d = some d') :
    restrictImpl (V := V) r (Sum.inr d) =
      (PRFScheme.functionQuery d' : OracleComp (PRFScheme.PRFOracleSpec D' V) V) := by
  simp only [restrictImpl, hd]

theorem restrictImpl_inr_none (r : D → Option D') {d : D} (hd : r d = none) :
    restrictImpl (V := V) r (Sum.inr d) = pure default := by
  simp only [restrictImpl, hd]

/-- The function on the large domain that the wrapper presents when the restricted oracle is `h`. -/
def pull (r : D → Option D') (h : D' → V) (d : D) : V :=
  match r d with
  | some d' => h d'
  | none => default

/-- Answering the wrapped program by `h` is answering the original program by `pull r h`. -/
theorem simulateQ_fnImpl_restrict (r : D → Option D') (h : D' → V)
    (oa : OracleComp (unifSpec + (D →ₒ V)) α) :
    simulateQ (Tables.fnImpl h) (simulateQ (restrictImpl r) oa) =
      simulateQ (Tables.fnImpl (pull r h)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with n | d
    · have e1 : restrictImpl (V := V) r (Sum.inl n) =
          (liftM (liftM (unifSpec.query n) : ProbComp _) :
            OracleComp (unifSpec + (D' →ₒ V)) _) := rfl
      rw [e1, Tables.simulateQ_fnImpl_liftM]
      exact bind_congr fun u => ih u
    · have e2 : Tables.fnImpl (pull r h) (Sum.inr d) = pure (pull r h d) := rfl
      rw [e2, pure_bind, ← ih]
      cases hd : r d with
      | none =>
        rw [restrictImpl_inr_none r hd, simulateQ_pure, pure_bind]
        simp only [pull, hd]
      | some d' =>
        rw [restrictImpl_inr_some r hd, Tables.simulateQ_fnImpl_functionQuery, pure_bind]
        simp only [pull, hd]

theorem simulateQ_restrict_liftM (r : D → Option D') (oa : ProbComp α) :
    simulateQ (restrictImpl (V := V) r) (liftM oa : OracleComp (unifSpec + (D →ₒ V)) α) =
      (liftM oa : OracleComp (unifSpec + (D' →ₒ V)) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    rw [liftM_bind, simulateQ_bind, liftM_bind]
    refine congrArg₂ _ ?_ (funext ih)
    exact simulateQ_spec_query _ _

theorem queriesIn_restrict (r : D → Option D') {S : Set D} {S' : Set D'}
    (hr : ∀ d ∈ S, ∀ d', r d = some d' → d' ∈ S')
    {oa : OracleComp (unifSpec + (D →ₒ V)) α} (hoa : Tables.QueriesIn S oa) :
    Tables.QueriesIn S' (simulateQ (restrictImpl r) oa) := by
  refine AllQueriesSatisfy.simulateQ hoa fun t ht => ?_
  rcases t with n | d
  · exact Tables.queriesIn_liftM S' _
  · cases hd : r d with
    | none =>
      rw [restrictImpl_inr_none r hd]
      exact Tables.queriesIn_pure S' _
    | some d' =>
      rw [restrictImpl_inr_some r hd]
      exact Tables.queriesIn_functionQuery (hr d ht d' hd)

/-- The wrapper makes at most one function query per function query. -/
theorem queryBound_restrict (r : D → Option D') {oa : OracleComp (unifSpec + (D →ₒ V)) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun i => i.isRight = true) n) :
    IsQueryBoundP (simulateQ (restrictImpl (V := V) r) oa) (fun i => i.isRight = true) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | d
    · simp at ht
    · cases hd : r d with
      | none =>
        rw [restrictImpl_inr_none r hd]
        exact isQueryBoundP_pure _ _ _
      | some d' =>
        rw [restrictImpl_inr_some r hd]
        simp [PRFScheme.functionQuery]
  · rcases t with n | d
    · exact (isQueryBoundP_liftM_isRight (hs := D' →ₒ V) _)
    · simp at ht

end Restrict

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The domain and the problem -/

/-- The secret-key address domain of the parameter set: FIPS-canonical, type `WOTS_PRF` or
`FORS_PRF`, at a layer of this hypertree, in a tree that exists at the bottom layer. -/
def SkDom (vp : ValidatedParams) (a : Adrs) : Prop :=
  a.isCanonical = true ∧ a.IsSecretKey ∧ a.layer < vp.params.d ∧
    a.tree < 2 ^ ((vp.params.d - 1) * vp.params.hp)

instance (vp : ValidatedParams) (a : Adrs) : Decidable (SkDom vp a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem SkDom.addressFacts {a : Adrs} (h : SkDom vp a) : AddressFacts vp a :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- Secret-key addresses of the parameter set. -/
abbrev SkAdrs (vp : ValidatedParams) : Type := {a : Adrs // SkDom vp a}

/-- `PRF(PK.seed, SK.seed, ADRS)` keyed by `SK.seed`, on inputs `(PK.seed, ADRS)` with `ADRS` a
secret-key address of the parameter set. -/
def skPrfC (vp : ValidatedParams) (prims : Primitives vp.params) [SampleableType prims.SkSeed] :
    PRFScheme prims.SkSeed (prims.PkSeed × SkAdrs vp) prims.Y where
  keygen := $ᵗ prims.SkSeed
  eval := fun k d => prims.PRF d.1 k d.2.val

/-- The partial map from old to new PRF inputs. -/
def skRestrict (vp : ValidatedParams) (prims : Primitives vp.params) (d : prims.PkSeed × Adrs) :
    Option (prims.PkSeed × SkAdrs vp) :=
  if h : SkDom vp d.2 then some (d.1, ⟨d.2, h⟩) else none

theorem skRestrict_of_dom {d : prims.PkSeed × Adrs} (h : SkDom vp d.2) :
    skRestrict vp prims d = some (d.1, ⟨d.2, h⟩) := by
  simp only [skRestrict, h, ↓reduceDIte]

/-- The `PRF` distinguisher on the secret-key address domain: `bPrf A` behind the forwarding
wrapper. -/
noncomputable def bPrfC (A : Forger vp prims optRand pkSeedDist) :
    PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y :=
  simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bPrf A)

/-! ## `bPrf` only queries the domain -/

@[reducible] private def prfQ' (prims : Primitives vp.params) : HasQuery (publicHashSpec prims.core)
    (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

attribute [local instance] prfQ'

/-- The signing procedure `bPrf` hands to the harness (copy of the private `bSign`). -/
noncomputable def bSignC (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
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

/-- Everything `bPrf A` does after sampling `PK.seed` (copy of the private `bRest`). -/
noncomputable def bRestC (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool := do
  let skPrf ← (monadLift ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.SkPrf)
  let root ← (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
    (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y)
  let z ← runForger A ⟨pkSeed, root⟩ (bSignC optRand ⟨pkSeed, root⟩ skPrf)
  return harnessValid ⟨pkSeed, root⟩ z.2 z.1.1 z.1.2

theorem bPrf_eq_bRestC (A : Forger vp prims optRand pkSeedDist) :
    bPrf A = (liftM pkSeedDist :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.PkSeed) >>=
        bRestC A := rfl

/-- Every secret child of a ledger address is in the secret-key address domain. -/
theorem skDom_of_secretChild (hb : CanonicalAddressBounds vp.params) {a b : Adrs}
    (hmem : b ∈ constructionAddresses vp) (h : .inl a ∈ childAdrs vp b) : SkDom vp a := by
  rcases List.mem_append.1 (mem_secretChildren_of_inl_mem_childAdrs hmem h) with h1 | h2
  · obtain ⟨⟨pos, i⟩, -, rfl⟩ := List.mem_map.1 h1
    have hf := addressFacts_wotsSkAdrs hb pos i
    exact ⟨hf.canonical, Adrs.isSecretKey_wotsSkAdrs _ _, hf.layer_lt, hf.tree_lt⟩
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 h2
    have hf := addressFacts_forsLeafAddresses vp hb b' hb'
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := Adrs.fits_of_isCanonical b' hf.canonical
    refine ⟨?_, Adrs.isSecretKey_forsSkAdrs _ _, hf.layer_lt, hf.tree_lt⟩
    simp [Adrs.isCanonical, forsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setTreeIndex, Adrs.getKeyPairAddress, f1, f2, f4, f6]
    exact ⟨by decide, by decide⟩

/-- The function queries of `bRestC A pkSeed` are at `PK.seed = pkSeed` and addresses of the
secret-key domain. -/
theorem queriesIn_bRestC (hb : CanonicalAddressBounds vp.params)
    (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed) :
    Tables.QueriesIn {d : prims.PkSeed × Adrs | d.1 = pkSeed ∧ SkDom vp d.2}
      (bRestC A pkSeed) := by
  set S : Set (prims.PkSeed × Adrs) := {d | d.1 = pkSeed ∧ SkDom vp d.2} with hSdef
  have hsecret : ∀ a b, b ∈ constructionAddresses vp → .inl a ∈ childAdrs vp b →
      Tables.QueriesIn S (PRFScheme.functionQuery (pkSeed, a) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) :=
    fun a b hmem hab =>
      Tables.queriesIn_functionQuery ⟨rfl, skDom_of_secretChild hb hmem hab⟩
  unfold bRestC
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
    simp [harnessSignOracle, bSignC]
    refine Tables.queriesIn_bind (Tables.queriesIn_liftM S _) fun addrnd => ?_
    rw [map_eq_bind_pure_comp]
    refine Tables.queriesIn_bind ?_ fun sig => Tables.queriesIn_pure S _
    exact signInternalWithSecretRandomizerM_pred_of_ledger
      (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
      (fun {α} oa => Tables.QueriesIn S oa) (fun x => Tables.queriesIn_pure S x)
      (fun oa ob h1 h2 => Tables.queriesIn_bind h1 h2) prims.core hsecret m pkSeed root _
      (fun a _ xs => Tables.queriesIn_pure S _) (Tables.queriesIn_pure S _)

/-- `bPrfC A` as a prefix followed by the wrapped rest. -/
theorem bPrfC_eq (A : Forger vp prims optRand pkSeedDist) :
    bPrfC A = (liftM pkSeedDist :
      OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) prims.PkSeed) >>=
        fun s => simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bRestC A s) := by
  unfold bPrfC
  rw [bPrf_eq_bRestC, simulateQ_bind, Restrict.simulateQ_restrict_liftM]

/-- Behind the wrapper, answering by `h` on the domain is answering `bRestC` by any `h'` that
agrees with `h` on the domain. -/
theorem simulateQ_fnImpl_wrapped (hb : CanonicalAddressBounds vp.params)
    (A : Forger vp prims optRand pkSeedDist) (s : prims.PkSeed)
    (h : prims.PkSeed × SkAdrs vp → prims.Y) (h' : prims.PkSeed × Adrs → prims.Y)
    (hh : ∀ (pk : prims.PkSeed) (a : SkAdrs vp), h (pk, a) = h' (pk, a.val)) :
    simulateQ (Tables.fnImpl h)
        (simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bRestC A s)) =
      simulateQ (Tables.fnImpl h') (bRestC A s) := by
  rw [Restrict.simulateQ_fnImpl_restrict]
  refine Tables.simulateQ_fnImpl_congr (queriesIn_bRestC hb A s) fun d hd => ?_
  unfold Restrict.pull
  rw [skRestrict_of_dom hd.2]
  exact hh d.1 ⟨d.2, hd.2⟩

/-! ## Real and ideal worlds -/

/-- The real experiments of the new and the old game are the same program. -/
theorem prfRealExperimentC_eq (hb : CanonicalAddressBounds vp.params)
    (A : Forger vp prims optRand pkSeedDist) :
    (skPrfC vp prims).prfRealExperiment (bPrfC A) = (skPrf vp prims).prfRealExperiment (bPrf A) := by
  unfold PRFScheme.prfRealExperiment
  refine bind_congr fun k => ?_
  change simulateQ (Tables.fnImpl fun d : prims.PkSeed × SkAdrs vp => prims.PRF d.1 k d.2.val) _ =
    simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => prims.PRF d.1 k d.2) _
  rw [bPrfC_eq, bPrf_eq_bRestC, simulateQ_bind, simulateQ_bind, Tables.simulateQ_fnImpl_liftM,
    Tables.simulateQ_fnImpl_liftM]
  exact bind_congr fun s => simulateQ_fnImpl_wrapped hb A s _ _ fun _ _ => rfl

/-- Real world of the new PRF game at `bPrfC A` is `G0`. -/
theorem prfRealC_bPrfC (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    𝒟[(skPrfC vp prims).prfRealExperiment (bPrfC A)] {true} = prTrue (g0 A) := by
  rw [prfRealExperimentC_eq hS.bounds, prfReal_bPrf]

/-- The ideal experiments of the new and the old game have the same output distribution. -/
theorem evalDist_prfIdealExperimentC_eq (hb : CanonicalAddressBounds vp.params)
    (A : Forger vp prims optRand pkSeedDist) :
    𝒟[PRFScheme.prfIdealExperiment (bPrfC A)] = 𝒟[PRFScheme.prfIdealExperiment (bPrf A)] := by
  have hold : 𝒟[PRFScheme.prfIdealExperiment (bPrf A)] =
      𝒟[pkSeedDist >>= fun s => sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => secretOf vp prims tbl d.2)
          (bRestC A s)] :=
    evalDist_prfIdeal_eq_sampleTable (vp := vp) (prims := prims)
      secIdx_injOn_canonical pkSeedDist id (bRestC A)
      (fun s _ => (queriesIn_bRestC hb A s).mono fun t => by
        rcases t with n | d
        · exact fun h => h
        · exact fun h => ⟨h.1, h.2.1⟩)
  have hnew : 𝒟[PRFScheme.prfIdealExperiment (bPrfC A)] =
      𝒟[pkSeedDist >>= fun s => sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun d : prims.PkSeed × SkAdrs vp => tbl (secIdx d.2.val))
          (simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bRestC A s))] := by
    unfold PRFScheme.prfIdealExperiment
    rw [bPrfC_eq]
    exact Tables.evalDist_prfIdealExperiment_liftM_bind pkSeedDist
      (fun s => simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bRestC A s))
      (fun _ d => secIdx d.2.val) (fun s => {d : prims.PkSeed × SkAdrs vp | d.1 = s})
      (fun s _ d hd d' hd' h => Prod.ext (hd.trans hd'.symm)
        (Subtype.ext (secIdx_injOn_canonical d.2.2.1 d'.2.2.1 h)))
      (fun s _ => Restrict.queriesIn_restrict _ (S := {d | d.1 = s ∧ SkDom vp d.2})
        (fun d hd d' hd' => by
          rw [skRestrict_of_dom hd.2] at hd'
          cases hd'
          exact hd.1) (queriesIn_bRestC hb A s))
  rw [hold, hnew]
  refine congrArg _ (bind_congr fun s => bind_congr fun tbl => ?_)
  exact simulateQ_fnImpl_wrapped hb A s _ _ fun _ _ => rfl

/-- Ideal world of the new PRF game at `bPrfC A` is `G1`. -/
theorem prfIdealC_bPrfC (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    𝒟[PRFScheme.prfIdealExperiment (bPrfC A)] {true} = prTrue (g1 A) := by
  rw [evalDist_prfIdealExperimentC_eq hS.bounds, prfIdeal_bPrf hS]

/-- The wrapped distinguisher has, against the restricted problem, exactly the advantage of the
original one against the unrestricted problem. -/
theorem prfAdvantageC_eq (hb : CanonicalAddressBounds vp.params)
    (A : Forger vp prims optRand pkSeedDist) :
    (skPrfC vp prims).prfAdvantage (bPrfC A) = (skPrf vp prims).prfAdvantage (bPrf A) := by
  unfold PRFScheme.prfAdvantage
  rw [prfRealExperimentC_eq hb, evalDist_prfIdealExperimentC_eq hb]

/-- **Step 1 on the secret-key address domain.** -/
theorem stepPRFC (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g0 A) ≤ prTrue (g1 A) + (skPrfC vp prims).prfAdvantage (bPrfC A) := by
  rw [prfAdvantageC_eq hS.bounds]
  exact stepPRF hS A

/-- Resource lemma: `bPrfC A` makes at most `2^h'·len + qs·(k·2^a + d·2^h'·len)` function
queries when `A` makes at most `qs` signing queries. -/
theorem bPrfC_queryBound_exact (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfC A) (fun i => i.isRight = true)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  Restrict.queryBound_restrict _ (bPrf_queryBound_exact A qs hA)

/-- Every function query of `bPrfC A` is at the `PK.seed` it sampled (and, by typing, at an
address of the domain); the wrapper's `default` branch is never taken on `bRestC`. -/
theorem queriesIn_bPrfC_rest (hb : CanonicalAddressBounds vp.params)
    (A : Forger vp prims optRand pkSeedDist) (s : prims.PkSeed) :
    Tables.QueriesIn {d : prims.PkSeed × SkAdrs vp | d.1 = s}
      (simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bRestC A s)) :=
  Restrict.queriesIn_restrict _ (S := {d | d.1 = s ∧ SkDom vp d.2})
    (fun d hd d' hd' => by
      rw [skRestrict_of_dom hd.2] at hd'
      cases hd'
      exact hd.1) (queriesIn_bRestC hb A s)

#print axioms Reduction.prfRealC_bPrfC
#print axioms Reduction.prfIdealC_bPrfC
#print axioms Reduction.prfAdvantageC_eq
#print axioms Reduction.stepPRFC
#print axioms Reduction.bPrfC_queryBound_exact

end Reduction
