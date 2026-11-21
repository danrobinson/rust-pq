import Reduction.Tables
import Reduction.OpenPRE
import Reduction.WotsEmbed
import HashSig.SLHDSA.Security.WeakKeyBound

/-!
# Sparse secret tables: only cells of the key structure are sampled

`sampleTable` draws `2 ^ 256` uniform values.  `sparseOn is` draws one uniform value for each
index of the explicit list `is` and is `default` elsewhere; no object of size `2 ^ 256` is
created.  The lists used are

* `wotsSkIdx vp` — the cells of the `len` start values of every WOTS+ instance of the hypertree;
* `forsSkIdx vp` (`Reduction.OpenPRE`) — the cells of the secret values of all FORS leaves;
* `structSecIdx vp = forsSkIdx vp ++ wotsSkIdx vp` — all secret cells of the key structure.

Results (interface used by `Reduction.Lazy.*Sparse`):

* `evalDist_sparseOn_bind` — `sparseOn is` is the uniform table restricted to `is`
  (`restrictTo`), in law, for every continuation;
* `evalDist_sparseOn_perm`, `evalDist_sparseOn_extract` — order irrelevance and splitting off a
  block of cells as fresh samples;
* `idealRoot_restrictTo`, `idealSign_restrictTo` — the honest objects of `G2` never read a cell
  outside the structure;
* `prTrue_g2Class_eq_sparse` — hence `G2 ∧ class = c` may be played with the sparse table.

The number of samples of `sparseOn is` is `is.length` (`sparseOn` is a map of
`Tables.sampleList _ is.length`); `structSecIdx_length` gives the closed form
`2^h·k·2^a + #WOTS instances·len`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Lazy

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## Cells of the key structure -/

/-- The table cells of all WOTS+ start values of the hypertree. -/
def wotsSkIdx (vp : ValidatedParams) : List SecIdx :=
  (wotsInsts vp).flatMap fun a => (List.finRange vp.params.len).map fun j => wotsCells vp a j

/-- All secret cells of the key structure: FORS leaf secrets, then WOTS+ start values. -/
def structSecIdx (vp : ValidatedParams) : List SecIdx :=
  forsSkIdx vp ++ wotsSkIdx vp

theorem mem_wotsSkIdx {i : SecIdx} : i ∈ wotsSkIdx vp ↔ IsWotsCell vp i := by
  simp only [wotsSkIdx, IsWotsCell, wotsCells, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and]

theorem wotsInsts_nodup (vp : ValidatedParams) : (wotsInsts vp).Nodup :=
  (allWotsInstances_nodup vp).map (wotsInstanceAdrs_injective vp)

theorem wotsSkIdx_nodup (hS : Structural vp prims) : (wotsSkIdx vp).Nodup := by
  unfold wotsSkIdx
  rw [List.nodup_flatMap]
  refine ⟨fun a ha => ?_, ?_⟩
  · refine (List.nodup_finRange _).map_on fun j _ j' _ h => ?_
    exact (wotsCell_inj hS a ha a ha j j' h).2
  · refine (wotsInsts_nodup vp).imp_of_mem fun {a b} ha hb hab => ?_
    intro i hi hi'
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
    obtain ⟨j', -, hj'⟩ := List.mem_map.1 hi'
    exact hab (wotsCell_inj hS a ha b hb j j' hj'.symm).1

/-- A FORS secret cell is not a WOTS+ cell. -/
theorem forsSkIdx_not_wotsCell (hS : Structural vp prims) {i : SecIdx} (hi : i ∈ forsSkIdx vp) :
    ¬ IsWotsCell vp i := by
  rintro ⟨a, ha, j, hj⟩
  obtain ⟨leaf, hleaf, rfl⟩ := List.mem_map.1 hi
  obtain ⟨p, rfl⟩ := z_mem_wotsInsts ha
  have e := op_secIdx_inj _ _ (addressFacts_wotsSkAdrs hS.bounds p j).canonical
    (op_skOf_canonical hS hleaf).1 hj
  have e' := congrArg Adrs.type e
  revert e'
  show AddrType.wotsPrf.toCode = AddrType.forsPrf.toCode → False
  decide

theorem structSecIdx_nodup (hS : Structural vp prims) : (structSecIdx vp).Nodup := by
  unfold structSecIdx
  refine List.Nodup.append (forsSkIdx_nodup hS) (wotsSkIdx_nodup hS) ?_
  intro i hi hi'
  exact forsSkIdx_not_wotsCell hS hi (mem_wotsSkIdx.1 hi')

theorem wotsSkIdx_length : (wotsSkIdx vp).length = (wotsInsts vp).length * vp.params.len := by
  simp [wotsSkIdx, List.length_flatMap]

theorem structSecIdx_length :
    (structSecIdx vp).length =
      (forsLeafAddresses vp).length + (wotsInsts vp).length * vp.params.len := by
  rw [structSecIdx, List.length_append, forsSkIdx_length, wotsSkIdx_length]

/-! ## The sparse sampler -/

/-- The sparse table on the index list `is`: `is.length` independent uniform values written at
the cells `is`, `default` everywhere else. -/
noncomputable def sparseOn (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] [Inhabited prims.Y] (is : List SecIdx) :
    ProbComp (SecretTable vp prims) :=
  (fun xs => Tables.updateList (fun _ => default) is xs) <$>
    Tables.sampleList prims.Y is.length

/-- The sparse table of the whole key structure. -/
noncomputable def sparseTable (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] [Inhabited prims.Y] : ProbComp (SecretTable vp prims) :=
  sparseOn vp prims (structSecIdx vp)

/-- Restriction of a table to the cells `is` (`default` elsewhere). -/
def restrictTo (is : List SecIdx) (tbl : SecretTable vp prims) : SecretTable vp prims :=
  fun i => if i ∈ is then tbl i else default

theorem restrictTo_apply_of_mem (tbl : SecretTable vp prims) {is : List SecIdx} {i : SecIdx}
    (h : i ∈ is) : restrictTo is tbl i = tbl i := by
  simp [restrictTo, h]

theorem restrictTo_apply_of_not_mem (tbl : SecretTable vp prims) {is : List SecIdx} {i : SecIdx}
    (h : i ∉ is) : restrictTo is tbl i = default := by
  simp [restrictTo, h]

/-- On a listed cell (or where the base tables agree) `updateList` does not depend on the base
table. -/
theorem updateList_congr_base {g g' : SecretTable vp prims} {i : SecIdx} :
    ∀ {is : List SecIdx} {xs : List prims.Y}, xs.length = is.length →
      (i ∉ is → g i = g' i) →
      Tables.updateList g is xs i = Tables.updateList g' is xs i
  | [], xs, _, h => by
      rw [Tables.updateList_nil_left, Tables.updateList_nil_left]
      exact h (by simp)
  | j :: is, [], hlen, _ => by simp at hlen
  | j :: is, x :: xs, hlen, h => by
      rw [Tables.updateList_cons, Tables.updateList_cons]
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hij, Function.update_of_ne hij]
        exact updateList_congr_base (by simpa using hlen)
          (fun hi => h fun hmem => by
            rcases List.mem_cons.1 hmem with h1 | h1
            · exact hij h1
            · exact hi h1)

/-- Restricting an overwritten table: the overwritten cells stay, the rest is restricted. -/
theorem restrictTo_append_updateList (T : SecretTable vp prims) (is js : List SecIdx)
    {xs : List prims.Y} (hlen : xs.length = is.length) :
    restrictTo (is ++ js) (Tables.updateList T is xs) =
      Tables.updateList (restrictTo js T) is xs := by
  funext i
  by_cases hi : i ∈ is
  · rw [restrictTo_apply_of_mem _ (List.mem_append_left _ hi)]
    exact updateList_congr_base hlen (fun h => absurd hi h)
  · rw [Tables.updateList_apply_of_not_mem _ _ _ hi]
    by_cases hj : i ∈ js
    · rw [restrictTo_apply_of_mem _ (List.mem_append_right _ hj), restrictTo_apply_of_mem _ hj,
        Tables.updateList_apply_of_not_mem _ _ _ hi]
    · rw [restrictTo_apply_of_not_mem _ (fun h => (List.mem_append.1 h).elim hi hj),
        restrictTo_apply_of_not_mem _ hj]

theorem restrictTo_updateList (T : SecretTable vp prims) (is : List SecIdx)
    {xs : List prims.Y} (hlen : xs.length = is.length) :
    restrictTo is (Tables.updateList T is xs) = Tables.updateList (fun _ => default) is xs := by
  have h := restrictTo_append_updateList T is [] hlen
  rw [List.append_nil] at h
  rw [h]
  funext i
  exact updateList_congr_base hlen (fun _ => restrictTo_apply_of_not_mem T (by simp))

theorem restrictTo_congr_mem (T : SecretTable vp prims) {is js : List SecIdx}
    (h : ∀ i, i ∈ is ↔ i ∈ js) : restrictTo is T = restrictTo js T := by
  funext i
  by_cases hi : i ∈ is
  · rw [restrictTo_apply_of_mem _ hi, restrictTo_apply_of_mem _ ((h i).1 hi)]
  · rw [restrictTo_apply_of_not_mem _ hi, restrictTo_apply_of_not_mem _ (fun hj => hi ((h i).2 hj))]

/-- **Sparse = restricted uniform.** -/
theorem evalDist_sparseOn_bind {α : Type} [MeasurableSpace α] {is : List SecIdx}
    (hnd : is.Nodup) (f : SecretTable vp prims → ProbComp α) :
    𝒟[sparseOn vp prims is >>= f] =
      𝒟[sampleTable vp prims >>= fun tbl => f (restrictTo is tbl)] := by
  have h1 : sparseOn vp prims is >>= f =
      Tables.sampleList prims.Y is.length >>= fun xs =>
        f (Tables.updateList (fun _ => default) is xs) := by
    unfold sparseOn
    rw [bind_map_left]
  rw [h1]
  refine Eq.trans ?_ (evalDist_sampleTable_extract_list hnd
    (fun _ tbl => f (restrictTo is tbl)))
  refine Eq.trans (OracleComp.evalDist_bind_const (sampleTable vp prims) _).symm ?_
  refine evalDist_bind_congr_of_support _ _ _ fun tbl _ => ?_
  refine evalDist_bind_congr_of_support _ _ _ fun xs hxs => ?_
  rw [restrictTo_updateList tbl is (Tables.length_of_mem_support_sampleList hxs)]

/-- The order of the index list is irrelevant. -/
theorem evalDist_sparseOn_perm {α : Type} [MeasurableSpace α] {is js : List SecIdx}
    (hnd : is.Nodup) (hp : is.Perm js) (f : SecretTable vp prims → ProbComp α) :
    𝒟[sparseOn vp prims is >>= f] = 𝒟[sparseOn vp prims js >>= f] := by
  rw [evalDist_sparseOn_bind hnd f, evalDist_sparseOn_bind (hp.nodup_iff.1 hnd) f]
  have e : (fun tbl : SecretTable vp prims => f (restrictTo is tbl)) =
      fun tbl => f (restrictTo js tbl) :=
    funext fun tbl => by rw [restrictTo_congr_mem tbl fun i => hp.mem_iff]
  rw [e]

/-- **Splitting off a block.**  A sparse table on `js` whose cells `is` are then overwritten by
fresh uniform samples is the sparse table on `is ++ js`. -/
theorem evalDist_sparseOn_extract {α : Type} [MeasurableSpace α] {is js : List SecIdx}
    (hnd : (is ++ js).Nodup) (f : SecretTable vp prims → ProbComp α) :
    𝒟[sparseOn vp prims js >>= fun tbl => Tables.sampleList prims.Y is.length >>= fun xs =>
        f (Tables.updateList tbl is xs)] =
      𝒟[sparseOn vp prims (is ++ js) >>= f] := by
  rw [evalDist_sparseOn_bind (List.Nodup.of_append_right hnd), evalDist_sparseOn_bind hnd f]
  refine Eq.trans ?_ (evalDist_sampleTable_extract_list (List.Nodup.of_append_left hnd)
    (fun _ tbl => f (restrictTo (is ++ js) tbl)))
  refine evalDist_bind_congr_of_support _ _ _ fun tbl _ => ?_
  refine evalDist_bind_congr_of_support _ _ _ fun xs hxs => ?_
  rw [restrictTo_append_updateList tbl is js (Tables.length_of_mem_support_sampleList hxs)]

/-! ## The honest objects read only structure cells -/

section Reads

/-- Public-hash queries inside a provider program are evaluated by `prims`. -/
@[reducible] private def prfQ (prims : Primitives vp.params) : HasQuery (publicHashSpec prims.core)
    (OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)) :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

/-- Public-hash queries in `ProbComp` are evaluated by `prims`. -/
@[reducible] private def probQ (prims : Primitives vp.params) :
    HasQuery (publicHashSpec prims.core) ProbComp :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

attribute [local instance] prfQ probQ

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

/-- The cell of every secret child of a ledger address is a structure cell. -/
theorem secIdx_secretChild_mem_structSecIdx {a b : Adrs} (hmem : b ∈ constructionAddresses vp)
    (h : .inl a ∈ childAdrs vp b) : secIdx a ∈ structSecIdx vp := by
  rcases List.mem_append.1 (mem_secretChildren_of_inl_mem_childAdrs hmem h) with h1 | h2
  · obtain ⟨⟨pos, j⟩, -, rfl⟩ := List.mem_map.1 h1
    refine List.mem_append_right _ (mem_wotsSkIdx.2 ⟨wotsInstanceAdrs pos, ?_, j, rfl⟩)
    exact List.mem_map.2 ⟨pos, mem_allWotsInstances vp pos, rfl⟩
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 h2
    exact List.mem_append_left _ (List.mem_map.2 ⟨b', hb', rfl⟩)

private theorem pure_inj_probComp {α : Type} {x y : α}
    (h : (pure x : ProbComp α) = pure y) : x = y := by
  have h' := congrArg support h
  rw [support_pure, support_pure] at h'
  exact Set.singleton_eq_singleton_iff.1 h'

/-- `PK.root` depends only on the structure cells of the table. -/
theorem idealRoot_congr_struct {tbl tbl' : SecretTable vp prims} (pkSeed : prims.PkSeed)
    (h : ∀ i ∈ structSecIdx vp, tbl i = tbl' i) :
    idealRoot vp prims tbl pkSeed = idealRoot vp prims tbl' pkSeed := by
  set S : Set (prims.PkSeed × Adrs) := {d | secIdx d.2 ∈ structSecIdx vp} with hSdef
  have hq : Tables.QueriesIn S
      (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) :=
    keygenInternalWithSecretM_pred_of_ledger
      (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
      (fun {α} oa => Tables.QueriesIn S oa) (fun x => Tables.queriesIn_pure S x)
      (fun oa ob h1 h2 => Tables.queriesIn_bind h1 h2) prims.core
      (fun a b hmem hab => Tables.queriesIn_functionQuery
        (secIdx_secretChild_mem_structSecIdx hmem hab)) pkSeed
      (fun a _ xs => Tables.queriesIn_pure S _)
  have e := Tables.simulateQ_fnImpl_congr hq
    (h₁ := fun d : prims.PkSeed × Adrs => secretOf vp prims tbl d.2)
    (h₂ := fun d : prims.PkSeed × Adrs => secretOf vp prims tbl' d.2) (fun d hd => h _ hd)
  rw [keygen_sim, keygen_sim] at e
  exact pure_inj_probComp e

/-- Signing depends only on the structure cells of the table. -/
theorem idealSign_congr_struct {tbl tbl' : SecretTable vp prims} (msg : List Byte)
    (pk : PublicKeyCore prims.core) (R : prims.Y)
    (h : ∀ i ∈ structSecIdx vp, tbl i = tbl' i) :
    idealSign vp prims tbl msg pk R = idealSign vp prims tbl' msg pk R := by
  set S : Set (prims.PkSeed × Adrs) := {d | secIdx d.2 ∈ structSecIdx vp} with hSdef
  have hq : Tables.QueriesIn S
      (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pk.pkSeed, a)) msg pk.pkSeed pk.pkRoot R :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
          (GeneralScheme.SignatureCore vp prims.core)) :=
    signInternalWithSecretRandomizerM_pred_of_ledger
      (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
      (fun {α} oa => Tables.QueriesIn S oa) (fun x => Tables.queriesIn_pure S x)
      (fun oa ob h1 h2 => Tables.queriesIn_bind h1 h2) prims.core
      (fun a b hmem hab => Tables.queriesIn_functionQuery
        (secIdx_secretChild_mem_structSecIdx hmem hab)) msg pk.pkSeed pk.pkRoot R
      (fun a _ xs => Tables.queriesIn_pure S _) (Tables.queriesIn_pure S _)
  have e := Tables.simulateQ_fnImpl_congr hq
    (h₁ := fun d : prims.PkSeed × Adrs => secretOf vp prims tbl d.2)
    (h₂ := fun d : prims.PkSeed × Adrs => secretOf vp prims tbl' d.2) (fun d hd => h _ hd)
  rw [sign_sim, sign_sim] at e
  exact pure_inj_probComp e

end Reads

/-- `PK.root` reads only WOTS+ cells. -/
theorem idealRoot_restrictTo (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) {is : List SecIdx} (his : ∀ i ∈ wotsSkIdx vp, i ∈ is) :
    idealRoot vp prims (restrictTo is tbl) pkSeed = idealRoot vp prims tbl pkSeed := by
  classical
  -- intermediate table: `tbl` on the FORS cells, `restrictTo is tbl` elsewhere
  let mid : SecretTable vp prims := fun i => if i ∈ forsSkIdx vp then tbl i else restrictTo is tbl i
  have h1 : idealRoot vp prims (restrictTo is tbl) pkSeed = idealRoot vp prims mid pkSeed := by
    refine op_idealRoot_congr hS.bounds _ _ pkSeed fun a hl ht hty => ?_
    have hn : secIdx a ∉ forsSkIdx vp := by
      intro hmem
      obtain ⟨leaf, hleaf, heq⟩ := List.mem_map.1 hmem
      have hc := op_skOf_canonical hS hleaf
      exact op_secIdx_ne a (skOf leaf) hl ht hty hc.2.1 hc.2.2 rfl heq.symm
    show restrictTo is tbl (secIdx a) = mid (secIdx a)
    show _ = if secIdx a ∈ forsSkIdx vp then _ else _
    simp only [hn, ↓reduceIte]
  rw [h1]
  refine idealRoot_congr_struct pkSeed fun i hi => ?_
  show (if i ∈ forsSkIdx vp then tbl i else restrictTo is tbl i) = tbl i
  by_cases hf : i ∈ forsSkIdx vp
  · simp only [hf, ↓reduceIte]
  · simp only [hf, ↓reduceIte]
    exact restrictTo_apply_of_mem tbl (his i ((List.mem_append.1 hi).resolve_left hf))

theorem idealPk_restrictTo (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) {is : List SecIdx} (his : ∀ i ∈ wotsSkIdx vp, i ∈ is) :
    idealPk vp prims (restrictTo is tbl) pkSeed = idealPk vp prims tbl pkSeed := by
  unfold idealPk
  rw [idealRoot_restrictTo hS tbl pkSeed his]

set_option linter.unusedVariables false in
/-- Signing reads only structure cells. -/
theorem idealSign_restrictTo (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (msg : List Byte) (pk : PublicKeyCore prims.core) (R : prims.Y) {is : List SecIdx}
    (his : ∀ i ∈ structSecIdx vp, i ∈ is) :
    idealSign vp prims (restrictTo is tbl) msg pk R = idealSign vp prims tbl msg pk R :=
  idealSign_congr_struct msg pk R fun i hi => restrictTo_apply_of_mem tbl (his i hi)

/-- `G2 ∧ class = c` for a fixed seed and table. -/
noncomputable def g2ClassAt (A : Forger vp prims optRand pkSeedDist) (c : ForgeryClass)
    (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) : ProbComp Bool :=
  g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
    pure (g2Valid (idealPk vp prims tbl pkSeed) z.2 z.1.1 z.1.2 &&
      decide (g2ClassOf tbl (idealPk vp prims tbl pkSeed) z.2 z.1.1 z.1.2 = c))

theorem g2Class_eq_g2ClassAt (A : Forger vp prims optRand pkSeedDist) (c : ForgeryClass) :
    g2Class A c = pkSeedDist >>= fun pkSeed => sampleTable vp prims >>= fun tbl =>
      g2ClassAt A c pkSeed tbl := rfl

theorem g2ClassAt_restrictTo (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (c : ForgeryClass) (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) :
    g2ClassAt A c pkSeed (restrictTo (structSecIdx vp) tbl) = g2ClassAt A c pkSeed tbl := by
  have hpk : idealPk vp prims (restrictTo (structSecIdx vp) tbl) pkSeed =
      idealPk vp prims tbl pkSeed :=
    idealPk_restrictTo hS tbl pkSeed fun i hi => List.mem_append_right _ hi
  have hsign : idealSign vp prims (restrictTo (structSecIdx vp) tbl) = idealSign vp prims tbl :=
    funext fun m => funext fun pk => funext fun R =>
      idealSign_restrictTo hS tbl m pk R fun i hi => hi
  unfold g2ClassAt g2Run g2ClassOf
  rw [hpk, hsign]

/-- **`G2 ∧ class = c` with the sparse table.** -/
theorem prTrue_g2Class_eq_sparse (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) (c : ForgeryClass) :
    prTrue (g2Class A c) = prTrue (pkSeedDist >>= fun pkSeed => sparseTable vp prims >>= fun tbl =>
      g2ClassAt A c pkSeed tbl) := by
  rw [g2Class_eq_g2ClassAt]
  refine prTrue_congr (evalDist_bind_congr_of_support _ _ _ fun pkSeed _ => ?_)
  refine Eq.trans ?_ (evalDist_sparseOn_bind (structSecIdx_nodup hS) (g2ClassAt A c pkSeed)).symm
  have e : (fun tbl : SecretTable vp prims =>
      g2ClassAt A c pkSeed (restrictTo (structSecIdx vp) tbl)) = g2ClassAt A c pkSeed :=
    funext fun tbl => g2ClassAt_restrictTo hS A c pkSeed tbl
  rw [e]

end Lazy
end Reduction

#print axioms Reduction.Lazy.prTrue_g2Class_eq_sparse
#print axioms Reduction.Lazy.evalDist_sparseOn_extract
#print axioms Reduction.Lazy.structSecIdx_nodup
