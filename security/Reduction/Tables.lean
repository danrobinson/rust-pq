import Reduction.Harness

/-!
# P0: probability tools for uniform tables

Generic facts about a uniformly sampled table `I → R` (`uniformTable`, of which
`Reduction.sampleTable` is an instance) in VCVio's `ProbComp`.  The sampler is supplied by the
class `UniformSampler`, whose only instance (`Fin n`, cell by cell with `Fin.mOfFn`) is
choice-free; the lemmas use only that the sampler denotes the uniform measure:

* **resampling** (`evalDist_resample_*`): overwriting coordinates of a uniform table by fresh
  uniform values (one cell, a duplicate-free list of cells, a block of cells written from a
  uniform `Vector`) does not change the law of any continuation; in the *extraction* form the
  continuation additionally receives the fresh values, which are the values the table holds;
* **lazy = eager** (`evalDist_romImpl_run'_eq_*`): a lazily sampled random function on an
  arbitrary (possibly infinite) domain `D`, queried only inside a set `S` on which an index map
  `D → I` is injective, is a uniform table read through that map.  Block form: a lazy random
  function with range `Vector R n` is `n` cells of the table per query;
* small `prTrue` congruence / monotonicity / union-bound lemmas.

No measure-theoretic hypothesis appears in any statement: samplers are the concrete `$ᵗ R` and
`uniformTable I R`, and the output type of the continuation carries an arbitrary
`MeasurableSpace`.  `status/P0.md` says which lemma each consumer (`prfIdeal_bPrf`,
`stepOpenPRE`, `stepWotsEmbed`) applies.
-/

open OracleComp OracleSpec MeasureTheory ProbabilityTheory ENNReal

namespace Reduction
namespace Tables

/-! ## Uniform tables -/

section Uniform

/-- A choice-free sampler of uniform tables `I → R`, together with the proof that it denotes the
uniform measure.  The only instance is `Fin n`, sampled cell by cell in increasing index order
with `Fin.mOfFn` (`Fintype.equivFin` is not used).  Choice-free does not mean feasible: at
`n = 2^256` (`sampleTable`) the sampler draws `2^256` values. -/
class UniformSampler (I R : Type) [SampleableType R] where
  /-- The sampler. -/
  sample : ProbComp (I → R)
  /-- It is uniform. -/
  evalDist_sample : ∀ [MeasurableSpace R] [MeasurableSingletonClass R],
    𝒟[sample] = uniformOn Set.univ

noncomputable instance instUniformSamplerFin (n : ℕ) (R : Type) [SampleableType R] :
    UniformSampler (Fin n) R where
  sample := Fin.mOfFn n fun _ => ($ᵗ R : ProbComp R)
  evalDist_sample := evalDist_mOfFn_const_uniform n _ SampleableType.evalDist_uniformSample

variable {I R : Type} [Fintype I] [SampleableType R] [UniformSampler I R]

/-- A uniformly random table: independent uniform values at every index. -/
noncomputable def uniformTable (I R : Type) [SampleableType R] [UniformSampler I R] :
    ProbComp (I → R) :=
  UniformSampler.sample

/-- `uniformTable` denotes the uniform measure on the function space. -/
theorem evalDist_uniformTable [MeasurableSpace R] [MeasurableSingletonClass R] :
    𝒟[uniformTable I R] = uniformOn Set.univ :=
  UniformSampler.evalDist_sample

/-- On a finite type, a measurable structure with measurable singletons is the discrete one. -/
theorem measurableSpace_eq_top {T : Type} [Finite T] (m : MeasurableSpace T)
    [MeasurableSingletonClass T] : m = ⊤ :=
  le_antisymm le_top fun s _ => (Set.toFinite s).measurableSet

/-- `uniformTable` is uniform for every measurable structure with measurable singletons (the
form in which `SampleableType` states uniformity). -/
theorem evalDist_uniformTable' [MeasurableSpace (I → R)] [MeasurableSingletonClass (I → R)] :
    𝒟[uniformTable I R] = uniformOn Set.univ := by
  have h1 := measurableSpace_eq_top (T := I → R) inferInstance
  subst h1
  let mR : MeasurableSpace R := ⊤
  have h := evalDist_uniformTable (I := I) (R := R)
  have h2 := measurableSpace_eq_top (T := I → R) MeasurableSpace.pi
  rw [h2] at h
  exact h

end Uniform

/-! ## Abstract resampling through a lens

A *cell* of a table type `T` with content type `V` is a pair `read : T → V`, `write : T → V → T`
obeying the lens laws.  Swapping a fresh uniform content with the content of the cell is an
involution of `V × T`, hence preserves the uniform measure. -/

section Lens

variable {T V α : Type} [MeasurableSpace α]

/-- **Bijective re-randomisation of a uniform pair.**  For independent uniform draws `u`, `g`
and a bijection `σ` of the pair space, `(u, g)` may be replaced by `σ (u, g)`. -/
theorem evalDist_uniform_pair_bijective [Finite T] [Nonempty T] [Finite V] [Nonempty V]
    (value : ProbComp V) (table : ProbComp T)
    (hvalue : ∀ [MeasurableSpace V] [MeasurableSingletonClass V], 𝒟[value] = uniformOn Set.univ)
    (htable : ∀ [MeasurableSpace T] [MeasurableSingletonClass T], 𝒟[table] = uniformOn Set.univ)
    (σ : V × T → V × T) (hσ : Function.Bijective σ) (f : V × T → ProbComp α) :
    𝒟[value >>= fun u => table >>= fun g => f (σ (u, g))] =
      𝒟[value >>= fun u => table >>= fun g => f (u, g)] := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSpace T := ⊤
  set pair : ProbComp (V × T) := Prod.mk <$> value <*> table with hpair
  have hunif : 𝒟[pair] = uniformOn Set.univ :=
    evalDist_seq_map_eq_uniformOn _ _ Prod.mk hvalue htable
      Measurable.of_discrete ⟨fun x y h => h, fun x => ⟨x, rfl⟩⟩
  have h1 : ∀ F : V × T → ProbComp α,
      (value >>= fun u => table >>= fun g => F (u, g)) = pair >>= F := fun F => by
    simp [hpair, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  rw [h1 fun p => f (σ p), h1 f]
  exact evalDist_bind_bijective_of_uniform pair hunif σ hσ f

/-- **Lens resampling, extraction form.**  For a uniform `table : ProbComp T` and a lawful lens
`(read, write)` with sampleable content type: reading the cell of a uniform table is the same as
writing a fresh uniform value to it and returning that value. -/
theorem evalDist_lens_extract [Finite T] [Nonempty T] [SampleableType V] (table : ProbComp T)
    (htable : ∀ [MeasurableSpace T] [MeasurableSingletonClass T], 𝒟[table] = uniformOn Set.univ)
    (read : T → V) (write : T → V → T)
    (hrw : ∀ g u, read (write g u) = u) (hww : ∀ g u u', write (write g u) u' = write g u')
    (hwr : ∀ g, write g (read g) = g) (f : V → T → ProbComp α) :
    𝒟[$ᵗ V >>= fun u => table >>= fun g => f u (write g u)] =
      𝒟[table >>= fun g => f (read g) g] := by
  set σ : V × T → V × T := fun p => (read p.2, write p.2 p.1) with hσ
  have hσinv : Function.Involutive σ := fun p => by
    simp only [hσ, hrw, hww, hwr]
  have key := evalDist_uniform_pair_bijective ($ᵗ V) table
    SampleableType.evalDist_uniformSample htable σ hσinv.bijective
    (fun q : V × T => f (read q.2) q.2)
  simp only [hσ, hrw] at key
  rw [key]
  exact OracleComp.evalDist_bind_const _ _

/-- **Lens resampling.**  Writing a fresh uniform value into a cell of a uniform table leaves the
law of every continuation unchanged. -/
theorem evalDist_lens_resample [Finite T] [Nonempty T] [SampleableType V] (table : ProbComp T)
    (htable : ∀ [MeasurableSpace T] [MeasurableSingletonClass T], 𝒟[table] = uniformOn Set.univ)
    (read : T → V) (write : T → V → T)
    (hrw : ∀ g u, read (write g u) = u) (hww : ∀ g u u', write (write g u) u' = write g u')
    (hwr : ∀ g, write g (read g) = g) (f : T → ProbComp α) :
    𝒟[$ᵗ V >>= fun u => table >>= fun g => f (write g u)] = 𝒟[table >>= f] :=
  evalDist_lens_extract table htable read write hrw hww hwr fun _ g => f g

end Lens

/-! ## Lazy random function = table read through a lens family -/

section Lazy

variable {D V T α : Type}

/-- The handler answering uniform-sampling queries by sampling and function queries by the fixed
function `h`.  Definitionally `PRFScheme.prfRealQueryImpl ⟨_, fun _ => h⟩ ()`. -/
def fnImpl (h : D → V) : QueryImpl (unifSpec + (D →ₒ V)) ProbComp :=
  unifSpec.passthrough + (fun d => pure (h d) : QueryImpl (D →ₒ V) ProbComp)

/-- Every function query of `oa` is at a point of `S` (uniform-sampling queries are free). -/
abbrev QueriesIn (S : Set D) (oa : OracleComp (unifSpec + (D →ₒ V)) α) : Prop :=
  oa.AllQueriesSatisfy (Sum.elim (fun _ => True) (· ∈ S))

/-- Two answer functions that agree on `S` are indistinguishable to a computation that queries
only inside `S`. -/
theorem simulateQ_fnImpl_congr {S : Set D} {oa : OracleComp (unifSpec + (D →ₒ V)) α}
    (hoa : QueriesIn S oa) {h₁ h₂ : D → V} (h : ∀ d ∈ S, h₁ d = h₂ d) :
    simulateQ (fnImpl h₁) oa = simulateQ (fnImpl h₂) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [QueriesIn, allQueriesSatisfy_query_bind_iff] at hoa
    rcases t with n | d
    · simp only [simulateQ_bind, simulateQ_spec_query]
      exact congrArg _ (funext fun u => ih u (hoa.2 u))
    · have hd : h₁ d = h₂ d := h d hoa.1
      simp only [simulateQ_bind, simulateQ_spec_query]
      have e1 : fnImpl h₁ (Sum.inr d) = pure (h₁ d) := rfl
      have e2 : fnImpl h₂ (Sum.inr d) = pure (h₂ d) := rfl
      rw [e1, e2, pure_bind, pure_bind, hd]
      exact ih _ (hoa.2 _)

/-- A lifted `ProbComp` makes no function query. -/
theorem queriesIn_liftM (S : Set D) (oa : ProbComp α) :
    QueriesIn S (liftM oa : OracleComp (unifSpec + (D →ₒ V)) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind n k ih =>
    rw [liftM_bind]
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 trivial) ih

/-- A function query at a point of `S`. -/
theorem queriesIn_query {S : Set D} {d : D} (hd : d ∈ S) :
    QueriesIn S (liftM ((unifSpec + (D →ₒ V)).query (Sum.inr d)) :
      OracleComp (unifSpec + (D →ₒ V)) V) :=
  (allQueriesSatisfy_query_iff _ _).2 hd

/-- `PRFScheme.functionQuery` at a point of `S`. -/
theorem queriesIn_functionQuery {S : Set D} {d : D} (hd : d ∈ S) :
    QueriesIn S (PRFScheme.functionQuery d : OracleComp (PRFScheme.PRFOracleSpec D V) V) :=
  queriesIn_query hd

theorem queriesIn_pure (S : Set D) (a : α) :
    QueriesIn S (pure a : OracleComp (unifSpec + (D →ₒ V)) α) :=
  allQueriesSatisfy_pure _ _

theorem queriesIn_bind {β : Type} {S : Set D} {oa : OracleComp (unifSpec + (D →ₒ V)) α}
    {ob : α → OracleComp (unifSpec + (D →ₒ V)) β} (h₁ : QueriesIn S oa)
    (h₂ : ∀ x, QueriesIn S (ob x)) : QueriesIn S (oa >>= ob) :=
  allQueriesSatisfy_bind h₁ h₂

/-- `fnImpl` is transparent on a lifted `ProbComp`. -/
@[simp] theorem simulateQ_fnImpl_liftM (h : D → V) (oa : ProbComp α) :
    simulateQ (fnImpl h) (liftM oa : OracleComp (unifSpec + (D →ₒ V)) α) = oa := by
  simp [fnImpl, QueryImpl.simulateQ_add_liftM_left]

/-- `fnImpl` answers a function query by the function. -/
@[simp] theorem simulateQ_fnImpl_query (h : D → V) (d : D) :
    simulateQ (fnImpl h) (liftM ((unifSpec + (D →ₒ V)).query (Sum.inr d)) :
      OracleComp (unifSpec + (D →ₒ V)) V) = pure (h d) := by
  rw [simulateQ_spec_query]
  rfl

@[simp] theorem simulateQ_fnImpl_functionQuery (h : D → V) (d : D) :
    simulateQ (fnImpl h) (PRFScheme.functionQuery d :
      OracleComp (PRFScheme.PRFOracleSpec D V) V) = pure (h d) :=
  simulateQ_fnImpl_query h d

variable [DecidableEq D] [SampleableType V] [MeasurableSpace α]

/-- **Lazy = eager, abstract form.**  `table : ProbComp T` is any sampler of "tables", read at a
point `d` by `read · d` and overwritten there by `write · d`.  If, on `S`, writing then reading
returns the written value, writing at `d` does not disturb the other points of `S`, and writing a
fresh uniform value does not change the law of the table, then a lazy random function queried
only inside `S`, started from the cache `c`, is `read` of a sampled table overlaid by `c`. -/
theorem evalDist_romImpl_run'_eq_of_lens (table : ProbComp T) (read : T → D → V)
    (write : T → D → V → T) (S : Set D)
    (hrw : ∀ g d u, d ∈ S → read (write g d u) d = u)
    (hframe : ∀ g d u d', d ∈ S → d' ∈ S → d' ≠ d → read (write g d u) d' = read g d')
    (hres : ∀ d ∈ S, ∀ f : T → ProbComp α,
      𝒟[$ᵗ V >>= fun u => table >>= fun g => f (write g d u)] = 𝒟[table >>= f])
    (oa : OracleComp (unifSpec + (D →ₒ V)) α) (hoa : QueriesIn S oa)
    (c : (D →ₒ V).QueryCache) :
    𝒟[(simulateQ (D →ₒ V).romImpl oa).run' c] =
      𝒟[table >>= fun g => simulateQ (fnImpl fun d => (c d).getD (read g d)) oa] := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      rw [OracleComp.evalDist_bind_const]
  | query_bind t k ih =>
      rw [QueriesIn, allQueriesSatisfy_query_bind_iff] at hoa
      rcases t with n | d
      · have hred :
            (simulateQ (D →ₒ V).romImpl
              (liftM ((unifSpec + (D →ₒ V)).query (.inl n)) >>= k)).run' c =
            (unifSpec.query n : ProbComp _) >>= fun u =>
              (simulateQ (D →ₒ V).romImpl (k u)).run' c := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
            roSim.run_apply_inl]
          simp [StateT.run'_eq]
        have heval : ∀ h : D → V,
            simulateQ (fnImpl h) (liftM ((unifSpec + (D →ₒ V)).query (.inl n)) >>= k) =
              (unifSpec.query n : ProbComp _) >>= fun u => simulateQ (fnImpl h) (k u) :=
          fun h => by simp [fnImpl]
        rw [hred]
        simp_rw [heval]
        exact (evalDist_bind_congr_of_support _ _ _ fun u _ => ih u (hoa.2 u) c).trans
          (OracleComp.evalDist_bind_bind_swap _ _ _)
      · have hdS : d ∈ S := hoa.1
        have hred :
            (simulateQ (D →ₒ V).romImpl
              (liftM ((unifSpec + (D →ₒ V)).query (.inr d)) >>= k)).run' c =
            ((D →ₒ V).randomOracle d).run c >>= fun p =>
              (simulateQ (D →ₒ V).romImpl (k p.1)).run' p.2 := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
          rfl
        have heval : ∀ h : D → V,
            simulateQ (fnImpl h) (liftM ((unifSpec + (D →ₒ V)).query (.inr d)) >>= k) =
              simulateQ (fnImpl h) (k (h d)) := fun h => by
          rw [simulateQ_bind, simulateQ_spec_query]
          exact pure_bind _ _
        rw [hred]
        simp_rw [heval]
        rcases hc : c d with _ | u
        · rw [QueryImpl.withCaching_run_none _ hc, map_eq_bind_pure_comp]
          simp only [Function.comp, bind_assoc, pure_bind]
          set ψ : T → ProbComp α := fun g =>
            simulateQ (fnImpl fun d' => (c d').getD (read g d')) (k (read g d)) with hψ
          have hfun : ∀ u : V, (fun g : T =>
                simulateQ (fnImpl fun d' => ((c.cacheQuery d u) d').getD (read g d')) (k u)) =
              fun g => ψ (write g d u) := by
            intro u
            funext g
            simp only [hψ, hrw g d u hdS]
            refine simulateQ_fnImpl_congr (hoa.2 u) fun d' hd' => ?_
            by_cases hdd : d' = d
            · subst hdd
              simp [hc, hrw g d' u hdS]
            · rw [QueryCache.cacheQuery_of_ne _ _ hdd, hframe g d u d' hdS hd' hdd]
          refine (evalDist_bind_congr_of_support _ _ _ fun u _ =>
            (ih u (hoa.2 u) (c.cacheQuery d u)).trans (by rw [hfun u])).trans ?_
          exact hres d hdS ψ
        · rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih u (hoa.2 u) c]
          simp

end Lazy

/-! ## Concrete cells of a function table -/

section Cells

variable {I R α : Type} [DecidableEq I]

/-- Overwrite the coordinates `idx j` of `g` by the entries of the vector `v`. -/
noncomputable def writeBlock {n : ℕ} (g : I → R) (idx : Fin n → I) (v : Vector R n) : I → R :=
  fun i => if h : ∃ j, idx j = i then v[h.choose] else g i

/-- The coordinates `idx j` of `g`, as a vector. -/
def readBlock {n : ℕ} (g : I → R) (idx : Fin n → I) : Vector R n :=
  Vector.ofFn fun j => g (idx j)

theorem writeBlock_apply_idx {n : ℕ} (g : I → R) {idx : Fin n → I}
    (hinj : Function.Injective idx) (v : Vector R n) (j : Fin n) :
    writeBlock g idx v (idx j) = v[j] := by
  have h : ∃ j', idx j' = idx j := ⟨j, rfl⟩
  have e : writeBlock g idx v (idx j) = v[h.choose] := by simp [writeBlock]
  rw [e]
  exact congrArg (fun k : Fin n => v[k]) (hinj h.choose_spec)

theorem writeBlock_apply_of_forall_ne {n : ℕ} (g : I → R) (idx : Fin n → I) (v : Vector R n)
    {i : I} (h : ∀ j, idx j ≠ i) : writeBlock g idx v i = g i := by
  simp [writeBlock, h]

omit [DecidableEq I] in
@[simp] theorem readBlock_getElem {n : ℕ} (g : I → R) (idx : Fin n → I) (j : Fin n) :
    (readBlock g idx)[j] = g (idx j) := by
  simp [readBlock]

theorem readBlock_writeBlock {n : ℕ} (g : I → R) {idx : Fin n → I}
    (hinj : Function.Injective idx) (v : Vector R n) :
    readBlock (writeBlock g idx v) idx = v := by
  ext j hj
  have := writeBlock_apply_idx g hinj v ⟨j, hj⟩
  simpa [readBlock] using this

theorem writeBlock_writeBlock {n : ℕ} (g : I → R) (idx : Fin n → I) (v v' : Vector R n) :
    writeBlock (writeBlock g idx v) idx v' = writeBlock g idx v' := by
  funext i
  by_cases h : ∃ j, idx j = i <;> simp [writeBlock, h]

theorem writeBlock_readBlock {n : ℕ} (g : I → R) (idx : Fin n → I) :
    writeBlock g idx (readBlock g idx) = g := by
  funext i
  by_cases h : ∃ j, idx j = i
  · have e : writeBlock g idx (readBlock g idx) i = (readBlock g idx)[h.choose] := by
      simp [writeBlock, h]
    rw [e, readBlock_getElem, h.choose_spec]
  · simp [writeBlock, h]

/-- Reading a block disjoint from the written one is unaffected. -/
theorem readBlock_writeBlock_of_disjoint {n : ℕ} (g : I → R) (idx idx' : Fin n → I)
    (v : Vector R n) (h : ∀ j j', idx j ≠ idx' j') :
    readBlock (writeBlock g idx v) idx' = readBlock g idx' := by
  ext j hj
  simp only [readBlock, Vector.getElem_ofFn]
  exact writeBlock_apply_of_forall_ne g idx v fun j' => h j' ⟨j, hj⟩

/-- Overwrite the coordinates listed in `is` by the corresponding entries of `xs` (stops at the
shorter list; for a duplicate-free `is` the order is irrelevant). -/
def updateList (g : I → R) : List I → List R → I → R
  | i :: is, x :: xs => Function.update (updateList g is xs) i x
  | _, _ => g

@[simp] theorem updateList_nil_left (g : I → R) (xs : List R) : updateList g [] xs = g := by
  cases xs <;> rfl

@[simp] theorem updateList_nil_right (g : I → R) (is : List I) : updateList g is [] = g := by
  cases is <;> rfl

@[simp] theorem updateList_cons (g : I → R) (i : I) (is : List I) (x : R) (xs : List R) :
    updateList g (i :: is) (x :: xs) = Function.update (updateList g is xs) i x := rfl

theorem updateList_apply_of_not_mem (g : I → R) (is : List I) (xs : List R) {i : I}
    (hi : i ∉ is) : updateList g is xs i = g i := by
  induction is generalizing xs with
  | nil => simp
  | cons j is ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [updateList_cons,
        Function.update_of_ne (fun h : i = j => hi (by rw [h]; exact List.mem_cons_self))]
      exact ih xs fun h => hi (List.mem_cons_of_mem _ h)

/-- A duplicate-free index list reads back exactly the written values. -/
theorem map_updateList (g : I → R) {is : List I} (hnd : is.Nodup) {xs : List R}
    (hlen : xs.length = is.length) : is.map (updateList g is xs) = xs := by
  induction is generalizing xs with
  | nil => cases xs <;> simp_all
  | cons j is ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, updateList_cons, Function.update_self, List.cons.injEq, true_and]
      have h1 : is.map (Function.update (updateList g is xs) j x) =
          is.map (updateList g is xs) :=
        List.map_congr_left fun i hi =>
          Function.update_of_ne (fun h : i = j => hnd.1 (by rw [← h]; exact hi)) _ _
      rw [h1]
      exact ih hnd.2 (by simpa using hlen)

/-- Positional form of `map_updateList`. -/
theorem updateList_getElem (g : I → R) {is : List I} (hnd : is.Nodup) {xs : List R}
    (hlen : xs.length = is.length) (j : ℕ) (hj : j < is.length) :
    updateList g is xs is[j] = xs[j]'(hlen ▸ hj) := by
  have h := map_updateList g hnd hlen
  have h2 : (is.map (updateList g is xs))[j]'(by simpa using hj) = xs[j]'(hlen ▸ hj) := by
    simp only [h]
  simpa using h2

/-- Take the coordinates satisfying `p` from `g₁` and the others from `g₂`. -/
def mix (p : I → Prop) [DecidablePred p] (g₁ g₂ : I → R) : I → R :=
  fun i => if p i then g₁ i else g₂ i

omit [DecidableEq I] in
theorem mix_apply_of_pos {p : I → Prop} [DecidablePred p] (g₁ g₂ : I → R) {i : I} (h : p i) :
    mix p g₁ g₂ i = g₁ i := by simp [mix, h]

omit [DecidableEq I] in
theorem mix_apply_of_neg {p : I → Prop} [DecidablePred p] (g₁ g₂ : I → R) {i : I} (h : ¬p i) :
    mix p g₁ g₂ i = g₂ i := by simp [mix, h]

/-- `n` independent uniform samples, as a list (head sampled first). -/
noncomputable def sampleList (R : Type) [SampleableType R] : ℕ → ProbComp (List R)
  | 0 => pure []
  | n + 1 => do
    let x ← $ᵗ R
    let xs ← sampleList R n
    pure (x :: xs)

theorem length_of_mem_support_sampleList [SampleableType R] {n : ℕ} {xs : List R}
    (h : xs ∈ support (sampleList R n)) : xs.length = n := by
  induction n generalizing xs with
  | zero => simp_all [sampleList]
  | succ n ih =>
    simp only [sampleList, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at h
    obtain ⟨x, -, ys, hys, rfl⟩ := h
    simp [ih hys]

variable [Fintype I] [SampleableType R] [UniformSampler I R] [MeasurableSpace α]

/-- **One cell, extraction form.**  Reading coordinate `i` of a uniform table is the same as
overwriting it by a fresh uniform value and returning that value. -/
theorem evalDist_extract_cell (i : I) (f : R → (I → R) → ProbComp α) :
    𝒟[$ᵗ R >>= fun u => uniformTable I R >>= fun g => f u (Function.update g i u)] =
      𝒟[uniformTable I R >>= fun g => f (g i) g] :=
  evalDist_lens_extract (uniformTable I R) evalDist_uniformTable' (fun g => g i)
    (fun g u => Function.update g i u) (fun g u => by simp) (fun g u u' => by simp)
    (fun g => by simp) f

/-- **One cell.**  Overwriting a coordinate of a uniform table by a fresh uniform value changes
nothing. -/
theorem evalDist_resample_cell (i : I) (f : (I → R) → ProbComp α) :
    𝒟[$ᵗ R >>= fun u => uniformTable I R >>= fun g => f (Function.update g i u)] =
      𝒟[uniformTable I R >>= f] :=
  evalDist_extract_cell i fun _ g => f g

/-- **A block of cells, extraction form.**  The coordinates `idx j` (`idx` injective) of a
uniform table are a uniform vector; equivalently they can be overwritten by one. -/
theorem evalDist_extract_block {n : ℕ} {idx : Fin n → I} (hinj : Function.Injective idx)
    (f : Vector R n → (I → R) → ProbComp α) :
    𝒟[$ᵗ (Vector R n) >>= fun v => uniformTable I R >>= fun g => f v (writeBlock g idx v)] =
      𝒟[uniformTable I R >>= fun g => f (readBlock g idx) g] :=
  evalDist_lens_extract (uniformTable I R) evalDist_uniformTable' (fun g => readBlock g idx)
    (fun g v => writeBlock g idx v) (fun g v => readBlock_writeBlock g hinj v)
    (fun g v v' => writeBlock_writeBlock g idx v v') (fun g => writeBlock_readBlock g idx) f

/-- **A block of cells.** -/
theorem evalDist_resample_block {n : ℕ} {idx : Fin n → I} (hinj : Function.Injective idx)
    (f : (I → R) → ProbComp α) :
    𝒟[$ᵗ (Vector R n) >>= fun v => uniformTable I R >>= fun g => f (writeBlock g idx v)] =
      𝒟[uniformTable I R >>= f] :=
  evalDist_extract_block hinj fun _ g => f g

/-- **A list of cells, extraction form** (samples drawn one by one, before the table).  For a
duplicate-free index list `is`, the values `is.map g` of a uniform table are independent uniform
samples; equivalently they can be overwritten by such samples. -/
theorem evalDist_extract_list {is : List I} (hnd : is.Nodup)
    (f : List R → (I → R) → ProbComp α) :
    𝒟[sampleList R is.length >>= fun xs => uniformTable I R >>= fun g =>
        f xs (updateList g is xs)] =
      𝒟[uniformTable I R >>= fun g => f (is.map g) g] := by
  induction is generalizing f with
  | nil => simp [sampleList]
  | cons i is ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.length_cons, sampleList, bind_assoc, pure_bind, updateList_cons,
      List.map_cons]
    refine (evalDist_bind_congr_of_support _ _ _ fun x _ =>
      ih hnd.2 fun xs g => f (x :: xs) (Function.update g i x)).trans ?_
    have key := evalDist_extract_cell i fun (u : R) (g : I → R) => f (u :: is.map g) g
    refine Eq.trans ?_ key
    refine evalDist_bind_congr_of_support _ _ _ fun x _ => ?_
    refine evalDist_bind_congr_of_support _ _ _ fun g _ => ?_
    have : is.map (Function.update g i x) = is.map g :=
      List.map_congr_left fun j hj =>
        Function.update_of_ne (fun h : j = i => hnd.1 (by rw [← h]; exact hj)) _ _
    rw [this]

/-- **A list of cells, extraction form** (table sampled first, as in a reduction that samples
its table before the game samples the targets). -/
theorem evalDist_extract_list' {is : List I} (hnd : is.Nodup)
    (f : List R → (I → R) → ProbComp α) :
    𝒟[uniformTable I R >>= fun g => sampleList R is.length >>= fun xs =>
        f xs (updateList g is xs)] =
      𝒟[uniformTable I R >>= fun g => f (is.map g) g] :=
  (OracleComp.evalDist_bind_bind_swap _ _ _).trans (evalDist_extract_list hnd f)

/-- **A list of cells.** -/
theorem evalDist_resample_list (is : List I) (hnd : is.Nodup) (f : (I → R) → ProbComp α) :
    𝒟[uniformTable I R >>= fun g => sampleList R is.length >>= fun xs =>
        f (updateList g is xs)] =
      𝒟[uniformTable I R >>= f] :=
  evalDist_extract_list' hnd fun _ g => f g

omit [DecidableEq I] in
/-- **Merging two tables.**  Two independent uniform tables, one used on the coordinates
satisfying `p` and the other elsewhere, are one uniform table. -/
theorem evalDist_uniformTable_mix (p : I → Prop) [DecidablePred p] (f : (I → R) → ProbComp α) :
    𝒟[uniformTable I R >>= fun g₁ => uniformTable I R >>= fun g₂ => f (mix p g₁ g₂)] =
      𝒟[uniformTable I R >>= f] := by
  set σ : (I → R) × (I → R) → (I → R) × (I → R) :=
    fun q => (mix p q.2 q.1, mix p q.1 q.2) with hσ
  have hσinv : Function.Involutive σ := fun q => by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      by_cases h : p i <;> simp [hσ, mix, h]
  have key := evalDist_uniform_pair_bijective (uniformTable I R) (uniformTable I R)
    evalDist_uniformTable' evalDist_uniformTable' σ hσinv.bijective
    (fun q : (I → R) × (I → R) => f q.2)
  simp only [hσ] at key
  rw [key]
  exact OracleComp.evalDist_bind_const _ _

end Cells

/-! ## Lazy random function = uniform table -/

section LazyTable

variable {D I R α : Type} [DecidableEq D] [DecidableEq I] [Fintype I] [SampleableType R]
  [UniformSampler I R] [MeasurableSpace α]

/-- **Lazy = eager, cache-parametrised.**  A lazy random function `D → R` (any `D`), started
from the cache `c` and queried only inside a set `S` on which the index map `e : D → I` is
injective, has the law of a uniform table read through `e` and overlaid by `c`. -/
theorem evalDist_romImpl_run'_eq_uniformTable_of_cache (e : D → I) {S : Set D}
    (he : Set.InjOn e S) (oa : OracleComp (unifSpec + (D →ₒ R)) α) (hoa : QueriesIn S oa)
    (c : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ (D →ₒ R).romImpl oa).run' c] =
      𝒟[uniformTable I R >>= fun g => simulateQ (fnImpl fun d => (c d).getD (g (e d))) oa] :=
  evalDist_romImpl_run'_eq_of_lens (uniformTable I R) (fun g d => g (e d))
    (fun g d u => Function.update g (e d) u) S (fun g d u _ => by simp)
    (fun g d u d' hd hd' hne => Function.update_of_ne (fun h => hne (he hd' hd h)) _ _)
    (fun d _ f => evalDist_resample_cell (e d) f) oa hoa c

/-- **Lazy = eager.**  A lazy random function `D → R` queried only inside a set `S` on which
`e : D → I` is injective is the uniform table `g : I → R` read as `g ∘ e`. -/
theorem evalDist_romImpl_run'_eq_uniformTable (e : D → I) {S : Set D}
    (he : Set.InjOn e S) (oa : OracleComp (unifSpec + (D →ₒ R)) α) (hoa : QueriesIn S oa) :
    𝒟[(simulateQ (D →ₒ R).romImpl oa).run' ∅] =
      𝒟[uniformTable I R >>= fun g => simulateQ (fnImpl fun d => g (e d)) oa] :=
  evalDist_romImpl_run'_eq_uniformTable_of_cache e he oa hoa ∅

/-- **Lazy = eager, block form, cache-parametrised.**  A lazy random function with range
`Vector R n` whose query `d` owns the `n` table cells `e d j`, the cells of distinct queries of
`S` being distinct. -/
theorem evalDist_romImpl_run'_eq_uniformTable_block_of_cache {n : ℕ} (e : D → Fin n → I)
    {S : Set D}
    (he : ∀ d ∈ S, ∀ d' ∈ S, ∀ j j', e d j = e d' j' → d = d' ∧ j = j')
    (oa : OracleComp (unifSpec + (D →ₒ Vector R n)) α) (hoa : QueriesIn S oa)
    (c : (D →ₒ Vector R n).QueryCache) :
    𝒟[(simulateQ (D →ₒ Vector R n).romImpl oa).run' c] =
      𝒟[uniformTable I R >>= fun g =>
        simulateQ (fnImpl fun d => (c d).getD (readBlock g (e d))) oa] := by
  have hinj : ∀ d ∈ S, Function.Injective (e d) := fun d hd j j' h => (he d hd d hd j j' h).2
  exact evalDist_romImpl_run'_eq_of_lens (uniformTable I R) (fun g d => readBlock g (e d))
    (fun g d v => writeBlock g (e d) v) S
    (fun g d v hd => readBlock_writeBlock g (hinj d hd) v)
    (fun g d v d' hd hd' hne => readBlock_writeBlock_of_disjoint g (e d) (e d') v
      fun j j' h => hne (he d hd d' hd' j j' h).1.symm)
    (fun d hd f => evalDist_resample_block (hinj d hd) f) oa hoa c

/-- **Lazy = eager, block form.** -/
theorem evalDist_romImpl_run'_eq_uniformTable_block {n : ℕ} (e : D → Fin n → I) {S : Set D}
    (he : ∀ d ∈ S, ∀ d' ∈ S, ∀ j j', e d j = e d' j' → d = d' ∧ j = j')
    (oa : OracleComp (unifSpec + (D →ₒ Vector R n)) α) (hoa : QueriesIn S oa) :
    𝒟[(simulateQ (D →ₒ Vector R n).romImpl oa).run' ∅] =
      𝒟[uniformTable I R >>= fun g => simulateQ (fnImpl fun d => readBlock g (e d)) oa] :=
  evalDist_romImpl_run'_eq_uniformTable_block_of_cache e he oa hoa ∅

/-- **Lazy block function next to a table = one table.**  A computation `oa g` that depends
on a uniform table `g` only outside the cells `e d j` (`d ∈ S`), and has access to a lazy random
function with range `Vector R n` queried inside `S`, is the same computation reading the blocks
`e d` of the *same* table.  (The form in which a reduction that samples its own table and
receives further fresh vectors from a game oracle is compared with a one-table game.) -/
theorem evalDist_uniformTable_bind_romImpl_block {n : ℕ} (e : D → Fin n → I) {S : Set D}
    (he : ∀ d ∈ S, ∀ d' ∈ S, ∀ j j', e d j = e d' j' → d = d' ∧ j = j')
    (oa : (I → R) → OracleComp (unifSpec + (D →ₒ Vector R n)) α)
    (hoa : ∀ g, QueriesIn S (oa g))
    (hdep : ∀ g g', (∀ i, (∀ d ∈ S, ∀ j, e d j ≠ i) → g i = g' i) → oa g = oa g') :
    𝒟[uniformTable I R >>= fun g => (simulateQ (D →ₒ Vector R n).romImpl (oa g)).run' ∅] =
      𝒟[uniformTable I R >>= fun g =>
        simulateQ (fnImpl fun d => readBlock g (e d)) (oa g)] := by
  classical
  set p : I → Prop := fun i => ∃ d ∈ S, ∃ j, e d j = i with hp
  set f : (I → R) → ProbComp α := fun h =>
    simulateQ (fnImpl fun d => readBlock h (e d)) (oa h) with hf
  have hpt : ∀ g g₂ : I → R,
      simulateQ (fnImpl fun d => readBlock g₂ (e d)) (oa g) = f (mix p g₂ g) := by
    intro g g₂
    have h1 : oa (mix p g₂ g) = oa g := hdep _ _ fun i hi =>
      mix_apply_of_neg g₂ g (by
        rintro ⟨d, hd, j, hj⟩
        exact hi d hd j hj)
    simp only [hf, h1]
    refine simulateQ_fnImpl_congr (hoa g) fun d hd => ?_
    ext j hj
    simp only [readBlock, Vector.getElem_ofFn]
    exact (mix_apply_of_pos g₂ g ⟨d, hd, ⟨j, hj⟩, rfl⟩).symm
  refine (evalDist_bind_congr_of_support _ _ _ fun g _ =>
    evalDist_romImpl_run'_eq_uniformTable_block e he (oa g) (hoa g)).trans ?_
  simp only [hpt]
  exact (OracleComp.evalDist_bind_bind_swap _ _ _).trans (evalDist_uniformTable_mix p f)

/-! ### Fresh sampling at never-repeated points -/

/-- The handler answering every function query by a *fresh* uniform sample (no cache). -/
noncomputable def freshImpl (D V : Type) [SampleableType V] :
    QueryImpl (unifSpec + (D →ₒ V)) ProbComp :=
  unifSpec.passthrough + (fun _ => $ᵗ V : QueryImpl (D →ₒ V) ProbComp)

/-- No function query of `oa` is at a point of `seen` or at a point queried earlier on the same
execution path (uniform-sampling queries are free).  This is a VCVio `IsQueryBound` whose budget
is the set of points already used, so `isQueryBound_query_bind_iff`, `isQueryBound_bind`,
`IsQueryBound.simulateQ_run_of_step` apply. -/
def NoRepeat {V α : Type} (seen : Set D) (oa : OracleComp (unifSpec + (D →ₒ V)) α) : Prop :=
  oa.IsQueryBound seen (fun t s => Sum.elim (fun _ => True) (fun d => d ∉ s) t)
    (fun t s => Sum.elim (fun _ => s) (fun d => insert d s) t)

/-- `freshImpl` is transparent on a lifted `ProbComp`. -/
@[simp] theorem simulateQ_freshImpl_liftM {V : Type} [SampleableType V] (oa : ProbComp α) :
    simulateQ (freshImpl D V) (liftM oa : OracleComp (unifSpec + (D →ₒ V)) α) = oa := by
  simp [freshImpl, QueryImpl.simulateQ_add_liftM_left]

/-- `freshImpl` answers a function query by a fresh uniform sample. -/
@[simp] theorem simulateQ_freshImpl_query {V : Type} [SampleableType V] (d : D) :
    simulateQ (freshImpl D V) (liftM ((unifSpec + (D →ₒ V)).query (Sum.inr d)) :
      OracleComp (unifSpec + (D →ₒ V)) V) = $ᵗ V := by
  rw [simulateQ_spec_query]
  rfl

/-- A lifted `ProbComp` repeats no function query. -/
theorem noRepeat_liftM {V : Type} (seen : Set D) (oa : ProbComp α) :
    NoRepeat seen (liftM oa : OracleComp (unifSpec + (D →ₒ V)) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBound_pure _ _ _ _
  | query_bind n k ih =>
    rw [liftM_bind]
    exact (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨trivial, ih⟩

/-- **Fresh = lazy.**  On a computation that never repeats a function query (and never queries a
cached point), the lazy random function is fresh sampling.  An equality of programs. -/
theorem simulateQ_romImpl_run'_eq_freshImpl {V : Type} [SampleableType V]
    (oa : OracleComp (unifSpec + (D →ₒ V)) α) (c : (D →ₒ V).QueryCache)
    (h : NoRepeat {d | (c d).isSome} oa) :
    (simulateQ (D →ₒ V).romImpl oa).run' c = simulateQ (freshImpl D V) oa := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
      rw [NoRepeat, isQueryBound_query_bind_iff] at h
      rcases t with n | d
      · have hred :
            (simulateQ (D →ₒ V).romImpl
              (liftM ((unifSpec + (D →ₒ V)).query (.inl n)) >>= k)).run' c =
            (unifSpec.query n : ProbComp _) >>= fun u =>
              (simulateQ (D →ₒ V).romImpl (k u)).run' c := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
            roSim.run_apply_inl]
          simp [StateT.run'_eq]
        have heval :
            simulateQ (freshImpl D V) (liftM ((unifSpec + (D →ₒ V)).query (.inl n)) >>= k) =
              (unifSpec.query n : ProbComp _) >>= fun u => simulateQ (freshImpl D V) (k u) := by
          simp [freshImpl]
        rw [hred, heval]
        exact congrArg _ (funext fun u => ih u c (h.2 u))
      · have hc : c d = none := by
          have := h.1
          simpa using this
        have hred :
            (simulateQ (D →ₒ V).romImpl
              (liftM ((unifSpec + (D →ₒ V)).query (.inr d)) >>= k)).run' c =
            ((D →ₒ V).randomOracle d).run c >>= fun p =>
              (simulateQ (D →ₒ V).romImpl (k p.1)).run' p.2 := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
          rfl
        have heval :
            simulateQ (freshImpl D V) (liftM ((unifSpec + (D →ₒ V)).query (.inr d)) >>= k) =
              ($ᵗ V : ProbComp V) >>= fun u => simulateQ (freshImpl D V) (k u) := by
          rw [simulateQ_bind, simulateQ_spec_query]
          rfl
        rw [hred, heval, QueryImpl.withCaching_run_none _ hc, map_eq_bind_pure_comp]
        simp only [Function.comp, bind_assoc, pure_bind]
        refine congrArg _ (funext fun u => ih u (c.cacheQuery d u) ?_)
        have hset : {d' | ((c.cacheQuery d u) d').isSome} = insert d {d' | (c d').isSome} := by
          ext d'
          by_cases hdd : d' = d
          · subst hdd; simp
          · simp [hdd]
        rw [hset]
        exact h.2 u

/-- **Fresh sampling = uniform table.**  Fresh uniform answers at never-repeated points of a set
`S` on which `e : D → I` is injective are the uniform table read through `e`. -/
theorem evalDist_freshImpl_eq_uniformTable (e : D → I) {S : Set D} (he : Set.InjOn e S)
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (hoa : QueriesIn S oa) (hnr : NoRepeat ∅ oa) :
    𝒟[simulateQ (freshImpl D R) oa] =
      𝒟[uniformTable I R >>= fun g => simulateQ (fnImpl fun d => g (e d)) oa] := by
  rw [← simulateQ_romImpl_run'_eq_freshImpl oa ∅ (by simpa using hnr)]
  exact evalDist_romImpl_run'_eq_uniformTable e he oa hoa

/-- **Fresh vectors next to a table = one table.**  As
`evalDist_uniformTable_bind_romImpl_block`, for a computation that draws a fresh uniform vector
at each (never repeated) query. -/
theorem evalDist_uniformTable_bind_freshImpl_block {n : ℕ} (e : D → Fin n → I) {S : Set D}
    (he : ∀ d ∈ S, ∀ d' ∈ S, ∀ j j', e d j = e d' j' → d = d' ∧ j = j')
    (oa : (I → R) → OracleComp (unifSpec + (D →ₒ Vector R n)) α)
    (hoa : ∀ g, QueriesIn S (oa g)) (hnr : ∀ g, NoRepeat ∅ (oa g))
    (hdep : ∀ g g', (∀ i, (∀ d ∈ S, ∀ j, e d j ≠ i) → g i = g' i) → oa g = oa g') :
    𝒟[uniformTable I R >>= fun g => simulateQ (freshImpl D (Vector R n)) (oa g)] =
      𝒟[uniformTable I R >>= fun g =>
        simulateQ (fnImpl fun d => readBlock g (e d)) (oa g)] := by
  have h : ∀ g, simulateQ (freshImpl D (Vector R n)) (oa g) =
      (simulateQ (D →ₒ Vector R n).romImpl (oa g)).run' ∅ := fun g =>
    (simulateQ_romImpl_run'_eq_freshImpl (oa g) ∅ (by simpa using hnr g)).symm
  simp only [h]
  exact evalDist_uniformTable_bind_romImpl_block e he oa hoa hdep

/-! ### PRF-game form -/

/-- The "PRF" whose key is a uniform table and whose evaluation reads it through `e`. -/
noncomputable def tablePrf (e : D → I) : PRFScheme (I → R) D R where
  keygen := uniformTable I R
  eval := fun g d => g (e d)

omit [DecidableEq D] [DecidableEq I] in
theorem prfRealQueryImpl_tablePrf (e : D → I) (g : I → R) :
    (tablePrf e).prfRealQueryImpl g = fnImpl fun d => g (e d) := rfl

/-- The ideal PRF experiment is the real experiment of the table PRF, for a distinguisher that
queries only inside a set on which `e` is injective. -/
theorem evalDist_prfIdealExperiment_eq_tablePrf (e : D → I) {S : Set D}
    (he : Set.InjOn e S) (adv : PRFScheme.PRFAdversary D R) (hadv : QueriesIn S adv) :
    𝒟[PRFScheme.prfIdealExperiment adv] = 𝒟[(tablePrf e).prfRealExperiment adv] :=
  evalDist_romImpl_run'_eq_uniformTable e he adv hadv

/-- The ideal PRF experiment of a distinguisher `liftM pre >>= rest` whose query set (and index
map) may depend on the output of its oracle-free prefix `pre`. -/
theorem evalDist_prfIdealExperiment_liftM_bind {σ : Type} (pre : ProbComp σ)
    (rest : σ → OracleComp (PRFScheme.PRFOracleSpec D R) α) (e : σ → D → I) (S : σ → Set D)
    (he : ∀ s ∈ support pre, Set.InjOn (e s) (S s))
    (hrest : ∀ s ∈ support pre, QueriesIn (S s) (rest s)) :
    𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := R))
        (liftM pre >>= rest)).run' ∅] =
      𝒟[pre >>= fun s => uniformTable I R >>= fun g =>
        simulateQ (fnImpl fun d => g (e s d)) (rest s)] := by
  rw [simulateQ_bind]
  refine (congrArg _ (roSim.run'_liftM_bind _ pre _ ∅)).trans ?_
  exact evalDist_bind_congr_of_support _ _ _ fun s hs =>
    evalDist_romImpl_run'_eq_uniformTable (e s) (he s hs) (rest s) (hrest s hs)

end LazyTable

end Tables

/-! ## Specialisations to the secret table of the reduction -/

section Secret

open SLHDSA SLHDSA.Security

variable {vp : ValidatedParams} {prims : Primitives vp.params} [SampleableType prims.Y]
variable {α : Type} [MeasurableSpace α]

/-- `sampleTable` is the uniform table on `SecIdx`. -/
theorem sampleTable_eq_uniformTable :
    sampleTable vp prims = Tables.uniformTable SecIdx prims.Y := rfl

/-- `sampleTable` denotes the uniform measure, for every measurable structure with measurable
singletons on the table type. -/
theorem evalDist_sampleTable [MeasurableSpace (SecretTable vp prims)]
    [MeasurableSingletonClass (SecretTable vp prims)] :
    𝒟[sampleTable vp prims] = uniformOn Set.univ :=
  Tables.evalDist_uniformTable'

/-- **P1.**  The ideal `PRF` world of a distinguisher `liftM pre >>= rest` which, after its
oracle-free prefix `pre` (which fixes `PK.seed = pk s`), queries its function oracle only at
`(pk s, a)` with `a` canonical: the lazy function is the uniform secret table read by
`secretOf`. `hinj` is `secIdx_injOn_canonical`. -/
theorem evalDist_prfIdeal_eq_sampleTable [DecidableEq prims.PkSeed] {σ : Type}
    (hinj : Set.InjOn secIdx {a : Adrs | a.isCanonical = true})
    (pre : ProbComp σ) (pk : σ → prims.PkSeed)
    (rest : σ → OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) α)
    (hrest : ∀ s ∈ support pre, Tables.QueriesIn
      {d : prims.PkSeed × Adrs | d.1 = pk s ∧ d.2.isCanonical = true} (rest s)) :
    𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl (D := prims.PkSeed × Adrs) (R := prims.Y))
        (liftM pre >>= rest)).run' ∅] =
      𝒟[pre >>= fun s => sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun d => secretOf vp prims tbl d.2) (rest s)] :=
  Tables.evalDist_prfIdealExperiment_liftM_bind pre rest (fun _ d => secIdx d.2)
    (fun s => {d : prims.PkSeed × Adrs | d.1 = pk s ∧ d.2.isCanonical = true})
    (fun _ _ _ hd _ hd' h => Prod.ext (hd.1.trans hd'.1.symm) (hinj hd.2 hd'.2 h)) hrest

/-- **P4.**  The secrets at a duplicate-free list of table indices are independent uniform
samples drawn after the table: overwrite them and hand the samples to the continuation. -/
theorem evalDist_sampleTable_extract_list {is : List SecIdx} (hnd : is.Nodup)
    (f : List prims.Y → SecretTable vp prims → ProbComp α) :
    𝒟[sampleTable vp prims >>= fun tbl => Tables.sampleList prims.Y is.length >>= fun xs =>
        f xs (Tables.updateList tbl is xs)] =
      𝒟[sampleTable vp prims >>= fun tbl => f (is.map tbl) tbl] :=
  Tables.evalDist_extract_list' hnd f

/-- **P6.**  A reduction that samples its own table `tbl`, uses it only outside the cells
`e d j` (`d ∈ S`), and obtains fresh uniform vectors from a lazy random function on `S`, is the
one-table computation in which the vector at `d` is the block `e d` of `tbl`. -/
theorem evalDist_sampleTable_bind_romImpl_block {D : Type} [DecidableEq D] {n : ℕ}
    (e : D → Fin n → SecIdx) {S : Set D}
    (he : ∀ d ∈ S, ∀ d' ∈ S, ∀ j j', e d j = e d' j' → d = d' ∧ j = j')
    (oa : SecretTable vp prims → OracleComp (unifSpec + (D →ₒ Vector prims.Y n)) α)
    (hoa : ∀ tbl, Tables.QueriesIn S (oa tbl))
    (hdep : ∀ tbl tbl', (∀ i, (∀ d ∈ S, ∀ j, e d j ≠ i) → tbl i = tbl' i) → oa tbl = oa tbl') :
    𝒟[sampleTable vp prims >>= fun tbl =>
        (simulateQ (D →ₒ Vector prims.Y n).romImpl (oa tbl)).run' ∅] =
      𝒟[sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun d => Tables.readBlock tbl (e d)) (oa tbl)] :=
  Tables.evalDist_uniformTable_bind_romImpl_block e he oa hoa hdep

/-- **P6**, fresh-sampling form: as `evalDist_sampleTable_bind_romImpl_block` for a reduction
whose vectors are drawn afresh at never-repeated points (the shape of `WotsGame.signOracle`). -/
theorem evalDist_sampleTable_bind_freshImpl_block {D : Type} [DecidableEq D] {n : ℕ}
    (e : D → Fin n → SecIdx) {S : Set D}
    (he : ∀ d ∈ S, ∀ d' ∈ S, ∀ j j', e d j = e d' j' → d = d' ∧ j = j')
    (oa : SecretTable vp prims → OracleComp (unifSpec + (D →ₒ Vector prims.Y n)) α)
    (hoa : ∀ tbl, Tables.QueriesIn S (oa tbl)) (hnr : ∀ tbl, Tables.NoRepeat ∅ (oa tbl))
    (hdep : ∀ tbl tbl', (∀ i, (∀ d ∈ S, ∀ j, e d j ≠ i) → tbl i = tbl' i) → oa tbl = oa tbl') :
    𝒟[sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.freshImpl D (Vector prims.Y n)) (oa tbl)] =
      𝒟[sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun d => Tables.readBlock tbl (e d)) (oa tbl)] :=
  Tables.evalDist_uniformTable_bind_freshImpl_block e he oa hoa hnr hdep

end Secret

/-! ## `prTrue` calculus -/

section PrTrue

variable {α : Type}

/-- `prTrue` only depends on the output law. -/
theorem prTrue_congr {g₁ g₂ : ProbComp Bool} (h : 𝒟[g₁] = 𝒟[g₂]) : prTrue g₁ = prTrue g₂ := by
  rw [prTrue, prTrue, h]

theorem prTrue_pure (b : Bool) : prTrue (pure b) = if b then 1 else 0 := by
  cases b <;> simp [prTrue]

/-- `Pr[true]` of a sequential composition is the expectation of the continuation's. -/
theorem prTrue_bind (oa : ProbComp α) (f : α → ProbComp Bool) :
    prTrue (oa >>= f) = (letI : MeasurableSpace α := ⊤; ∫⁻ x, prTrue (f x) ∂𝒟[oa]) := by
  let : MeasurableSpace α := ⊤
  rw [prTrue, evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable]
  rfl

/-- Monotonicity under a common prefix; the continuations are compared on the support only. -/
theorem prTrue_bind_mono (oa : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ x ∈ support oa, prTrue (f x) ≤ prTrue (g x)) :
    prTrue (oa >>= f) ≤ prTrue (oa >>= g) := by
  let : MeasurableSpace α := ⊤
  rw [prTrue_bind, prTrue_bind]
  exact lintegral_mono_ae (evalDist.ae_of_forall_mem_support oa _ .of_discrete h)

/-- Congruence under a common prefix. -/
theorem prTrue_bind_congr (oa : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ x ∈ support oa, prTrue (f x) = prTrue (g x)) :
    prTrue (oa >>= f) = prTrue (oa >>= g) :=
  le_antisymm (prTrue_bind_mono oa f g fun x hx => (h x hx).le)
    (prTrue_bind_mono oa g f fun x hx => (h x hx).ge)

/-- Union bound under a common prefix. -/
theorem prTrue_bind_le_add (oa : ProbComp α) (f g h : α → ProbComp Bool)
    (hfgh : ∀ x ∈ support oa, prTrue (f x) ≤ prTrue (g x) + prTrue (h x)) :
    prTrue (oa >>= f) ≤ prTrue (oa >>= g) + prTrue (oa >>= h) := by
  let : MeasurableSpace α := ⊤
  rw [prTrue_bind, prTrue_bind, prTrue_bind, ← lintegral_add_left Measurable.of_discrete]
  exact lintegral_mono_ae (evalDist.ae_of_forall_mem_support oa _ .of_discrete hfgh)

/-- Event inclusion: if the final predicate `p` implies `q` on the support, `Pr[p] ≤ Pr[q]`. -/
theorem prTrue_bind_pure_mono (oa : ProbComp α) (p q : α → Bool)
    (h : ∀ x ∈ support oa, p x = true → q x = true) :
    prTrue (oa >>= fun x => pure (p x)) ≤ prTrue (oa >>= fun x => pure (q x)) :=
  prTrue_bind_mono oa _ _ fun x hx => by
    have := h x hx
    rw [prTrue_pure, prTrue_pure]
    cases hp : p x <;> cases hq : q x <;> simp_all

/-- Union bound on the final predicate: `Pr[p] ≤ Pr[q] + Pr[r]` when `p → q ∨ r`. -/
theorem prTrue_bind_pure_le_add (oa : ProbComp α) (p q r : α → Bool)
    (h : ∀ x ∈ support oa, p x = true → q x = true ∨ r x = true) :
    prTrue (oa >>= fun x => pure (p x)) ≤
      prTrue (oa >>= fun x => pure (q x)) + prTrue (oa >>= fun x => pure (r x)) :=
  prTrue_bind_le_add oa _ _ _ fun x hx => by
    have := h x hx
    rw [prTrue_pure, prTrue_pure, prTrue_pure]
    cases hp : p x <;> cases hq : q x <;> cases hr : r x <;> simp_all

end PrTrue

end Reduction

section Axioms
open Reduction Reduction.Tables
#print axioms Reduction.Tables.evalDist_uniform_pair_bijective
#print axioms Reduction.Tables.evalDist_extract_list
#print axioms Reduction.Tables.evalDist_extract_block
#print axioms Reduction.Tables.evalDist_uniformTable_mix
#print axioms Reduction.Tables.evalDist_romImpl_run'_eq_of_lens
#print axioms Reduction.Tables.evalDist_romImpl_run'_eq_uniformTable
#print axioms Reduction.Tables.evalDist_romImpl_run'_eq_uniformTable_block
#print axioms Reduction.Tables.evalDist_uniformTable_bind_romImpl_block
#print axioms Reduction.Tables.simulateQ_romImpl_run'_eq_freshImpl
#print axioms Reduction.Tables.evalDist_freshImpl_eq_uniformTable
#print axioms Reduction.Tables.evalDist_prfIdealExperiment_eq_tablePrf
#print axioms Reduction.evalDist_prfIdeal_eq_sampleTable
#print axioms Reduction.evalDist_sampleTable_extract_list
#print axioms Reduction.evalDist_sampleTable_bind_romImpl_block
#print axioms Reduction.evalDist_sampleTable_bind_freshImpl_block
#print axioms Reduction.prTrue_bind_pure_le_add
#print axioms Reduction.prTrue_bind_congr
end Axioms
