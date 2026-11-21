import Ideal.Core.HPHop

/-!
# The chaining-value-equals-`IV` event

`hasIV` marks the phase-one queries of the eager ideal game one of whose table answers (the
public answer, the private row answer or a continuation value of a chain query) equals `IV`.
`prEvent_trace_hasIV_le`: over uniform tables, some traced query is marked with probability at
most `(q₁ + C * (1 + L)) / |St|`.  The proof moves to the lazy random oracle, where every fresh
answer equals `IV` with probability `1 / |St|`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.HP

variable {St Blk : Type}

/-! ## Counting the table queries of phase one -/

theorem isQueryBoundP_foldlM (bs : List Blk) (c : St) :
    IsQueryBoundP
      (bs.foldlM (m := OracleComp (unifSpec + (hS St Blk + tS St Blk)))
        (fun c b => liftM ((unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b))))) c)
      (fun i => Sum.isRight i = true) bs.length := by
  induction bs generalizing c with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldlM_cons, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by simp), fun u => ?_⟩
    simpa using ih u

theorem isQueryBoundP_chainToT {α : Type}
    (oa : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) α) (a c L : ℕ)
    (ha : IsQueryBoundP oa (fun i => isPub i = true) a)
    (hc : IsQueryBoundP oa (fun i => isChain i = true) c)
    (hL : AllQueriesSatisfy oa (chainLenLe L)) :
    IsQueryBoundP (simulateQ chainToT oa) (fun i => Sum.isRight i = true) (a + c * (1 + L)) := by
  induction oa using OracleComp.inductionOn generalizing a c with
  | pure x => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at ha hc
    rw [allQueriesSatisfy_query_bind_iff] at hL
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with n | q | q
    · simp only [isPub, isChain, Bool.false_eq_true, ite_false] at ha hc
      simp only [chainToT]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (by simp), fun u => ?_⟩
      simpa using ih u a c (ha.2 u) (hc.2 u) (hL.2 u)
    · simp only [isPub, isChain, Bool.false_eq_true, ite_false, ite_true, not_true, false_or]
        at ha hc
      simp only [chainToT]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr (by omega), fun u => ?_⟩
      simp only [Sum.isRight_inr, ite_true]
      refine (ih u (a - 1) c (ha.2 u) (hc.2 u) (hL.2 u)).mono ?_
      have := ha.1
      omega
    · simp only [isPub, isChain, Bool.false_eq_true, ite_false, ite_true, not_true, false_or]
        at ha hc
      have hlen : q.2.length ≤ L := hL.1
      have hstep : IsQueryBoundP (chainToT (St := St) (Blk := Blk) (.inr (.inr q)))
          (fun i => Sum.isRight i = true) (1 + q.2.length) := by
        simp only [chainToT]
        rw [isQueryBoundP_query_bind_iff]
        refine ⟨Or.inr (by omega), fun u => ?_⟩
        simpa using isQueryBoundP_foldlM q.2 u
      refine (isQueryBoundP_bind hstep fun u _ =>
        ih u a (c - 1) (ha.2 u) (hc.2 u) (hL.2 u)).mono ?_
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by have := hc.1; omega⟩
      simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
      omega

/-! ## The flag at the level of table queries -/

/-- A table answer equals `IV`. -/
def isIV [DecidableEq St] (IV : St) :
    (t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t → Bool
  | .inl _, u => decide (u = IV)
  | .inr _, u => decide (u = IV)

/-- Forward every query, raising the flag when a table answer equals `IV`. -/
def flagFwd [DecidableEq St] (IV : St) :
    QueryImpl (unifSpec + (hS St Blk + tS St Blk))
      (StateT Bool (OracleComp (unifSpec + (hS St Blk + tS St Blk)))) := fun
  | .inl n => StateT.mk fun b => do
      let x ← (unifSpec + (hS St Blk + tS St Blk)).query (.inl n)
      pure (x, b)
  | .inr t => StateT.mk fun b => do
      let u ← (unifSpec + (hS St Blk + tS St Blk)).query (.inr t)
      pure (u, b || isIV IV t u)

section Flag

variable [DecidableEq St] {α : Type}

theorem run_flagFwd_inl_bind (IV : St) (n : ℕ)
    (k : (unifSpec + (hS St Blk + tS St Blk)).Range (.inl n) →
      OracleComp (unifSpec + (hS St Blk + tS St Blk)) α) (b : Bool) :
    (simulateQ (flagFwd IV) (liftM ((unifSpec + (hS St Blk + tS St Blk)).query (.inl n)) >>= k)).run
        b =
      liftM ((unifSpec + (hS St Blk + tS St Blk)).query (.inl n)) >>= fun x =>
        (simulateQ (flagFwd IV) (k x)).run b := by
  rw [run_simulateQ_query_bind]
  simp [flagFwd]

theorem run_flagFwd_inr_bind (IV : St) (t : (St × Blk) ⊕ Blk)
    (k : (unifSpec + (hS St Blk + tS St Blk)).Range (.inr t) →
      OracleComp (unifSpec + (hS St Blk + tS St Blk)) α) (b : Bool) :
    (simulateQ (flagFwd IV) (liftM ((unifSpec + (hS St Blk + tS St Blk)).query (.inr t)) >>= k)).run
        b =
      liftM ((unifSpec + (hS St Blk + tS St Blk)).query (.inr t)) >>= fun u =>
        (simulateQ (flagFwd IV) (k u)).run (b || isIV IV t u) := by
  rw [run_simulateQ_query_bind]
  simp [flagFwd]

/-- The flagged program at a fixed table. -/
theorem simulateQ_ansImpl_run_flagFwd (IV : St)
    (F : (t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t)
    (M : OracleComp (unifSpec + (hS St Blk + tS St Blk)) α) (b : Bool) :
    simulateQ (ansImpl F) ((simulateQ (flagFwd IV) M).run b) =
      (simulateQ (stImpl F fun t b => b || isIV IV t (F t)) M).run b := by
  induction M using OracleComp.inductionOn generalizing b with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with n | t
    · rw [run_flagFwd_inl_bind, simulateQ_ansImpl_inl_bind, run_stImpl_inl_bind]
      exact bind_congr fun x => ih x b
    · rw [run_flagFwd_inr_bind, simulateQ_ansImpl_inr_bind, run_stImpl_inr_bind]
      exact ih _ _

end Flag

/-! ## The flag at the level of phase-one queries -/

/-- Some later chaining value of the continuation from `c` through `bs` equals `IV`. -/
def restIV [DecidableEq St] (IV : St) (g : CF St Blk) : St → List Blk → Bool
  | _, [] => false
  | c, b :: bs => decide (g (c, b) = IV) || restIV IV g (g (c, b)) bs

/-- Some table answer read by a phase-one query equals `IV`. -/
def hasIV [DecidableEq St] (IV : St) (g : CF St Blk) (T : Blk → St) :
    (St × Blk) ⊕ (Blk × List Blk) → Bool
  | .inl q => decide (g q = IV)
  | .inr q => decide (T q.1 = IV) || restIV IV g (T q.1) q.2

theorem run_stImpl_foldlM [DecidableEq St] (IV : St) (g : CF St Blk) (T : Blk → St)
    (bs : List Blk) (c : St) (s : Bool) :
    (simulateQ (stImpl (tbl g T) fun t b => b || isIV IV t (tbl g T t))
        (bs.foldlM (fun c b => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b))))
          c)).run s =
      pure (mdFold g c bs, s || restIV IV g c bs) := by
  induction bs generalizing c s with
  | nil => simp [mdFold, restIV]
  | cons b bs ih =>
    rw [List.foldlM_cons, run_stImpl_inr_bind, ih]
    simp only [mdFold, restIV, isIV, tbl, Bool.or_assoc, List.foldl_cons]
    rfl

/-- The flag of the table-level run is the flag of the phase-one run. -/
theorem run_stImpl_chainToT [DecidableEq St] {α : Type} (IV : St) (g : CF St Blk) (T : Blk → St)
    (oa : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) α) (b : Bool) :
    (simulateQ (stImpl (tbl g T) fun t b => b || isIV IV t (tbl g T t))
        (simulateQ chainToT oa)).run b =
      (simulateQ (stImpl (pairAns g (chainI g T)) fun t b => b || hasIV IV g T t) oa).run b := by
  have key : simulateQ (stImpl (tbl g T) fun t b => b || isIV IV t (tbl g T t))
        (simulateQ chainToT oa) =
      simulateQ (stImpl (pairAns g (chainI g T)) fun t b => b || hasIV IV g T t) oa := by
    refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
    rcases t with n | q | q
    · exact simulateQ_spec_query _ _
    · exact simulateQ_spec_query _ _
    · refine StateT.ext fun s => ?_
      simp only [chainToT]
      rw [run_stImpl_inr_bind]
      exact (run_stImpl_foldlM IV g T q.2 (T q.1) _).trans
        (by simp [stImpl, pairAns, chainI, hasIV, isIV, tbl, Bool.or_assoc]; rfl)
  rw [key]

theorem foldl_or_eq_any {ι : Type} (h : ι → Bool) (l : List ι) (b : Bool) :
    l.foldl (fun s t => s || h t) b = (b || l.any h) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, Bool.or_assoc]

/-! ## The lazy bound -/

section Lazy

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] {α : Type}

theorem run'_romImpl_inl_bind {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t, SampleableType (spec.Range t)] (n : ℕ)
    (k : (unifSpec + spec).Range (.inl n) → OracleComp (unifSpec + spec) α)
    (c : spec.QueryCache) :
    (simulateQ spec.romImpl (liftM ((unifSpec + spec).query (.inl n)) >>= k)).run' c =
      (unifSpec.query n : ProbComp _) >>= fun u => (simulateQ spec.romImpl (k u)).run' c := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
    roSim.run_apply_inl]
  simp [StateT.run'_eq]

theorem run'_romImpl_inr_bind {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t, SampleableType (spec.Range t)] (t : ι)
    (k : (unifSpec + spec).Range (.inr t) → OracleComp (unifSpec + spec) α)
    (c : spec.QueryCache) :
    (simulateQ spec.romImpl (liftM ((unifSpec + spec).query (.inr t)) >>= k)).run' c =
      (spec.randomOracle t).run c >>= fun p => (simulateQ spec.romImpl (k p.1)).run' p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [DecidableEq Blk] in
theorem prEvent_isIV [Fintype St] (IV : St) (t : (St × Blk) ⊕ Blk) :
    Pr{let u ← $ᵗ ((hS St Blk + tS St Blk).Range t)}[isIV IV t u = true] =
      (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rcases t with q | B
  · simp only [isIV, decide_eq_true_eq]
    exact SampleableType.prEvent_uniformSample_eq_singleton IV
  · simp only [isIV, decide_eq_true_eq]
    exact SampleableType.prEvent_uniformSample_eq_singleton IV

/-- In the lazy random oracle, a program with at most `n` table queries raises the flag with
probability at most `n / |St|`. -/
theorem prT_flag_lazy [Fintype St] (IV : St)
    (M : OracleComp (unifSpec + (hS St Blk + tS St Blk)) α) (n : ℕ)
    (hn : IsQueryBoundP M (fun i => Sum.isRight i = true) n)
    (c : (hS St Blk + tS St Blk).QueryCache) (hc : ∀ t v, c t = some v → isIV IV t v = false) :
    prT ((simulateQ (hS St Blk + tS St Blk).romImpl
        (Prod.snd <$> (simulateQ (flagFwd IV) M).run false)).run' c) ≤
      n * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  induction M using OracleComp.inductionOn generalizing n c with
  | pure x => simp [prT_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rcases t with m | t
    · rw [run_flagFwd_inl_bind, map_bind, run'_romImpl_inl_bind]
      exact prT_bind_le_of_forall_le _ _ fun u _ => ih u n (by simpa using hn.2 u) c hc
    · rw [run_flagFwd_inr_bind, map_bind, run'_romImpl_inr_bind]
      have hpos : 0 < n := by simpa using hn.1
      have hk : ∀ u, IsQueryBoundP (k u) (fun i => Sum.isRight i = true) (n - 1) := fun u => by
        simpa using hn.2 u
      have hle : ((n - 1 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ ≤
          n * (Fintype.card St : ℝ≥0∞)⁻¹ := by
        gcongr
        exact Nat.sub_le _ _
      rcases hct : c t with _ | v
      · rw [QueryImpl.withCaching_run_none _ hct, bind_map_left]
        refine (prT_bind_le_prEvent_add _ _ (fun u => isIV IV t u = true)
          (ε := ((n - 1 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹) ?_).trans ?_
        · intro u _ hu
          simp only [Bool.not_eq_true] at hu
          simp only [Bool.false_or, hu]
          refine ih u (n - 1) (hk u) _ fun t' v hv => ?_
          by_cases htt : t' = t
          · subst htt
            rw [QueryCache.cacheQuery_self] at hv
            rw [← Option.some.inj hv]
            exact hu
          · rw [QueryCache.cacheQuery_of_ne _ _ htt] at hv
            exact hc t' v hv
        · rw [uniformSampleImpl_apply, prEvent_isIV]
          obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
          rw [add_mul, one_mul, add_comm]
      · rw [QueryImpl.withCaching_run_some _ hct, pure_bind]
        simp only [Bool.false_or, hc t v hct]
        exact (ih v (n - 1) (hk v) c hc).trans hle

end Lazy

/-! ## The bound for the eager trace -/

theorem prEvent_trace_hasIV_le [Fintype St] [DecidableEq St] [DecidableEq Blk]
    [SampleableType St] [Fintype Blk] [SampleableType (CF St Blk)] {σ : Type} (IV : St)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ) (q₁ C L : ℕ)
    (hq : IsQueryBoundP prog₁ (fun i => isPub i = true) q₁)
    (hC : IsQueryBoundP prog₁ (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy prog₁ (chainLenLe L)) :
    prT ($ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T =>
        (simulateQ (trImpl (pairAns g (chainI g T))) prog₁).run [] >>= fun z =>
          pure (z.2.any (hasIV IV g T))) ≤
      ((q₁ + C * (1 + L) : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  let : SampleableType ((t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t) :=
    SampleableType.ofEquiv tblEquiv
  set Mb : OracleComp (unifSpec + (hS St Blk + tS St Blk)) Bool :=
    Prod.snd <$> (simulateQ (flagFwd IV) (simulateQ chainToT prog₁)).run false with hMb
  have hlazy := prT_flag_lazy IV (simulateQ chainToT prog₁) _
    (isQueryBoundP_chainToT prog₁ q₁ C L hq hC hL) ∅ (fun t v hv => by simp at hv)
  refine le_of_eq_of_le ?_ hlazy
  rw [← hMb]
  have h1 := OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable Mb
    (∅ : (hS St Blk + tS St Blk).QueryCache)
  rw [prT_congr h1]
  have hdraw : ∀ k : ((t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t) → ProbComp Bool,
      ($ᵗ ((t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t) >>= k) =
        $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T => k (tbl g T) := by
    intro k
    change (tblEquiv <$> ((·, ·) <$> ($ᵗ (CF St Blk)) <*> ($ᵗ (Blk → St)))) >>= k = _
    simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    rfl
  rw [hdraw]
  refine congrArg prT (bind_congr fun g => bind_congr fun T => ?_)
  rw [OracleComp.completeTable_empty, hMb, simulateQ_map, simulateQ_ansImpl_run_flagFwd,
    run_stImpl_chainToT]
  have h2 := run_stImpl_eq_trace (pairAns g (chainI g T)) (fun t b => b || hasIV IV g T t)
    prog₁ false []
  simp only [List.foldl_nil] at h2
  rw [h2]
  simp [foldl_or_eq_any, map_eq_bind_pure_comp]

end Ideal.HP

#print axioms Ideal.HP.prEvent_trace_hasIV_le
