import Ideal.Core.HPBad
import Ideal.Games.PrfLemmas
import VCVio.CryptoFoundations.PRF

/-!
# Generic lemmas for the HMAC-style PRF game in the ideal-compression model

* `relabelImpl ρ f`: answer every oracle query `t` by one query `ρ t` to another interface,
  post-processed by `f t`; evaluation, traces and query bounds of the relabelled program.
* `cellsQ`: the table cells read by a phase-one query (`HP.chainToT`); the trace of the
  table-level program is the concatenation of the cells of the traced queries.
* `coll_of_chainI_eq` (Merkle–Damgård): two different block lists with the same chain value read
  two distinct cells with the same table value.
* `prT_sumTable`: a uniform table on a sum type is a pair of independent uniform tables.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.MsgPrf

open Ideal.HP Ideal.Prf

/-! ## Relabelling the oracle queries of a program -/

section Relabel

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α τ : Type}

/-- Answer the oracle query `t` by the query `ρ t` to `spec'`, post-processed by `f t`. -/
def relabelImpl (ρ : ι → ι') (f : (t : ι) → spec'.Range (ρ t) → spec.Range t) :
    QueryImpl (unifSpec + spec) (OracleComp (unifSpec + spec')) := fun
  | .inl n => (unifSpec + spec').query (.inl n)
  | .inr t => f t <$> (liftM ((unifSpec + spec').query (.inr (ρ t))) :
      OracleComp (unifSpec + spec') (spec'.Range (ρ t)))

theorem simulateQ_stImpl_relabel (a' : (t : ι') → spec'.Range t) (u' : ι' → τ → τ) (ρ : ι → ι')
    (f : (t : ι) → spec'.Range (ρ t) → spec.Range t) (oa : OracleComp (unifSpec + spec) α) :
    simulateQ (stImpl a' u') (simulateQ (relabelImpl ρ f) oa) =
      simulateQ (stImpl (fun t => f t (a' (ρ t))) fun t s => u' (ρ t) s) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with n | t
  · exact simulateQ_spec_query _ _
  · refine StateT.ext fun s => ?_
    simp [relabelImpl, stImpl]

theorem simulateQ_ansImpl_relabel (a' : (t : ι') → spec'.Range t) (ρ : ι → ι')
    (f : (t : ι) → spec'.Range (ρ t) → spec.Range t) (oa : OracleComp (unifSpec + spec) α) :
    simulateQ (ansImpl a') (simulateQ (relabelImpl ρ f) oa) =
      simulateQ (ansImpl fun t => f t (a' (ρ t))) oa := by
  rw [← fst_map_run_stImpl a' (fun _ (s : Unit) => s) _ (), simulateQ_stImpl_relabel,
    fst_map_run_stImpl]

theorem isQueryBoundP_relabel (ρ : ι → ι') (f : (t : ι) → spec'.Range (ρ t) → spec.Range t)
    (p' : ℕ ⊕ ι' → Prop) [DecidablePred p'] (oa : OracleComp (unifSpec + spec) α) (n : ℕ)
    (h : IsQueryBoundP oa (fun i => p' (Sum.map id ρ i)) n) :
    IsQueryBoundP (simulateQ (relabelImpl ρ f) oa) p' n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with m | t
    · simp only [relabelImpl]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · simp only [relabelImpl, bind_map_left]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih _ _ (h.2 _)⟩

theorem allQueriesSatisfy_relabel (ρ : ι → ι') (f : (t : ι) → spec'.Range (ρ t) → spec.Range t)
    (P : ℕ ⊕ ι' → Prop) (oa : OracleComp (unifSpec + spec) α)
    (h : AllQueriesSatisfy oa (fun i => P (Sum.map id ρ i))) :
    AllQueriesSatisfy (simulateQ (relabelImpl ρ f) oa) P := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with m | t
    · simp only [relabelImpl]
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨h.1, fun u => ih u (h.2 u)⟩
    · simp only [relabelImpl, bind_map_left]
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨h.1, fun u => ih _ (h.2 _)⟩

theorem foldl_append_eq_flatMap {β γ : Type} (F : β → List γ) (l : List β) (s : List γ) :
    l.foldl (fun s t => s ++ F t) s = s ++ l.flatMap F := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The trace of a run with list-valued state updates. -/
theorem run_stImpl_append_eq_trace {γ : Type} (a : (t : ι) → spec.Range t) (F : ι → List γ)
    (oa : OracleComp (unifSpec + spec) α) :
    (simulateQ (stImpl a fun t l => l ++ F t) oa).run [] =
      (fun z => (z.1, z.2.flatMap F)) <$> (simulateQ (trImpl a) oa).run [] := by
  have h := run_stImpl_eq_trace a (fun t (l : List γ) => l ++ F t) oa [] []
  simp only [List.foldl_nil] at h
  rw [h]
  simp only [foldl_append_eq_flatMap, List.nil_append]

end Relabel

/-! ## The cells read by a chain query -/

section Cells

variable {St Blk : Type}

/-- The public cells read by the continuation from `c` through `bs`. -/
def rcells (g : CF St Blk) : St → List Blk → List ((St × Blk) ⊕ Blk)
  | _, [] => []
  | c, b :: bs => .inl (c, b) :: rcells g (g (c, b)) bs

/-- The cells read by the chain query `x`: the private row cell of its first block, then public
cells. -/
def cells (g : CF St Blk) (T : Blk → St) (x : Blk × List Blk) : List ((St × Blk) ⊕ Blk) :=
  .inr x.1 :: rcells g (T x.1) x.2

/-- The cells read by a phase-one query. -/
def cellsQ (g : CF St Blk) (T : Blk → St) :
    (St × Blk) ⊕ (Blk × List Blk) → List ((St × Blk) ⊕ Blk)
  | .inl q => [.inl q]
  | .inr x => cells g T x

theorem rcells_append (g : CF St Blk) (c : St) (bs : List Blk) (b : Blk) :
    rcells g c (bs ++ [b]) = rcells g c bs ++ [.inl (mdFold g c bs, b)] := by
  induction bs generalizing c with
  | nil => rfl
  | cons a bs ih => simp only [List.cons_append, rcells, ih]; rfl

theorem mdFold_append (g : CF St Blk) (c : St) (bs : List Blk) (b : Blk) :
    mdFold g c (bs ++ [b]) = g (mdFold g c bs, b) := by
  simp [mdFold]

theorem rcells_length (g : CF St Blk) (c : St) (bs : List Blk) :
    (rcells g c bs).length = bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons a bs ih => simp [rcells, ih]

theorem run_stImpl_foldlM_trace (g : CF St Blk) (T : Blk → St) (bs : List Blk) (c : St)
    (s : List ((St × Blk) ⊕ Blk)) :
    (simulateQ (trImpl (tbl g T))
        (bs.foldlM (fun c b => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b))))
          c)).run s =
      pure (mdFold g c bs, s ++ rcells g c bs) := by
  induction bs generalizing c s with
  | nil => simp [mdFold, rcells]
  | cons b bs ih =>
    rw [List.foldlM_cons, run_stImpl_inr_bind, ih]
    simp only [mdFold, rcells, tbl, List.foldl_cons, List.append_assoc, List.singleton_append]

/-- The trace of the table-level program is the concatenation of the cells of the traced
phase-one queries. -/
theorem simulateQ_trImpl_chainToT {α : Type} (g : CF St Blk) (T : Blk → St)
    (oa : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) α) :
    simulateQ (trImpl (tbl g T)) (simulateQ chainToT oa) =
      simulateQ (stImpl (pairAns g (chainI g T)) fun t l => l ++ cellsQ g T t) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with n | q | q
  · exact simulateQ_spec_query _ _
  · exact simulateQ_spec_query _ _
  · refine StateT.ext fun s => ?_
    simp only [chainToT]
    rw [run_stImpl_inr_bind]
    exact (run_stImpl_foldlM_trace g T q.2 (T q.1) _).trans
      (by simp [stImpl, pairAns, chainI, cellsQ, cells])

/-- **Merkle–Damgård.**  Two different chain queries with the same chain value read two distinct
cells with the same table value. -/
theorem coll_of_chainI_eq (g : CF St Blk) (T : Blk → St) (bs : List Blk) :
    ∀ (b₁ b₁' : Blk) (bs' : List Blk), (b₁, bs) ≠ (b₁', bs') →
      mdFold g (T b₁) bs = mdFold g (T b₁') bs' →
      ∃ c ∈ cells g T (b₁, bs), ∃ c' ∈ cells g T (b₁', bs'),
        c ≠ c' ∧ Sum.elim g T c = Sum.elim g T c' := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro b₁ b₁' bs' hne h
    rcases List.eq_nil_or_concat bs' with rfl | ⟨L, b, hL⟩ <;>
      try (rw [List.concat_eq_append] at hL; subst hL)
    · refine ⟨.inr b₁, by simp [cells], .inr b₁', by simp [cells], fun e => hne ?_, h⟩
      rw [Sum.inr.inj e]
    · refine ⟨.inr b₁, by simp [cells], .inl (mdFold g (T b₁') L, b), ?_, by simp, ?_⟩
      · simp [cells, rcells_append]
      · rw [mdFold_append] at h
        exact h
  | append_singleton as a ih =>
    intro b₁ b₁' bs' hne h
    rcases List.eq_nil_or_concat bs' with rfl | ⟨L, b, hL⟩ <;>
      try (rw [List.concat_eq_append] at hL; subst hL)
    · refine ⟨.inl (mdFold g (T b₁) as, a), ?_, .inr b₁', by simp [cells], by simp, ?_⟩
      · simp [cells, rcells_append]
      · rw [mdFold_append] at h
        exact h
    · rw [mdFold_append, mdFold_append] at h
      by_cases hc : (mdFold g (T b₁) as, a) = (mdFold g (T b₁') L, b)
      · obtain ⟨hm, hab⟩ := Prod.mk.inj hc
        subst hab
        have hne' : (b₁, as) ≠ (b₁', L) := fun e => hne (by
          obtain ⟨e1, e2⟩ := Prod.mk.inj e
          rw [e1, e2])
        obtain ⟨c, hcm, c', hcm', hcc, hJ⟩ := ih b₁ b₁' L hne' hm
        refine ⟨c, ?_, c', ?_, hcc, hJ⟩
        · simp only [cells, rcells_append, List.mem_cons, List.mem_append] at hcm ⊢
          tauto
        · simp only [cells, rcells_append, List.mem_cons, List.mem_append] at hcm' ⊢
          tauto
      · refine ⟨.inl (mdFold g (T b₁) as, a), ?_, .inl (mdFold g (T b₁') L, b), ?_,
          fun e => hc (Sum.inl.inj e), h⟩
        · simp [cells, rcells_append]
        · simp [cells, rcells_append]

end Cells

/-! ## A uniform table on a sum type -/

theorem prT_sumTable {A B V : Type} [Finite A] [Finite B] [Finite V] [Nonempty V]
    [SampleableType (A ⊕ B → V)] [SampleableType (A → V)] [SampleableType (B → V)]
    (F : (A ⊕ B → V) → ProbComp Bool) :
    prT ($ᵗ (A ⊕ B → V) >>= F) =
      prT ($ᵗ (A → V) >>= fun g => $ᵗ (B → V) >>= fun T => F (Sum.elim g T)) := by
  let : MeasurableSpace (A → V) := ⊤
  let : MeasurableSpace (B → V) := ⊤
  let : MeasurableSpace (A ⊕ B → V) := ⊤
  refine prT_congr ?_
  have hu : 𝒟[Sum.elim <$> ($ᵗ (A → V)) <*> ($ᵗ (B → V))] =
      ProbabilityTheory.uniformOn (Set.univ : Set (A ⊕ B → V)) :=
    evalDist_seq_map_eq_uniformOn _ _ Sum.elim SampleableType.evalDist_uniformSample
      SampleableType.evalDist_uniformSample Measurable.of_discrete
      ⟨fun x y h => by
          obtain ⟨x1, x2⟩ := x
          obtain ⟨y1, y2⟩ := y
          simp only [Function.uncurry] at h
          have h1 : x1 = y1 := funext fun a => congrFun h (.inl a)
          have h2 : x2 = y2 := funext fun b => congrFun h (.inr b)
          rw [h1, h2],
        fun J => ⟨(fun a => J (.inl a), fun b => J (.inr b)), by
          funext t; rcases t with a | b <;> rfl⟩⟩
  have h1 : ($ᵗ (A → V) >>= fun g => $ᵗ (B → V) >>= fun T => F (Sum.elim g T)) =
      (Sum.elim <$> ($ᵗ (A → V)) <*> ($ᵗ (B → V))) >>= F := by
    simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  rw [h1, evalDist_bind_of_discrete, evalDist_bind_of_discrete, hu,
    SampleableType.evalDist_uniformSample]

end Ideal.MsgPrf

#print axioms Ideal.MsgPrf.coll_of_chainI_eq
#print axioms Ideal.MsgPrf.prT_sumTable
#print axioms Ideal.MsgPrf.simulateQ_trImpl_chainToT
