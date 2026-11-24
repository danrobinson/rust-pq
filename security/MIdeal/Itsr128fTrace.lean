import MIdeal.Itsr128fGame

namespace MIdeal.Hmsg.Fast128
open MLink Ideal Ideal.Itsr Ideal.HP SLHDSA SLHDSA.Concrete OracleComp OracleSpec

abbrev Trace := List (St × Blk)
def logCell (t : (St × Blk) × Bool) (s : Trace) := s ++ [t.1]

abbrev traceImpl (g : CF St Blk) := stImpl (spec := mS St Blk) (fun t => g t.1) logCell

private theorem read_bind {α : Type} (g : CF St Blk) (c : St) (b : Blk) (m : Bool)
    (k : St → Prog α) (l : Trace) :
    (simulateQ (traceImpl g) (cq c b m >>= k)).run l =
      (simulateQ (traceImpl g) (k (g (c,b)))).run (l ++ [(c,b)]) :=
  run_stImpl_inr_bind (spec := mS St Blk) (fun t => g t.1) logCell ((c,b),m) k l

theorem md_trace (g : CF St Blk) (s : St) (bs : List Blk) (l : Trace) :
    (simulateQ (traceImpl g) (mdMF s bs)).run l = pure (mdFold g s bs, l ++ mdCells g s bs) := by
  induction bs generalizing s l with
  | nil => simp [mdMF, mdFold, mdCells]
  | cons b bs ih =>
    rw [mdMF, read_bind, ih]
    simp [mdFold, mdCells]

theorem hash_trace (g : CF St Blk) (x : Input) (l : Trace) :
    (simulateQ (traceImpl g) (hash x)).run l = pure (rowDigest g (g (prefixCell g x)), l ++ cells g x) := by
  unfold hash
  rw [simulateQ_bind, StateT.run_bind, md_trace, pure_bind, read_bind, read_bind, read_bind]
  simp [cells, prefixCell, rowDigest, List.append_assoc]

theorem hashes_trace (g : CF St Blk) (xs : List Input) (l : Trace) :
    (simulateQ (traceImpl g) (hashes xs)).run l =
      pure (xs.map (fun x => rowDigest g (g (prefixCell g x))), l ++ xs.flatMap (cells g)) := by
  induction xs generalizing l with
  | nil => simp [hashes]
  | cons x xs ih =>
    rw [hashes, simulateQ_bind, StateT.run_bind, hash_trace, pure_bind, simulateQ_bind,
      StateT.run_bind, ih, pure_bind]
    simp [List.append_assoc]

def uniqueCells {C : Type} [DecidableEq C] (proj : St × Blk → C) (l : Trace) : List C :=
  l.foldl (fun s t => logU proj t s) []

theorem mem_uniqueCells {C : Type} [DecidableEq C] (proj : St × Blk → C) (z : C) (l : Trace) :
    z ∈ uniqueCells proj l ↔ ∃ t ∈ l, proj t = z := by
  induction l using List.reverseRecOn generalizing z with
  | nil => simp [uniqueCells]
  | append_singleton l t ih =>
    change z ∈ (l ++ [t]).foldl _ [] ↔ _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change z ∈ logU proj t (uniqueCells proj l) ↔ _
    have rhs : (∃ u ∈ l ++ [t], proj u = z) ↔ (∃ u ∈ l, proj u = z) ∨ z = proj t := by
      constructor
      · rintro ⟨u,hu,eq⟩
        rcases List.mem_append.mp hu with h | h
        · exact Or.inl ⟨u,h,eq⟩
        · exact Or.inr (eq.symm.trans (congrArg proj (List.mem_singleton.mp h)))
      · rintro (⟨u,hu,e⟩ | rfl)
        · exact ⟨u,List.mem_append_left _ hu,e⟩
        · exact ⟨t,by simp,rfl⟩
    rw [rhs, ← ih]
    by_cases h : proj t ∈ uniqueCells proj l
    · rw [logU_of_mem h]
      exact ⟨Or.inl, fun e => e.elim id (fun e' => e' ▸ h)⟩
    · simp [logU_of_not_mem h]

theorem unique_run {C α : Type} [DecidableEq C] (proj : St × Blk → C) (g : CF St Blk)
    (oa : Prog α) (l : Trace) :
    (simulateQ (stImpl (spec := mS St Blk) (fun t => g t.1) (logU (fun t => proj t.1))) oa).run
      (uniqueCells proj l) =
      (fun z => (z.1,uniqueCells proj z.2)) <$> (simulateQ (traceImpl g) oa).run l := by
  induction oa using OracleComp.inductionOn generalizing l with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with n | t
    · rw [run_stImpl_inl_bind, run_stImpl_inl_bind, map_bind]
      exact bind_congr fun u => ih u l
    · rw [run_stImpl_inr_bind, run_stImpl_inr_bind, ← ih]
      simp [uniqueCells, logCell, logU]
      rfl

noncomputable def coverage (g : CF St Blk) (tr : Trace) : Bool :=
  covB (idxOf Sha2Set.s128f.vp) ((uniqueCells Prod.fst tr).map (rowDigest g))

def bad (g : CF St Blk) (tr : Trace) : Bool := badV IV128 ((uniqueCells id tr).map g)

theorem win_trace (g : CF St Blk) (A : ItsrAdvI St Blk Key Msg) (z : Bool × Trace)
    (hz : z ∈ support ((simulateQ (traceImpl g) (game A)).run [])) (hw : z.1 = true) :
    coverage g z.2 = true ∨ bad g z.2 = true := by
  classical
  by_cases hb : bad g z.2 = true
  · exact Or.inr hb
  refine Or.inl ?_
  simp only [game, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨⟨cand,targets⟩,start⟩,_,hz⟩ := hz
  simp only [finish,simulateQ_bind,StateT.run_bind, hashes_trace, pure_bind,hash_trace,
    simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at hz
  subst z
  simp only [decide_eq_true_eq] at hw
  let tr := (start ++ targets.flatMap (cells g)) ++ cells g cand
  change ¬ badV IV128 ((uniqueCells id tr).map g) = true at hb
  simp only [badV, decide_eq_true_eq, not_or, not_not] at hb
  change covB _ _ = true
  apply decide_eq_true
  apply win_row_coverage _ g (uniqueCells id tr) _ cand targets _ _ _ _ hw.1 ?_
  · intro x hx c hc
    apply (mem_uniqueCells _ _ _).mpr
    refine ⟨c,?_,rfl⟩
    rcases List.mem_cons.mp hx with rfl | h
    · exact List.mem_append_right _ hc
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x,h,hc⟩))
  · intro z hz
    obtain ⟨c,hc,rfl⟩ := (mem_uniqueCells _ _ _).mp hz
    exact (mem_uniqueCells _ _ _).mpr ⟨c,hc,rfl⟩
  · intro c hc d hd eq
    exact List.inj_on_of_nodup_map hb.1 hc hd eq
  · intro c hc eq
    exact hb.2 (eq ▸ List.mem_map_of_mem hc)
  · intro i hi
    obtain ⟨d,hd,hit⟩ := List.mem_flatMap.mp (hw.2 i hi)
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
    exact List.mem_flatMap.mpr ⟨x,hx,hit⟩

end MIdeal.Hmsg.Fast128
