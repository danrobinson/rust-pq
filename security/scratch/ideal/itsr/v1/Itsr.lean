import Ideal.Games.ItsrDefs

/-!
# ITSR in the ideal-compression model: reduction to a tape of independent uniform digests

`itsr_le`: for a uniformly random compression table, the ITSR experiment for
`H_g(k, x) = od (MD_g (ob (k, x) (MD_g (ib (k, x)))))` is won with probability at most

`Pr[covB idx (tape)] + Q² / |St|`,

where `tape` is a list of `Q` independent uniform digests, `covB idx` says that some entry of the
list has all its indices among the indices of the *other* entries, and `Q` bounds the compression
calls of the whole experiment `gameProg` (the adversary's and those of the final check).

Proof: the experiment is run while logging the distinct compression cells it reads.  Unless two
logged cells have the same value or a logged cell has value `IV` (`badV`, at most `Q² / |St|` by
`prT_tape_bad_le`), distinct hash inputs have distinct final cells (Merkle–Damgård walk-back,
`md_inj`, and injectivity of the block maps), so a win exhibits a logged cell — the final cell of
the candidate — whose digest indices are covered by the digests of other logged cells — the final
cells of the targets (`win_imp`).  The digests of the logged cells are dominated by a tape of
independent uniform digests (`prT_tape_le`).
-/

open OracleComp OracleSpec ENNReal KeyedHash

namespace Ideal.Itsr

open Ideal.HP Ideal.Prf AnswerTape

variable {St Blk K X Y Index : Type}

/-! ## Coverage of a list of digests -/

/-- Some entry of the list has all its indices among the indices of the other entries. -/
def CovP (idx : Y → List Index) (l : List Y) : Prop :=
  ∃ pre y post, l = pre ++ y :: post ∧ ∀ i ∈ idx y, ∃ z ∈ pre ++ post, i ∈ idx z

open Classical in
/-- `CovP` as a Boolean. -/
noncomputable def covB (idx : Y → List Index) (l : List Y) : Bool := decide (CovP idx l)

theorem covP_mono (idx : Y → List Index) (l l' : List Y) (h : l.Sublist l') (hc : CovP idx l) :
    CovP idx l' := by
  obtain ⟨pre, y, post, rfl, hcov⟩ := hc
  obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.append_sublist_iff.mp h
  obtain ⟨u, v, rfl, hy, h₃⟩ := List.cons_sublist_iff.mp h₂
  obtain ⟨u₁, u₂, rfl⟩ := List.append_of_mem hy
  refine ⟨r₁ ++ u₁, y, u₂ ++ v, by simp, fun i hi => ?_⟩
  obtain ⟨z, hz, hiz⟩ := hcov i hi
  refine ⟨z, ?_, hiz⟩
  rcases List.mem_append.mp hz with hz | hz
  · have := h₁.subset hz
    simp [this]
  · have := h₃.subset hz
    simp [this]

theorem covB_mono (idx : Y → List Index) (l l' : List Y) (h : l.Sublist l')
    (hc : covB idx l = true) : covB idx l' = true := by
  simp only [covB, decide_eq_true_eq] at hc ⊢
  exact covP_mono idx l l' h hc

/-! ## Merkle–Damgård cells -/

/-- The cells read by the iteration from `c` through `bs`. -/
def mdCells (g : CF St Blk) : St → List Blk → List (St × Blk)
  | _, [] => []
  | c, b :: bs => (c, b) :: mdCells g (g (c, b)) bs

theorem mdCells_append (g : CF St Blk) (c : St) (bs : List Blk) (b : Blk) :
    mdCells g c (bs ++ [b]) = mdCells g c bs ++ [(mdFold g c bs, b)] := by
  induction bs generalizing c with
  | nil => rfl
  | cons a bs ih => simp only [List.cons_append, mdCells, ih]; rfl

theorem mdFold_append (g : CF St Blk) (c : St) (bs : List Blk) (b : Blk) :
    mdFold g c (bs ++ [b]) = g (mdFold g c bs, b) := by
  simp [mdFold]

/-- **Merkle–Damgård walk-back.**  If `g` is injective on a set `s` of cells containing the cells
of two iterations from `c₀`, and no cell of `s` has value `c₀`, then equal chain values come from
equal block lists. -/
theorem md_inj (g : CF St Blk) (c₀ : St) (s : List (St × Blk))
    (hinj : ∀ c ∈ s, ∀ c' ∈ s, g c = g c' → c = c') (hIV : ∀ c ∈ s, g c ≠ c₀) (bs : List Blk) :
    ∀ bs' : List Blk, (∀ c ∈ mdCells g c₀ bs, c ∈ s) → (∀ c ∈ mdCells g c₀ bs', c ∈ s) →
      mdFold g c₀ bs = mdFold g c₀ bs' → bs = bs' := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro bs' _ h' h
    rcases List.eq_nil_or_concat bs' with rfl | ⟨L, b, hL⟩
    · rfl
    · rw [List.concat_eq_append] at hL; subst hL
      rw [mdFold_append] at h
      exact absurd h.symm (hIV _ (h' _ (by simp [mdCells_append])))
  | append_singleton as a ih =>
    intro bs' h1 h' h
    rcases List.eq_nil_or_concat bs' with rfl | ⟨L, b, hL⟩
    · rw [mdFold_append] at h
      exact absurd h (hIV _ (h1 _ (by simp [mdCells_append])))
    · rw [List.concat_eq_append] at hL; subst hL
      rw [mdFold_append, mdFold_append] at h
      have hc := hinj _ (h1 _ (by simp [mdCells_append])) _ (h' _ (by simp [mdCells_append])) h
      obtain ⟨hm, hab⟩ := Prod.mk.inj hc
      rw [hab, ih L (fun c hcm => h1 c (by simp [mdCells_append, hcm]))
        (fun c hcm => h' c (by simp [mdCells_append, hcm])) hm]

/-- The cells read by the computation of `H_g(k, x)`. -/
def cellsH (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (g : CF St Blk)
    (kx : K × X) : List (St × Blk) :=
  mdCells g IV (ib kx) ++ mdCells g IV (ob kx (mdFold g IV (ib kx)))

/-! ## A win exhibits a covered digest or a bad table -/

/-- If the logged cells `s` contain the cells of the candidate and of the targets and `g` is not
bad on `s`, a win exhibits coverage among the digests of the logged cells. -/
theorem win_imp [DecidableEq St] (IV : St) (ib : K × X → List Blk)
    (ob : K × X → St → List Blk) (od : St → Y) (idx : Y → List Index)
    (hib : Function.Injective ib) (hob : ∀ kx kx' s s', ob kx s = ob kx' s' → s = s')
    (hobne : ∀ kx s, ob kx s ≠ []) (g : CF St Blk) (s : List (St × Blk))
    (cand : K × X) (targets : List (K × X))
    (hc : ∀ c ∈ cellsH IV ib ob g cand, c ∈ s)
    (ht : ∀ kx ∈ targets, ∀ c ∈ cellsH IV ib ob g kx, c ∈ s)
    (hfresh : cand ∉ targets)
    (hwin : ∀ i ∈ idx (hashG IV ib ob od g cand),
      i ∈ (targets.map (hashG IV ib ob od g)).flatMap idx) :
    CovP idx (s.map fun c => od (g c)) ∨ badV IV (s.map g) = true := by
  by_cases hb : badV IV (s.map g) = true
  · exact Or.inr hb
  refine Or.inl ?_
  simp only [badV, decide_eq_true_eq, not_or, not_not] at hb
  have hinj : ∀ c ∈ s, ∀ c' ∈ s, g c = g c' → c = c' := fun c hc c' hc' h =>
    List.inj_on_of_nodup_map hb.1 hc hc' h
  have hIV : ∀ c ∈ s, g c ≠ IV := fun c hc h => hb.2 (h ▸ List.mem_map_of_mem hc)
  -- final cells
  have hfin : ∀ kx : K × X, (∀ c ∈ cellsH IV ib ob g kx, c ∈ s) →
      ∃ as a, ob kx (mdFold g IV (ib kx)) = as ++ [a] ∧ (mdFold g IV as, a) ∈ s ∧
        (∀ c ∈ mdCells g IV as, c ∈ s) ∧ (∀ c ∈ mdCells g IV (ib kx), c ∈ s) ∧
        hashG IV ib ob od g kx = od (g (mdFold g IV as, a)) := by
    intro kx hkx
    rcases List.eq_nil_or_concat (ob kx (mdFold g IV (ib kx))) with h | ⟨as, a, h⟩
    · exact absurd h (hobne _ _)
    · rw [List.concat_eq_append] at h
      refine ⟨as, a, h, hkx _ ?_, fun c hcm => hkx _ ?_, fun c hcm => hkx _ ?_, ?_⟩
      · simp [cellsH, h, mdCells_append]
      · simp [cellsH, h, mdCells_append, hcm]
      · simp [cellsH, hcm]
      · simp only [hashG, h, mdFold_append]
  have hdist : ∀ kx kx' : K × X, ∀ as a as' a',
      ob kx (mdFold g IV (ib kx)) = as ++ [a] → ob kx' (mdFold g IV (ib kx')) = as' ++ [a'] →
      (∀ c ∈ mdCells g IV as, c ∈ s) → (∀ c ∈ mdCells g IV as', c ∈ s) →
      (∀ c ∈ mdCells g IV (ib kx), c ∈ s) → (∀ c ∈ mdCells g IV (ib kx'), c ∈ s) →
      (mdFold g IV as, a) = (mdFold g IV as', a') → kx = kx' := by
    intro kx kx' as a as' a' h h' hs hs' hi hi' he
    obtain ⟨hm, haa⟩ := Prod.mk.inj he
    have e1 : as = as' := md_inj g IV s hinj hIV as as' hs hs' hm
    have e2 : mdFold g IV (ib kx) = mdFold g IV (ib kx') :=
      hob _ _ _ _ (by rw [h, h', e1, haa])
    exact hib (md_inj g IV s hinj hIV _ _ hi hi' e2)
  obtain ⟨as, a, hoa, hF, hs, hi, hH⟩ := hfin cand hc
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hF
  refine ⟨pre.map (fun c => od (g c)), od (g (mdFold g IV as, a)), post.map (fun c => od (g c)),
    by rw [hsplit]; simp, fun i hi' => ?_⟩
  rw [← hH] at hi'
  obtain ⟨d, hd, hid⟩ := List.mem_flatMap.mp (hwin i hi')
  obtain ⟨kx, hkx, rfl⟩ := List.mem_map.mp hd
  obtain ⟨as', a', hoa', hF', hs', hi2, hH'⟩ := hfin kx (ht kx hkx)
  have hne : (mdFold g IV as', a') ≠ (mdFold g IV as, a) := fun e =>
    hfresh (by rw [← hdist kx cand as' a' as a hoa' hoa hs' hs hi2 hi e]; exact hkx)
  refine ⟨od (g (mdFold g IV as', a')), ?_, by rw [← hH']; exact hid⟩
  rw [hsplit] at hF'
  rcases List.mem_append.mp hF' with hm | hm
  · exact List.mem_append_left _ (List.mem_map_of_mem hm)
  · rcases List.mem_cons.mp hm with hm | hm
    · exact absurd hm hne
    · exact List.mem_append_right _ (List.mem_map_of_mem hm)

/-! ## The log of the final check -/

section Log

variable [DecidableEq St] [DecidableEq Blk]

/-- Run against the table `g`, logging the distinct cells read. -/
abbrev logImpl (g : CF St Blk) :
    QueryImpl (unifSpec + hS St Blk) (StateT (List (St × Blk)) ProbComp) :=
  stImpl (spec := hS St Blk) (fun t => g t) (logU id)

/-- Log a list of cells. -/
def logAll (l s : List (St × Blk)) : List (St × Blk) := l.foldl (fun s c => logU id c s) s

theorem subset_logAll (l s : List (St × Blk)) : ∀ c ∈ s, c ∈ logAll l s := by
  induction l generalizing s with
  | nil => exact fun c hc => hc
  | cons a l ih => exact fun c hc => ih _ c (subset_logU id a s c hc)

theorem mem_logAll (l s : List (St × Blk)) : ∀ c ∈ l, c ∈ logAll l s := by
  induction l generalizing s with
  | nil => exact fun c hc => absurd hc (by simp)
  | cons a l ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact subset_logAll l _ _ (mem_logU id c s)
    · exact ih _ c hc

theorem logAll_append (l l' s : List (St × Blk)) :
    logAll (l ++ l') s = logAll l' (logAll l s) := List.foldl_append ..

theorem run_mdM (g : CF St Blk) (c : St) (bs : List Blk) (s : List (St × Blk)) :
    (simulateQ (logImpl g) (mdM c bs)).run s = pure (mdFold g c bs, logAll (mdCells g c bs) s) := by
  induction bs generalizing c s with
  | nil => simp [mdM, mdFold, mdCells, logAll]
  | cons b bs ih =>
    have e : mdM c (b :: bs) =
        (liftM ((unifSpec + hS St Blk).query (.inr (c, b))) :
          OracleComp (unifSpec + hS St Blk) St) >>= fun c' : St => mdM c' bs := by
      simp only [mdM, List.foldlM_cons]
    rw [e, run_stImpl_inr_bind, ih]
    simp [mdFold, mdCells, logAll]

theorem run_hashM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (g : CF St Blk) (kx : K × X) (s : List (St × Blk)) :
    (simulateQ (logImpl g) (hashM IV ib ob od kx)).run s =
      pure (hashG IV ib ob od g kx, logAll (cellsH IV ib ob g kx) s) := by
  simp only [hashM, simulateQ_bind, StateT.run_bind, run_mdM, pure_bind, simulateQ_pure,
    StateT.run_pure, cellsH, logAll_append, hashG]

theorem run_hashAllM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (g : CF St Blk) (l : List (K × X)) (s : List (St × Blk)) :
    (simulateQ (logImpl g) (hashAllM IV ib ob od l)).run s =
      pure (l.map (hashG IV ib ob od g), logAll (l.flatMap (cellsH IV ib ob g)) s) := by
  induction l generalizing s with
  | nil => simp [hashAllM, logAll]
  | cons kx l ih =>
    simp only [hashAllM, simulateQ_bind, StateT.run_bind, run_hashM, pure_bind, ih,
      simulateQ_pure, StateT.run_pure, List.map_cons, List.flatMap_cons, logAll_append]

/-- **A winning run logs a covered digest or a bad table.** -/
theorem win_log [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index)
    (hib : Function.Injective ib) (hob : ∀ kx kx' s s', ob kx s = ob kx' s' → s = s')
    (hobne : ∀ kx s, ob kx s ≠ []) (g : CF St Blk) (A : ItsrAdvI St Blk K X) :
    ∀ z ∈ support ((simulateQ (logImpl g) (gameProg IV ib ob od idx A)).run []), z.1 = true →
      covB idx (z.2.map fun c => od (g c)) = true ∨ badV IV (z.2.map g) = true := by
  intro z hz hwin
  simp only [gameProg, simulateQ_bind, StateT.run_bind, run_hashAllM, run_hashM, pure_bind,
    simulateQ_pure, StateT.run_pure] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only [decide_eq_true_eq] at hwin
  have h := win_imp IV ib ob od idx hib hob hobne g
    (logAll (cellsH IV ib ob g w.1.1) (logAll (w.1.2.flatMap (cellsH IV ib ob g)) w.2))
    w.1.1 w.1.2
    (fun c hc => mem_logAll _ _ c hc)
    (fun kx hkx c hc => subset_logAll _ _ c
      (mem_logAll _ _ c (List.mem_flatMap.mpr ⟨kx, hkx, hc⟩)))
    hwin.1 hwin.2
  rcases h with h | h
  · exact Or.inl (by simpa [covB] using h)
  · exact Or.inr h

end Log

/-! ## The bound -/

theorem prT_pure_or_le (a b : Bool) :
    prT (pure (a || b)) ≤ prT (pure a) + prT (pure b) := by
  cases a <;> cases b <;> simp [prT_pure]

/-- **ITSR in the ideal-compression model, reduced to a tape of independent uniform digests.**
`Q` bounds the compression calls of the whole experiment `gameProg` (adversary and final check).
The experiment is won with probability at most the probability that a tape of `Q` independent
uniform digests has an entry whose indices are all covered by the other entries, plus
`Q² / |St|`. -/
theorem itsr_le [DecidableEq St] [DecidableEq Blk] [Fintype St] [Finite Blk]
    [SampleableType St] [SampleableType Y] [SampleableType (CF St Blk)]
    [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index)
    (hib : Function.Injective ib) (hob : ∀ kx kx' s s', ob kx s = ob kx' s' → s = s')
    (hobne : ∀ kx s, ob kx s ≠ [])
    (hod : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (od u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : ItsrAdvI St Blk K X) (Q : ℕ)
    (hQ : IsQueryBoundP (gameProg IV ib ob od idx A) (fun i => i.isRight = true) Q) :
    prT ($ᵗ (CF St Blk) >>= fun g => ITSRExperiment (A.inst (probI IV ib ob od idx g) g)) ≤
      prT (tapeList Y Q >>= fun r => pure (covB idx r)) +
        ((Q ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have h1 : prT ($ᵗ (CF St Blk) >>= fun g =>
        ITSRExperiment (A.inst (probI IV ib ob od idx g) g)) ≤
      prT ($ᵗ (CF St Blk) >>= fun g =>
        (simulateQ (logImpl g) (gameProg IV ib ob od idx A)).run [] >>= fun z =>
          pure (covB idx (z.2.map fun c => od (g c)) || badV IV (z.2.map g))) := by
    refine prT_bind_mono _ _ _ fun g _ => ?_
    rw [← simulateQ_gameProg, show instImpl₀ g = ansImpl (spec := hS St Blk) (fun t => g t) from rfl,
      ← fst_map_run_stImpl (fun t => g t) (logU id) _ ([] : List (St × Blk)),
      map_eq_bind_pure_comp]
    refine prT_bind_mono _ _ _ fun z hz => ?_
    simp only [Function.comp, prT_pure]
    have := win_log IV ib ob od idx hib hob hobne g A z hz
    cases hz1 : z.1
    · simp
    · rcases this hz1 with h | h <;> simp [h]
  refine h1.trans ?_
  refine (prT_bind_le_add _ _ _ _ fun g => prT_bind_le_add _ _ _ _ fun z =>
    prT_pure_or_le _ _).trans (add_le_add ?_ ?_)
  · exact prT_tape_le (spec := hS St Blk) id (fun g t => g t) (fun g g' t h => h) od hod
      (covB idx) (covB_mono idx) _ Q hQ
  · refine (prT_tape_le (spec := hS St Blk) id (fun g t => g t) (fun g g' t h => h) id
      (fun p => rfl) (badV IV) (badV_mono IV) _ Q hQ).trans ?_
    exact prT_tape_bad_le IV Q

end Ideal.Itsr

#print axioms Ideal.Itsr.md_inj
#print axioms Ideal.Itsr.win_imp
#print axioms Ideal.Itsr.win_log
#print axioms Ideal.Itsr.itsr_le
